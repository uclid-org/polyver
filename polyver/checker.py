import logging
import sys
import time
from datetime import datetime
from functools import partial
from pathlib import Path

from .dsl import TrueExpr
from .procedure import Procedure
from .synthesizers.human_synthesizer import HumanSynthesizer
from .synthesizers.llm_synthesizer import LLMSynthesizer
from .synthesizers.symo_synthesizer import SyMOSynthesizer
from .utils import Lang, Result
from .utils import TypeConverter as tc
from .utils import invoke_parallel, print_trace
from .verifiers.cbmc_verifier import CbmcVerifier
from .verifiers.kani_verifier import KaniVerifier


class ModelChecker:
    """
    Model Checker for Uclid modules with procedures

    Attributes
    ----------
    module : ModuleWithProcedures
        Uclid module with procedures to be verified
    synthesizer : ExtSynthesizer
        Synthesizer for pre/post-conditions
    delete : bool
        Delete temporary file after use (default = True)
    verbose : bool
        Log debug messages (default = False)
    procs : dict(str -> Procedure)
        Store procedure names and corresponding objects
        Reference of procs of self.module
    shepherd : bool
        Intermittently pause the program and wait for user signal to resume.

    Methods
    -------
    check() -> Result
        Entry point for verification
        Returns PASSED if passed else VIOLATED with a cex trace
    verifyPrePost(func_name: str, proc: Procedure) -> (Result, example)
        Invoke verifier with latest pre/post-conditions
        Returns result and cex if there is one
    synthesize(func_name: str, proc: Procedure) -> (str, str)
        Synthesize and returns pre/post-conditions
    checkSpurious(trace: dict) -> bool
        Check whether the given trace is spurious
        Adds positive/negative examples to Procedures
    """

    def __init__(
        self,
        module,
        synthesizer=HumanSynthesizer(),
        parallel_synth=False,
        cegis_iter_limit=5,
        cegar_iter_limit=3,
        verif_timeout=60,
        synth_timeout=60,
        delete=True,
        verbose=False,
        shepherd=False,
        log_base=None,
        init_solution=None,
        json_report=None,
    ):
        self.module = module
        self.module.delete = delete
        self.module.verbose = verbose
        self.synthesizer = synthesizer
        self.parallel = parallel_synth
        self.verif_timeout = verif_timeout
        self.synth_timeout = synth_timeout
        self.delete = delete
        self.verbose = verbose
        self.shepherd = shepherd
        self.log_base = log_base
        self.json_report = json_report
        self.procs = self.module.getProcedures()
        # Use the initial solution to set the pre/post conditions to save compute
        # Can be used to verify solution
        if init_solution is not None:
            self.module.loadPrePost(init_solution)

        self.cegis_iter_limit = cegis_iter_limit
        self.cegar_iter_limit = cegar_iter_limit
        self.max_cegis_iter = 0
        self.total_cegis_iter = 0
        self.cegar_iter = 0

        self.solve_time = 0
        self.synthesizer_time = 0
        self.verifier_time = 0
        self.ucl_time = 0
        self.spurcheck_time = 0

        self.result = None

        if self.log_base is None:
            self.log_base = Path(".").resolve() / "logs" / "model_checker"
        self.log_file = Path(
            datetime.now().strftime(f"{self.log_base}_%Y%m%d_%H%M%S.log")
        )
        # Create log directory if it doesn't exist
        self.log_file.parent.mkdir(parents=True, exist_ok=True)

        self.setupLogger()
        if self.verbose:
            self.logger.debug("Procedures:")
            for proc in self.procs.values():
                self.logger.debug(proc)

        # Create verifier instances for each procedures
        self.verifiers = {}
        for name, proc in self.procs.items():
            match proc.lang:
                case Lang.C:
                    verifier = CbmcVerifier
                case Lang.RUST:
                    verifier = KaniVerifier
                case _:
                    raise NotImplementedError(f"{proc.lang.name} not handled")
            self.verifiers[name] = verifier(
                proc=proc,
                timeout=verif_timeout,
                delete=delete,
                verbose=verbose,
            )

        # ModelChecker overwrites the synthesizer's timeout, delete, and verbose
        self.synthesizer.timeout = synth_timeout
        self.synthesizer.delete = delete
        self.synthesizer.verbose = verbose

    def setupLogger(self):
        self.logger = logging.getLogger("ModelChecker")
        self.logger.setLevel(logging.DEBUG if self.verbose else logging.INFO)

        # Disable propagation to avoid duplicate log messages
        self.logger.propagate = False

        # Check if the logger already has handlers to avoid adding them multiple times
        if not self.logger.hasHandlers():
            # Create handlers
            console_handler = logging.StreamHandler()
            console_handler.setLevel(logging.INFO)

            file_handler = logging.FileHandler(self.log_file)
            file_handler.setLevel(logging.DEBUG if self.verbose else logging.INFO)

            # Create formatters and add to handlers
            console_format = logging.Formatter("%(levelname)s - %(message)s")
            file_format = logging.Formatter(
                "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
            )

            console_handler.setFormatter(console_format)
            file_handler.setFormatter(file_format)

            # Add handlers to logger
            self.logger.addHandler(console_handler)
            self.logger.addHandler(file_handler)

        # Install exception handler
        sys.excepthook = partial(
            self.log_exception
        )  # partial() binds the self parameter to the method.

    def log_exception(self, exc_type, exc_value, exc_traceback):
        self.result = Result.ERROR
        self.report(self.json_report)
        if issubclass(exc_type, KeyboardInterrupt):
            # Call the default hook for KeyboardInterrupt to allow program to exit
            sys.__excepthook__(exc_type, exc_value, exc_traceback)
            return
        # Log the exception with traceback
        self.logger.error(
            "Uncaught exception", exc_info=(exc_type, exc_value, exc_traceback)
        )

    def pause(self, s):
        try:
            if self.shepherd:
                self.solve_time += time.time() - self.solve_start
                i = input(s)
                self.solve_start = time.time()
                return i
            else:
                return None
        except EOFError:
            self.shepherd = True

    def check(self):
        """
        Entry point of verification
        Returns PASSED if passed else VIOLATED with a cex trace
        """
        self.solve_start = time.time()
        while True:
            self.logger.info(f"[CEGAR] Iteration {self.cegar_iter}")
            if self.cegar_iter > self.cegar_iter_limit:
                self.logger.info(
                    f"[CEGIS] Reached maximum CEGAR iteration: {self.cegar_iter_limit}"
                )
                break

            self.cegar_iter += 1

            self.synthesizeValidPrePost(self.procs, parallel=self.parallel)

            # Abort if fail to retrieve results from synthesizer and verifier
            # if self.result is not None:
            #     assert self.result in [
            #         Result.SYNTH_FAILURE,
            #         Result.VERIF_TIMEOUT,
            #     ], self.result
            #     break

            # CEGAR LOOP
            # Valid pre/post found. Generate and verify entire uclid module.
            while True:
                precondition_violated = {}
                start = time.time()
                res, traces = self.module.verify()
                end = time.time()
                self.ucl_time += end - start
                if res == Result.PASSED:
                    self.result = res
                else:
                    # Check if each trace is spurious
                    # Report if true cex is found
                    for prop_name, trace in traces.items():

                        self.logger.info(
                            f"[CEGAR] Analyzing trace for property: {prop_name}"
                        )

                        # TODO: Implement a feedback mechanism to update the
                        # pre/post conditions based on the spurious counterexample.
                        # We need to be able to localize errors, i.e., figure out
                        # which pre/post conditions to fix.
                        is_spurious = self.checkSpurious(trace)

                        # Mark proc for resynthesis if precondition is violated
                        if "precondition" in prop_name:
                            # Remove everything before first "_" and after last "__"
                            proc_name = prop_name.split("_", 1)[1].rsplit("__", 1)[0]
                            proc = self.procs[proc_name]
                            precondition_violated[proc_name] = proc

                        if not is_spurious:
                            if "precondition" in prop_name:
                                # TODO: Feedback mechanism needed here too.
                                # First, try to loosen precondition to include the cex
                                # If it does not pass, try concrete execution
                                self.logger.info("Precondition violated")
                            elif "property" in prop_name:
                                self.logger.info(f"Found true cex for {prop_name}")
                                trace["property"] = prop_name
                                self.true_cex = trace
                                self.result = Result.VIOLATED
                                break

                        self.pause(
                            f"[CEGAR] Finish analyzing trace for property {prop_name}. Continue?"
                        )
                if len(precondition_violated) == 0:
                    break
                else:
                    for name, proc in precondition_violated.items():
                        proc.synthesize = True
                    self.synthesizeValidPrePost(
                        precondition_violated, parallel=self.parallel
                    )

            if self.result is not None:
                break  # Exit CEGAR loop

            self.pause(
                "[CEGAR] No true CEX found in CEGAR. Preparing to go back to CEGIS. Continue?"
            )
        self.solve_time += time.time() - self.solve_start
        return self.result

    def synthesizeValidPrePost(self, procs, parallel=False):
        """
        Synthesize pre/post-conditions for each procedure

        Parameters
        ----------
        parallel : bool
            Synthesize pre/post-conditions in parallel
        """
        if isinstance(self.synthesizer, HumanSynthesizer):
            parallel = False

        if parallel:
            shep = self.shepherd
            self.shepherd = False
            invoke_parallel(self.synthesizeWithFeedback, procs.items())
            self.shepherd = shep
        else:
            for name, proc in procs.items():
                self.synthesizeWithFeedback(name, proc)

    # FIXME: Should implement some class to handle feedback mechanism since
    # LLM and Human requires implementing a feedback loop but SyMO does not.
    def synthesizeWithFeedback(self, name: str, proc: Procedure):
        """
        CEGIS LOOP
        Synthesize pre/post-conditions for each procedure with feedback
        For each procedure check if pre/post is valid
        Resynthesize with returned example if not

        Parameters
        ----------
        func_name : str
            function name
        proc : Procedure
            corresponding Procedure object
        """
        # NOTE: This is a hack
        # Skip if the procedure already has valid pre/post
        # In checkSpurious(), proc.synthesize is set to False if the cex is not spurious for proc.
        if not proc.synthesize:
            self.logger.info(
                f"[CEGIS] Skipping {name} since it does not need to be synthesized."
            )
            return
        skip = self.pause(f"[CEGIS] Start synthesizing pre/post for {name}. Skip?[y/N]")
        if skip and skip.lower() == "y":
            return
        cegis_iter = 0

        # FIXME: Hacky
        if isinstance(self.synthesizer, SyMOSynthesizer):
            # Pres and posts should be valid. No need to verify.
            pres, posts = self.synthesizer.synthesize(name, proc)
            pre, post = pres[0], posts[0]
            self.logger.info(f"Found valid pre/post: {pre} -> {post}")
            if post is None:
                self.logger.info(
                    f"[CEGIS] Failed to synthesize pre/post for {name}. "
                    "Assigning weakest pre/post (True -> True)."
                )
                pre, post = TrueExpr(), TrueExpr()
            self.module.updateArtifact(name, pre, post)
            self.result = Result.SYNTH_FAILURE
            self.pause(f"[CEGIS] Finish synthesizing pre/post for {name}. Continue?")
            return

        failed_attempts = None
        while True:
            cegis_iter += 1
            self.max_cegis_iter = max(cegis_iter, self.max_cegis_iter)
            self.total_cegis_iter += 1
            self.logger.info(f"[CEGIS] Iteration {cegis_iter}")
            if cegis_iter > self.cegis_iter_limit:
                self.logger.info(
                    f"[CEGIS] Reached maximum CEGIS iteration: {self.cegis_iter_limit}\n"
                    f"[CEGIS] Assigning weakest pre/post (True -> True) for {name}.\n"
                )
                pre, post = TrueExpr(), TrueExpr()
                self.module.updateArtifact(name, pre, post)
                # self.result = Result.SYNTH_FAILURE
                break

            pres, posts = self.synthesize(name, proc, failed_attempts)
            res, pre, post, cexs = self.verifyPrePost(name, proc, pres, posts)
            match res:
                case Result.EXT_SUCCESS:
                    # Register the verified pre/post condition pair.
                    self.module.updateArtifact(name, pre, post)
                    break
                case Result.EXT_FAILURE:
                    # Include example
                    self.logger.info(
                        f"[CEGIS] Synthesizing pre/post failed for {name}."
                    )
                    for i in range(len(cexs)):
                        self.logger.info(f"[CEGIS] ===== Counterexample {i} =====")
                        self.logger.info(f"[CEGIS] Pre: {pres[i]}")
                        self.logger.info(f"[CEGIS] Post: {posts[i]}")
                        self.logger.info(f"[CEGIS] CEX: {list(cexs)[i]}")
                        self.logger.info("[CEGIS] ============================")
                    self.pause(
                        f"[CEGIS] Synthesizing pre/post failed for {name}. "
                        "Preparing to resynthesize. Continue?"
                    )

                    # FIXME: A more robust implementation should
                    # construct this dictionary in verifyPrePost().
                    failed_attempts = {"pre": pre, "post": post, "cex": cexs}
                case Result.VERIF_TIMEOUT:
                    self.result = Result.VERIF_TIMEOUT
                    # FIXME: Assigning weakest pre/post (True -> True) if timeout occurs.
                    # Maybe ask the synthesizer to generate another pre/post?
                    self.logger.info(
                        f"[CEGIS] Verification timeout\n"
                        f"[CEGIS] Assigning weakest pre/post (True -> True) for {name}.\n"
                    )
                    pre, post = TrueExpr(), TrueExpr()
                    self.module.updateArtifact(name, pre, post)
                    break
                case _:
                    raise RuntimeError("Unhandled case")
        proc.synthesize = False
        self.pause(f"[CEGIS] Finish synthesizing pre/post for {name}. Continue?")

    def synthesize(self, func_name: str, proc: Procedure, failed_attempts: dict = None):
        """
        Synthesize and returns pre/post-conditions

        Parameters
        ----------
        func_name : str
            function name
        proc : Procedure
            corresponding Procedure object
        failed_attempts : dict
            a dictionary capturing previous failed attempts in the previous
            _call_ to synthesize(). Note that this is not storing all failed
            results. The dictionary has three keys: pre, post, cex. "pre" and
            "post" map to a list of Expr each. "cex" maps to a list of
            counterexamples.

        Returns
        -------
        pre : str
            Synthesized pre-condition
        post : str
            Synthesized post-condition
        """

        start = time.time()
        pres, posts = self.synthesizer.synthesize(func_name, proc, failed_attempts)
        end = time.time()
        self.synthesizer_time += end - start
        proc.synthesis_time += end - start
        proc.synthesis_attempts += 1
        return pres, posts

    # For each procedure, build query and call verifier
    # Parse output from verifier and returns cex if not valid
    def verifyPrePost(self, func_name: str, proc: Procedure, pres: list, posts: list):
        """
        Invoke verifier with latest pre/post-conditions
        Returns result and cex if there is one

        Parameters
        ----------
        func_name : str
            function name
        proc : Procedure
            corresponding Procedure object
        pres : list[Expr]
            List of preconditions to verify
        posts : list[Expr]
            List of postconditions to verify

        Returns
        -------
        res : Result
            EXT_SUCCESS if passed, EXT_FAILURE if failed,
            or EXT_ERROR if error occurs
        pre
            If EXT_SUCCESS, pre is the weakest precondition.
            Otherwise, pre is a list of preconditions attempted.
        post
            If EXT_FAILURE, post is the strongest postcondition.
            Otherwise, post is a list of postconditions attempted.
        example
            Positive example if result is EXT_FAILURE
        """

        # TODO: Replace with a function that takes in two
        # pre/post pairs and returns the stronger one
        def sort_func(c):
            return len(str(c[0])) - len(str(c[1]))

        verifier = self.verifiers[func_name]
        prepost_pairs = []
        # Different than proc.positive_examples, which stores all CEXs seen,
        # current_CEXs only stores counterexamples found within this function call.
        # FIXME: This might be unnecessarily complex. There should be a unified
        # place to store preconditions, postconditions, and counterexamples.
        current_CEXs = []

        self.logger.info(f"Checking pre/post using {verifier.name}...")
        for pre, post in zip(pres, posts):
            if pre is None or post is None:
                continue
            start = time.time()
            res, example = verifier.verify(
                pre=pre.translate(proc.lang),
                post=post.translate(proc.lang),
            )
            end = time.time()
            self.verifier_time += end - start
            match res:
                case Result.EXT_SUCCESS:
                    self.logger.info(f"Found valid pre/post: {pre} -> {post}")
                    prepost_pairs.append((pre, post))
                case Result.EXT_FAILURE:
                    assert example is not None
                    proc.positive_examples.add(example)
                    current_CEXs.append(example)
                case Result.EXT_ERROR:
                    self.logger.error(
                        "Error verifying pre/post conditions. Check logs for details. "
                        "Please check if `cbmc` has been installed on your system."
                    )
                case Result.VERIF_TIMEOUT:
                    self.logger.info(
                        "Timeout occurred while verifying pre/post conditions "
                        f"for `{func_name}` after {verifier.timeout} seconds.\n"
                        f"Pre:  {pre.translate(proc.lang)}\n"
                        f"Post: {post.translate(proc.lang)}\n"
                    )
                    # return Result.VERIF_TIMEOUT, None, None, None

        if len(prepost_pairs) == 0:
            # Positive examples are valid counterexamples returned from CBMC.
            return Result.EXT_FAILURE, pres, posts, current_CEXs

        sorted_prepost_pairs = sorted(prepost_pairs, key=sort_func)
        strongest_prepost = sorted_prepost_pairs[0]

        # If only the strongest_prepost variable is printed, due to its tuple
        # nature, the outmost API function will use __repr__ instead of __str__,
        # making the printed formula less readable. Therefore we separate them here.
        self.logger.info(
            f"Perhaps strongest pre/post pair: ({strongest_prepost[0]}, {strongest_prepost[1]})"
        )
        self.logger.info(
            f"Perhaps strongest pre/post pair (API): "
            f"({strongest_prepost[0].translate(Lang.API)}, "
            f"{strongest_prepost[1].translate(Lang.API)})"
        )
        return Result.EXT_SUCCESS, strongest_prepost[0], strongest_prepost[1], None

    # Find all invocations (input/output args) for each procedure
    # Check if cex trace is spurious. Trace is
    # - spurious if any of the verifier checks does not hold
    # - a true cex if all of them hold
    def checkSpurious(self, trace_obj):
        """
        Check whether the given trace is spurious
        Adds positive/negative examples to Procedures

        Parameters
        ----------
        trace_obj : dict
            Counterexample trace generated by Uclid

        Returns
        -------
        spurious : bool
            True if cex trace is spurious else False
        """

        if self.verbose:
            print_trace(trace_obj, self.logger)
        self.pause("[Spurious] Analyzing trace. Continue?")

        trace = trace_obj["trace"]
        spurious = False

        def getVar(var: str):
            v = var.rstrip("'")
            return v, len(var) - len(v)

        # Check if each invocation
        for name, proc in self.procs.items():
            self.logger.info(f"Checking spuriousness for: {name}")
            ver = self.verifiers[name]

            for flag, call in proc.ucl2tgt_map.items():
                inputs, outputs = call["inputs"], call["outputs"]

                for i, step in enumerate(trace):

                    # Check if UCLID5 returns a parse error. If so, ask user to skip.
                    # FIXME: This might be dangerous if the skipped step is the
                    # spurious step.
                    if (
                        isinstance(step, str)
                        and step == "error: unable to parse counterexample frame"
                    ):
                        self.pause(
                            "[CEGAR] Unable to parse counterexample frame. Continue?"
                        )
                        continue

                    # Only check if the input/output pair and the actual behavior match
                    # if the function is fired (flag == "true"). Otherwise skip.
                    if step[flag][0] != "true":
                        continue

                    # Collect input assignments
                    input_assgn = []
                    for uclname, info in inputs.items():
                        # Converting a CEX variable field to a Python integer
                        val = tc.ucl2tgt(
                            step[uclname][0], fr=info["ucltype"], to=info["tgttype"]
                        )
                        self.logger.debug(
                            f"uclname: {uclname}, step[uclname][0]: {step[uclname][0]}, val: {val}"
                        )
                        if val is not None:
                            input_assgn.append((info["tgtname"], val))
                    # input_assgn is a tuple of tuples. Each inner tuple is a
                    # variable assignment for a specific procedure call.
                    input_assgn = tuple(input_assgn)

                    # Collect output assignments
                    output_assgn = []
                    for uclname, info in outputs.items():
                        val = tc.ucl2tgt(
                            step[uclname][0], fr=info["ucltype"], to=info["tgttype"]
                        )
                        if val is not None:
                            output_assgn.append((info["tgtname"], val))
                    output_assgn = tuple(output_assgn)

                    iopair = (input_assgn, output_assgn)

                    self.logger.info("input assignment:")
                    for var, val in input_assgn:
                        self.logger.info(f"\t{var} = {val}")
                    self.logger.info("output assignment:")
                    for var, val in output_assgn:
                        self.logger.info(f"\t{var} = {val}")

                    # Can skip calling cbmc if the IO pair matches any examples
                    # that we have seen from the CEGIS step. This is an optimization.
                    if iopair in proc.positive_examples:
                        self.logger.info(f"{name} at step {i} is NOT spurious.")
                        continue
                    if iopair in proc.negative_examples:
                        self.logger.info(f"{name} at step {i} is spurious.")
                        spurious = True
                        proc.synthesize = True
                        continue

                    start = time.time()
                    res, pos_example = ver.checkIOValues(
                        input_assgn,
                        output_assgn,
                    )
                    end = time.time()
                    self.spurcheck_time += end - start
                    self.logger.debug(f"Spuriosity check result: {iopair} --> {res}")
                    match res:
                        case Result.EXT_SUCCESS:
                            proc.positive_examples.add(iopair)
                            proc.synthesize = False
                            self.logger.info(f"{name} at step {i} is NOT spurious.")
                            pass
                        case Result.EXT_FAILURE:
                            spurious = True
                            proc.synthesize = True
                            self.logger.info(f"{name} at step {i} is spurious.")
                            proc.negative_examples.add(iopair)
                            proc.positive_examples.add(pos_example)
                        case Result.EXT_ERROR:
                            raise RuntimeError("Error in spuriosity check")
                        case _:
                            raise RuntimeError("Unhandled case")
        return spurious

    def report(self, json_filename=None):
        """
        Report the verification results
        """
        if self.result is None:
            self.logger.info("No result to report. Please call check() first.")

        witness = {}

        self.logger.info("")
        self.logger.info("")
        self.logger.info("========== Verification Report ==========")
        self.logger.info(f"Benchmark: {self.module.name}")
        self.logger.info(f"Result: {self.result.name}")

        match self.result:
            case Result.PASSED:
                pass
            case Result.VIOLATED:
                print_trace(self.true_cex, self.logger)
                witness["cex"] = self.true_cex
            case Result.VERIF_TIMEOUT:
                self.logger.info(
                    f"Ext verifier timeout after {self.verif_timeout} seconds."
                )
            case Result.SYNTH_FAILURE:
                self.logger.info("Failed to synthesize pre/postconditions.")
            case Result.ERROR:
                self.logger.error("An error occurred during verification.")
            case _:
                self.logger.info(f"Please see {self.log_file} for details.")

        for name, proc in self.procs.items():
            self.logger.info(f"Pre/post conditions for {name}:")
            self.logger.info(f"  Pre:  {proc.requires[-1]}")
            self.logger.info(f"  Post: {proc.ensures[-1]}")
            witness[name] = {
                "dsl_pre": proc.requires[-1].translate(Lang.API),
                "dsl_post": proc.ensures[-1].translate(Lang.API),
                "tgt_pre": proc.requires[-1].translate(proc.lang),
                "tgt_post": proc.ensures[-1].translate(proc.lang),
                "ucl_pre": proc.requires[-1].translate(Lang.UCLID5),
                "ucl_post": proc.ensures[-1].translate(Lang.UCLID5),
                "filepath": str(proc.filepath),
                "jsonpath": str(proc.jsonpath),
                "synthesis_time": proc.synthesis_time,
                "synthesis_attempts": proc.synthesis_attempts,
            }

        self.logger.info(f"Wall clock time:     {self.solve_time:>6.2f} seconds")
        self.logger.info(f"Synthesizer time:    {self.synthesizer_time:>6.2f} seconds")
        self.logger.info(f"Ext. Verifier time:  {self.verifier_time:>6.2f} seconds")
        self.logger.info(f"Ucl. Verifier time:  {self.ucl_time:>6.2f} seconds")
        self.logger.info(f"Spurious check time: {self.spurcheck_time:>6.2f} seconds")
        self.logger.info("=========================================")

        result_dict = {
            "benchmark": self.module.name,
            "result": self.result.name,
            "args": {
                "cegis_iter_limit": self.cegis_iter_limit,
                "cegar_iter_limit": self.cegar_iter_limit,
                "verif_timeout": self.verif_timeout,
                "synth_timeout": self.synth_timeout,
                "delete": self.delete,
                "verbose": self.verbose,
                "shepherd": self.shepherd,
                "log_file": str(self.log_file),
                "json_report": self.json_report,
            },
            "witness": witness,
            "max_cegis_iter": self.max_cegis_iter,
            "total_cegis_iter": self.total_cegis_iter,
            "cegar_iter": self.cegar_iter,
            "wall_clock_time": self.solve_time,
            "synthesizer_time": self.synthesizer_time,
            "non_parallel_synth": (
                self.synthesizer_time + self.verifier_time + self.ucl_time
                if self.parallel
                else self.solve_time
            ),
            "verifier_time": self.verifier_time,
            "ucl_time": self.ucl_time,
            "spurcheck_time": self.spurcheck_time,
        }
        if json_filename is not None:
            import json

            with open(json_filename, "w") as f:
                json.dump(result_dict, f, indent=2)


if __name__ == "__main__":
    from led import BlinkLEDModule

    module = BlinkLEDModule()
    # synthesizer = LLMSynthesizer(model='gpt-3.5-turbo', method="chain-of-thought", verbose=True)
    synthesizer = LLMSynthesizer(
        model="gpt-4o-2024-08-06",
        method="chain-of-thought",
        # method="zero-shot",
        num_calls=5,
        max_attempts=3,
        error_feedback=True,
        verbose=True,
        # FIXME: The getLogger('ModelCheckerLogger') is officially created in
        # ModelChecker below. Not sure if calling it here is the best practice.
        logger=logging.getLogger("ModelCheckerLogger"),
    )
    # synthesizer = HumanSynthesizer()
    mc = ModelChecker(
        module,
        synthesizer=synthesizer,
        delete=False,
        verbose=True,
        shepherd=True,
    )
    res = mc.check()
    mc.report()
