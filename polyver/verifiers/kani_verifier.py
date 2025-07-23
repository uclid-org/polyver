import json
import logging
import subprocess
import tempfile
from pathlib import Path

from ..procedure import Procedure
from ..utils import Result
from ..verifier import Verifier


# KaniVerifier uses kani to verify Rust code
# kani is a Rust verification tool that uses CBMC as a backend
# To verify, a pair of pre and post conditions are passed to the verify method
# which are then used to build a query that is passed to kani.
class KaniVerifier(Verifier):
    """
    Wrapper class for Kani, a Rust verification tool.

    Attributes
    ----------
    verifier_exe : str
        The executable name for the Kani verifier.
    verifier_opt : list[str]
        List of options to pass to the Kani verifier.
    cbmc_args : list[str]
        List of additional arguments for CBMC.

    Methods
    -------
    verify(pre: str, post: str) -> tuple[Result, Union[None, tuple]]:
        Verifies the pre/post-conditions by building a query and running kani.
        Returns the result and a counterexample if there is one.
    buildQuery(pre: str, post: str) -> str
        Builds kani query with pre/post-conditions.
    run(query: str) -> JSONObject
        Runs kani with the query and returns the output as a JSON-like object.
    parse(output: list) -> (Result, Union[None, tuple]
        Parses output from kani and returns result and cex if there is one.
    checkIOValues(input_vals: dict, output_vals: dict) -> (Result, Union[None, tuple])
        Checks if the input/output values are valid by building a query with negated post-condition
        and running kani on it.
    findFirstFromTrace(trace: list, name: str) -> Union[str, None]
        Finds the first occurrence of a variable in the trace.
    """

    verifier_exe = "kani"
    relative_trace_path = "./report-main/json/viewer-trace.json"

    def __init__(
        self, proc: Procedure, use_smt=True, timeout=None, delete=True, verbose=False
    ):
        super().__init__(self.verifier_exe, proc, timeout, delete, verbose)

        self.verifier_opt = [
            "--enable-unstable",
            "--visualize",
        ]
        self.cbmc_args = [
            "--cbmc-args",
            "--property main.assertion.1",
        ]
        if use_smt:
            self.cbmc_args.append("--smt2")
        self.logger = logging.getLogger("ModelChecker.KaniVerifier")

    def verify(self, pre: str, post: str):
        query = self.buildQuery(pre, post)
        if self.verbose:
            self.logger.debug(f"kani query:\n{query}")
        output = self.run(query)
        return self.parse(output)

    def buildQuery(self, pre, post):
        # Inputs and outputs are passed by reference
        inputs = [
            f"{inp['tgtname']}: &{inp['tgttype']}" for inp in self.proc.data["inputs"]
        ]
        outputs = [
            f"{out['tgtname']}: &{out['tgttype']}" for out in self.proc.data["outputs"]
        ]
        query = f"""{self.proc.code}
fn precondition({", ".join(inputs)}) -> bool {{
    {pre}
}}

fn postcondition({", ".join(inputs + outputs)}) -> bool {{
    {post}
}}"""
        return query

    def run(self, query: str):
        # Create a unique temporary directory for kani query and report
        with tempfile.TemporaryDirectory(prefix="kani_", delete=self.delete) as tmpdir:
            self.logger.info(f"kani target dir: {tmpdir}")
            with tempfile.NamedTemporaryFile(
                prefix="kani_", suffix=".rs", dir=tmpdir, mode="w+", delete=self.delete
            ) as f:
                f.write(query)
                f.seek(0)
                self.logger.info(f"kani file written to {f.name}")

                # Run kani with the query file and the target directory
                cmd = (
                    f"{self.verifier_exe} {f.name} "
                    f"--target-dir {tmpdir} {' '.join(self.verifier_opt + self.cbmc_args)}"
                )
                self.logger.info(f"Running command: {cmd}")
                p = subprocess.Popen(
                    cmd.split(),
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
                try:
                    stdout, stderr = p.communicate(timeout=self.timeout)
                    output = None
                    # Read result from the trace file in the target directory
                    trace_path = Path(tmpdir) / self.relative_trace_path
                    if Path(trace_path).exists():
                        with open(trace_path, "r") as f:
                            try:
                                output = json.load(f)
                            except json.JSONDecodeError:
                                self.logger.error(
                                    f"Error loading trace file {trace_path}"
                                )
                    else:
                        self.logger.error(
                            f"Report directory not found for {self.proc.name} in {trace_path}. "
                            "An error may have occurred."
                        )
                        output = stdout
                except subprocess.TimeoutExpired:
                    p.kill()
                    stdout, stderr = p.communicate()
        return output

    # Parse the result with the property name "main.assertion.1"
    # `output` is
    # 1. a json-like object, or
    # 2. a string containing the output of the verifier if the json file is not found, or
    # 3. None if the verifier timed out
    def parse_status_and_result(self, output):
        if output is None:
            return Result.VERIF_TIMEOUT, None
        if isinstance(output, str):
            return Result.EXT_ERROR, None
        assert isinstance(output, dict), f"Unexpected output type {type(output)}"
        traces_dict = output["viewer-trace"]["traces"]
        if len(traces_dict) == 0:
            return Result.EXT_SUCCESS, None
        # trace is a list of dictionaries
        trace = traces_dict["main.assertion.1"]
        return Result.EXT_FAILURE, trace

    def parse(self, output):
        status, trace = self.parse_status_and_result(output)
        if status == Result.EXT_ERROR:
            return Result.EXT_ERROR, output
        elif status in [Result.VERIF_TIMEOUT, Result.EXT_SUCCESS]:
            return status, None
        elif status == Result.EXT_FAILURE:
            input_vals = {}
            output_vals = {}

            trace_before_func_call = None
            for i, step in enumerate(trace):
                if step["kind"] == "function-call":
                    assert "detail" in step, "Detail field not found"
                    assert "name" in step["detail"], "Function call name not found"
                    if self.proc.name in step["detail"]["name"]:
                        trace_before_func_call = trace[:i]
                        break
            assert (
                trace_before_func_call is not None
            ), f"Function call {self.proc.name} not found in trace"

            input_strings = [
                d["tgtname"]
                for d in list(self.proc.ucl2tgt_map.values())[0]["inputs"].values()
            ]
            output_strings = [
                d["tgtname"]
                for d in list(self.proc.ucl2tgt_map.values())[0]["outputs"].values()
            ]

            # Traces are reversed because we want to find the last occurrence of a variable
            for inp in input_strings:
                input_vals[inp] = self.findFirstFromTrace(
                    list(reversed(trace_before_func_call)), inp
                )
            for out in output_strings:
                output_vals[out] = self.findFirstFromTrace(list(reversed(trace)), out)
            return Result.EXT_FAILURE, (
                tuple(list(input_vals.items())),
                tuple(list(output_vals.items())),
            )
        else:
            raise NotImplementedError(f"{status} not handled")

    def findFirstFromTrace(self, trace, name):
        for step in trace:
            if step["kind"] == "variable-assignment":
                assert "detail" in step, "Detail field not found"
                assert "lhs" in step["detail"], "LHS field not found"
                assert "rhs-value" in step["detail"], "RHS field not found"
                if step["detail"]["lhs"] == name:
                    return step["detail"]["rhs-value"]

    def checkIOValues(self, input_vals, output_vals):
        pre = (
            " && ".join(f"{arg} == {val}" for arg, val in input_vals)
            if len(input_vals) > 0
            else "true"
        )
        post = (
            " && ".join(f"{arg} == {val}" for arg, val in output_vals)
            if len(output_vals) > 0
            else "true"
        )
        # we build a query with the negation of the post-condition
        # to handle non-deterministic functions. That is, if the
        # post-condition is false, then the IO pair is possible
        neg_post = "!(" + post + ")"
        query = self.buildQuery(pre, neg_post)
        if self.verbose:
            self.logger.debug(f"kani query:\n{query}")
        output = self.run(query)
        status, _ = self.parse_status_and_result(output)

        # if kani returns failure, then the IO pair is possible
        # if kani returns success, then the IO pair is not possible
        # in this case, we return the IO pair as a positive example
        # by asserting the IO pair
        if status == Result.EXT_FAILURE:
            return Result.EXT_SUCCESS, None
        elif status == Result.EXT_SUCCESS:
            return self.verify(pre, post)
        elif status == Result.EXT_ERROR:
            return Result.EXT_ERROR, None
        else:
            raise NotImplementedError(f"{status} not handled")


if __name__ == "__main__":
    import os
    import sys

    from ..utils import Lang

    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    name = os.path.basename(codepath).split(".")[0]
    proc = Procedure(
        name,
        Lang.RUST,
        codepath,
        jsonpath,
    )

    logging.basicConfig(level=logging.INFO)
    pre = "true"
    post = "false"

    rv = KaniVerifier(proc, delete=False, verbose=True)
    res, example = rv.verify(
        pre=pre,
        post=post,
    )
    print(res)
    print(example)
