import json
import logging

# import re
import subprocess
import tempfile

from ..procedure import Procedure
from ..utils import Result
from ..verifier import Verifier


class CbmcVerifier(Verifier):
    """
    Wrapper class for cbmc

    Attributes
    ----------
    verifier_exe : str
        Name of the cbmc executable
    verifier_opt : list[str]
        List of options to be passed to cbmc

    Methods
    -------
    verify(pre: str, post: str) -> (Result, Union[None, tuple])
        Verifies the pre/post-conditions by building a query and running cbmc.
        Returns the result and a counterexample if there is one.
    buildQuery(pre: str, post: str) -> str
        Builds cbmc query with pre/post-conditions.
    run(query: str) -> list
        Runs cbmc with the query and returns the output as a list.
    parse(output: list) -> (Result, Union[None, tuple]
        Parses output from cbmc and returns result and cex if there is one.
    checkIOValues(input_vals: dict, output_vals: dict) -> (Result, Union[None, tuple])
        Checks if the input/output values are valid by building a query with negated post-condition
        and running cbmc on it.
    parseNameFromTrace(name: str, key: str, tgttype: str, trace: list,
                       vals: dict, is_dynamic_object=False) -> None
        Parses the trace to find the value of `key` and store it in `vals` with the name `name`.
    """

    verifier_exe = "cbmc"

    def __init__(
        self,
        proc: Procedure,
        use_smt=True,
        timeout=None,
        delete=True,
        verbose=False,
    ):
        super().__init__(self.verifier_exe, proc, timeout, delete, verbose)

        self.verifier_opt = ["--no-pointer-check", "--property main.assertion.1"]
        if use_smt:
            self.verifier_opt.append("--smt2")
        # Add more cbmc flags here
        self.verifier_opt.extend(["--unwind 11", "--unwinding-assertions"])

        self.logger = logging.getLogger("ModelChecker.CbmcVerifier")

    def verify(self, pre: str, post: str):
        query = self.buildQuery(pre, post)
        if self.verbose:
            self.logger.debug(f"cbmc query:\n{query}")
        output = self.run(query)
        if self.verbose:
            self.logger.debug(f"{self.verifier_exe} output:\n{output}")
        return self.parse(output)

    def buildQuery(self, pre, post):
        """
        Builds cbmc with pre/post-conditions and returns query string

        Parameters
        ----------
        pre : str
            Pre-condition to be placed in `__CPROVER_assume`
        post : str
            Post-condition to be placed in `assert`

        Returns
        -------
        query : str
            Query string cbmc accepts
        """

        query = f"#define PRECONDITION {pre}\n#define POSTCONDITION {post}\n\n{self.proc.code}"
        return query

    # Run command on generated query
    def run(self, query: str):
        with tempfile.NamedTemporaryFile(
            prefix="out_", suffix=".c", mode="w+", delete=self.delete
        ) as f:
            f.write(query)
            # Change file object's position to enable reading
            f.seek(0)
            self.logger.info(f"cbmc file written to {f.name}")

            # Run cbmc with the query file
            cmd = f"{self.verifier_exe} {' '.join(self.verifier_opt)} {f.name} --trace --json-ui"
            self.logger.info(f"Running command: {cmd}")
            p = subprocess.Popen(
                cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
            try:
                byte_stdout, byte_stderr = p.communicate(timeout=self.timeout)
                output = json.loads(byte_stdout.decode("utf-8"))
            except subprocess.TimeoutExpired:
                # kill the process if timeout
                p.kill()
                byte_stdout, byte_stderr = p.communicate()
                output = None

        # with open("cbmc_output.json", "w") as f:
        #     json.dump(output, f, indent=4)
        return output

    def parse(self, output: list):
        """Parses output from cbmc and returns result and cex if there is one"""
        status, trace = self.parse_status_and_result(output)
        if status == Result.EXT_ERROR:
            return Result.EXT_ERROR, output
        elif status in [Result.VERIF_TIMEOUT, Result.EXT_SUCCESS]:
            return status, None
        elif status == Result.EXT_FAILURE:
            input_vals = {}
            output_vals = {}

            # with open("trace.json", "w") as f:
            #     json.dump(trace, f, indent=4)
            filtered_trace = list(
                filter(
                    lambda x: not x["hidden"]
                    and "sourceLocation" in x.keys()
                    and "builtin" not in x["sourceLocation"]["file"],
                    trace,
                )
            )
            # with open("filtered_trace.json", "w") as f:
            #     json.dump(filtered_trace, f, indent=4)
            trace_before_func_call = None
            for i, step in enumerate(filtered_trace):
                if "function" in step.keys() and "stepType" in step.keys():
                    if (
                        step["function"]["displayName"] == self.proc.name
                        and step["stepType"] == "function-call"
                    ):
                        trace_before_func_call = filtered_trace[:i]
                        break
            assert trace_before_func_call is not None
            # Traces are reversed because we want to find the last occurrence of a variable
            for inp in self.proc.data["inputs"]:
                self.parseNameFromTrace(
                    inp["tgtname"],
                    inp["tgtname"],
                    inp["tgttype"],
                    list(reversed(trace_before_func_call)),
                    input_vals,
                )
            for out in self.proc.data["outputs"]:
                self.parseNameFromTrace(
                    out["tgtname"],
                    out["tgtname"],
                    out["tgttype"],
                    list(reversed(filtered_trace)),
                    output_vals,
                )

            if self.verbose:
                self.logger.info(f"positive example: {input_vals} / {output_vals}")

            return Result.EXT_FAILURE, (
                tuple(list(input_vals.items())),
                tuple(list(output_vals.items())),
            )
        else:
            raise NotImplementedError(f"{status} not handled")

    # Parse the result with the property name "main.assertion.1"
    # `output` is None if the verifier timed out.
    # Otherwise it's what is returned by cbmc using --json-ui.
    def parse_status_and_result(self, output: list):
        if output is None:
            return Result.VERIF_TIMEOUT, None
        if "cProverStatus" not in output[-1]:
            return Result.EXT_ERROR, None
        result = list(
            filter(lambda x: x["property"] == "main.assertion.1", output[-3]["result"])
        )
        assert len(result) == 1
        result = result[0]
        assert result["status"] in ["SUCCESS", "FAILURE"]
        if result["status"] == "SUCCESS":
            return Result.EXT_SUCCESS, None
        else:
            return Result.EXT_FAILURE, result["trace"]

    # NOTE: Works with cbmc-6.3.1
    # NOTE: Parses struct types. Tested with single level structs.
    # Parse the trace to find the value of `key` and store it in `vals` with the name `name`.
    def parseNameFromTrace(
        self, name, key, tgttype, trace, vals, is_dynamic_object=False
    ):
        def checkLHS(s, k):
            return "lhs" in s.keys() and s["lhs"] == k

        is_pointer = tgttype[-1] == "*"
        type_name = tgttype[:-1].strip() if is_pointer else tgttype

        if is_pointer:
            for step in trace:
                if checkLHS(step, key):
                    data = step["value"]["data"]
                    if "NULL" in data:
                        vals[name] = "NULL"
                    else:
                        # `data` should be a 'dynamic_object' if it's a pointer
                        # Search for the dynamic object in the trace
                        self.parseNameFromTrace(
                            name, data, type_name, trace, vals, True
                        )
                    break
        elif type_name in self.proc.data["types"].keys():
            for field_name, field_type in self.proc.data["types"][type_name][
                "fields"
            ].items():
                self.parseNameFromTrace(
                    name + ("->" if is_dynamic_object else ".") + field_name,
                    key + "." + field_name,
                    field_type["tgttype"],
                    trace,
                    vals,
                    False,
                )
        else:
            for step in trace:
                if checkLHS(step, key):
                    vals[name] = step["value"]["data"]
                    break

    def checkIOValues(self, input_vals, output_vals):
        pre = (
            " && ".join(f"{arg} == {val}" for arg, val in input_vals)
            if len(input_vals) > 0
            else "1"
        )
        post = (
            " && ".join(f"{arg} == {val}" for arg, val in output_vals)
            if len(output_vals) > 0
            else "1"
        )
        # we build a query with the negation of the post-condition
        # to handle non-deterministic functions. That is, if the
        # post-condition is false, then the IO pair is possible
        neg_post = "!(" + post + ")"
        query = self.buildQuery(pre, neg_post)
        if self.verbose:
            logging.debug(f"cbmc query:\n{query}")
        output = self.run(query)
        status, _ = self.parse_status_and_result(output)

        # if cbmc returns failure, then the IO pair is possible
        # if cbmc returns success, then the IO pair is not possible
        # in this case, we return the IO pair as a positive example
        # by asserting the IO pair
        if status == Result.EXT_FAILURE:
            return Result.EXT_SUCCESS, None
        elif status == Result.EXT_SUCCESS:
            return self.verify(pre, post)
        elif status == Result.EXT_ERROR:
            return Result.EXT_ERROR, output
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
        Lang.C,
        codepath,
        jsonpath,
    )

    logging.basicConfig(level=logging.INFO)
    pre = "true"
    post = "false"

    cv = CbmcVerifier(proc, delete=False, verbose=True)
    res, example = cv.verify(
        pre=pre,
        post=post,
    )
    print(res)
    print(example)
