from .procedure import Procedure


class Verifier:
    """
    Parent class for all verifiers

    Attributes
    ----------
    name : str
        Name of the verifier, e.g., cbmc
    proc : Procedure
        Instance representing procedure
    timeout : int or None
        Timeout for verification in seconds (default = None, no timeout)
    delete : bool
        Delete temporary file after use (default = True)
    verbose : bool
        Log debug messages (default = False)

    Methods
    -------
    verify(pre: str, post: str) -> Tuple[Result, Union[None, tuple[tuple, tuple]]
        Verifies with given pre/post-conditions and returns result and cex if there is one
    checkIOValues(input_vals, output_vals)
        Checks whether given inputs and outputs are possible. Returns result and cex if there is one
    """

    def __init__(
        self,
        name: str,
        proc: Procedure,
        timeout=None,
        delete=True,
        verbose=False,
    ):
        self.name = name
        self.proc = proc
        self.timeout = timeout
        self.delete = delete
        self.verbose = verbose

    def verify(self, pre: str, post: str):
        """
        Verifies with given pre/post-conditions

        Parameters
        ----------
        pre : str
            pre-condition to be tested
        post : str
            post-condition to be tested

        Returns
        -------
        res : Result
            Verification result
        cex
            Counterexample that violates given pre/post-conditions
        """
        raise NotImplementedError

    def checkIOValues(self, input_vals, output_vals):
        """
        Checks whether given inputs and outputs are possible
        Calls `verify` with appropriate pre/post-conditions derived from input/output values.

        Parameters
        ----------
        input_vals
            input values to procedure
        output_vals
            output values of procedure

        Returns
        -------
        res : Result
            Verification result
        cex
            Counterexample that violates given input/output values
        """
        raise NotImplementedError
