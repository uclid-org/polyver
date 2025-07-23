from .procedure import Procedure


class Synthesizer:
    """
    Parent class for all synthesizers

    Attributes
    ----------
    timeout : int
        Timeout for synthesis in seconds
    delete : bool
        If True, deletes log/output files after synthesis
    verbose : bool
        If True, prints debug information

    Methods
    -------
    synthesize(name, proc):
        Synthesizes and returns new artifacs
    """

    def __init__(self, timeout=None, delete=True, verbose=False):
        self.timeout = timeout
        self.delete = delete
        self.verbose = verbose

    def synthesize(self, name: str, proc: Procedure):
        """
        Synthesizes and returns new artifact

        Parameters
        ----------
        name : str
            function name
        proc : Procedure
            Procedure object containing code and artifact history

        Returns
        -------
        pre : str
            Synthesized pre-condition
        post : str
            Synthesized post-condition
        """
        raise NotImplementedError
