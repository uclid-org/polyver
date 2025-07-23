import logging
import os
import subprocess
import tempfile

from ..dsl import TrueExpr
from ..dsl_parser import str2Expr
from ..procedure import Procedure
from ..synthesizer import Synthesizer
from ..utils import Lang
from ..utils import TypeConverter as tc
from ..utils import getSMTName, getSMTType
from .smt_parser import ASTTransformer, defineFunParser


# FIXME: Only supports bitvector operations for now
class SyGuSSynthesizer(Synthesizer):
    EXE = "cvc5"

    def __init__(
        self,
        timeout=60,
        delete=True,
        verbose=False,
        logger=None,
    ):
        super().__init__(timeout, delete, verbose)

        # Logging
        self.logger = logging.getLogger("ModelChecker.SyGuSSynthesizer")
        self.logger.setLevel(logging.DEBUG if verbose else logging.INFO)

    # Returns two lists, one containing a single precondition (TrueExpr)
    # and the other containing the postcondition
    def synthesize(self, name: str, proc: Procedure, failed_attempts=None):
        with (
            tempfile.NamedTemporaryFile(
                prefix="sygus_", suffix=".sl", mode="w+", delete=self.delete
            ) as sygusFile,
        ):
            # Generate SyGuS query
            query = self.generateSyGuSQuery(name, proc)
            sygusFile.write(query)
            sygusFile.flush()
            self.logger.info(f"Query written to {sygusFile.name}")

            # Close files so that they can be run safely
            sygusFile.close()

            # Run SyGuS solver
            smtlib = self.runSolver(sygusFile.name)

            if smtlib is None:
                post = None
            else:
                # Turn the smtlib string into an Expr object
                try:
                    parsed_tree = defineFunParser.parse(smtlib)
                    post = ASTTransformer().transform(parsed_tree)
                    post = str2Expr(post, proc.data)
                except Exception as e:
                    raise RuntimeError(f"Error parsing smtlib string: {str(e)}")

        return [TrueExpr()], [post]

    def generateSyGuSQuery(self, name: str, proc: Procedure):
        fun = "progSummary"
        io = list(proc.ucl2tgt_map.values())[0]
        inputs = [
            (getSMTName(d["tgtname"]), getSMTType(d["tgttype"]))
            for d in io["inputs"].values()
        ] + [
            (getSMTName(d["tgtname"]), getSMTType(d["tgttype"]))
            for d in io["outputs"].values()
        ]
        bool_names = [n for n, t in inputs if t == "Bool"]
        int_names = [n for n, t in inputs if t == "Int"]
        bv_names = [n for n, t in inputs if "BitVec" in t]
        tgt_types = [
            d["tgttype"]
            for d in list(io["inputs"].values()) + list(io["outputs"].values())
        ]
        pos_ex = [
            [val for assgn in io for _, val in assgn] for io in proc.positive_examples
        ]
        print("Positive Examples:\n", pos_ex)
        print("Target Types:\n", tgt_types)
        pos_ex = [
            [tc.tgt2smtlib(val, t) for val, t in zip(ex, tgt_types)] for ex in pos_ex
        ]
        print("Ended 1")
        pos_constraints = "\n".join(
            [f"(constraint ({fun} {' '.join(ex)}))" for ex in pos_ex]
        )
        neg_ex = [
            [val for assgn in io for _, val in assgn] for io in proc.negative_examples
        ]
        print("Negative Examples:\n", neg_ex)
        print("Target Types:\n", tgt_types)
        neg_ex = [
            [tc.tgt2smtlib(val, t) for val, t in zip(ex, tgt_types)] for ex in neg_ex
        ]
        neg_constraints = "\n".join(
            [f"(constraint (not ({fun} {' '.join(ex)})))" for ex in neg_ex]
        )
        query = f"""; SyGuS query for {name}
(set-logic ALL)
(synth-fun {fun} ( {' '.join([f"({n} {t})" for n, t in inputs])} ) Bool
    ; ( (B Bool) (I Int) (BV (_ BitVec 32)) )
    ( (B Bool) (BV (_ BitVec 32)) )

    (
        (B Bool (
            {' '.join(bool_names)}
            true false
            (and B B) (or B B) (not B)
            ; (=> B B)
            ; (< I I) (<= I I) (= I I)
            (bvslt BV BV) (bvsle BV BV) (= BV BV)
            ; (bvsgt BV BV) (bvsge BV BV) (bvult BV BV) (bvugt BV BV) (bvule BV BV) (bvuge BV BV)
        ))

        ; (I Int (
        ;     {' '.join(int_names)}
        ;     (Constant Int)
        ;     (+ I I) (- I I) (* I I)
        ;     (ite B I I)
        ; ))

        (BV (_ BitVec 32) (
            {' '.join(bv_names)}
            (Constant (_ BitVec 32))
            (bvadd BV BV) (bvsub BV BV) (bvneg BV) (bvmul BV BV)
            ; (bvurem BV BV)
            (ite B BV BV)
        ))
    )
)

; Below are positive examples
{pos_constraints}
; Below are negative examples
{neg_constraints}

(check-synth)
"""
        return query

    # Solve the SyGuS query and return the smtlib string
    def runSolver(self, query_path: str):
        cmd = f"{self.EXE} {query_path}"
        fail = False
        try:
            # Capture stdout and stderr
            proc = subprocess.Popen(
                cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
            self.logger.info(f"Running: {cmd}")
            stdout, stderr = proc.communicate(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            fail = True
            proc.kill()
            stdout, stderr = proc.communicate()
            self.logger.error(f"SyGuS solver timed out after {self.timeout} seconds")

        stdout = stdout.decode("utf-8")
        stderr = stderr.decode("utf-8")
        self.logger.debug(f"stdout: {stdout}")

        if not fail:
            return stdout
        else:
            self.logger.error(f"SyGuS solver failed:\n{stdout=}\n{stderr=}")
            return None


if __name__ == "__main__":
    import sys

    logging.basicConfig(level=logging.DEBUG)

    synth = SyGuSSynthesizer(
        verbose=True,
        delete=False,
    )

    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    with open(codepath, "r") as f:
        code = f.read()
    filename, file_extension = os.path.splitext(sys.argv[1])
    basename = os.path.basename(filename)
    proc = Procedure(
        basename,
        Lang.C,
        codepath,
        jsonpath,
    )

    pres, posts = synth.synthesize(basename, proc)
    print(pres)
    print(posts)
