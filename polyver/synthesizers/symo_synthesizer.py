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
class SyMOSynthesizer(Synthesizer):
    EXE = "delphi"

    def __init__(
        self,
        timeout=60,
        delete=True,
        verbose=False,
        logger=None,
    ):
        super().__init__(timeout, delete, verbose)

        # Logging
        self.logger = logging.getLogger("ModelChcker.SyMOSynthesizer")
        self.logger.setLevel(logging.DEBUG if verbose else logging.INFO)

    # Returns two lists, one containing a single precondition (TrueExpr)
    # and the other containing the postcondition
    def synthesize(self, name: str, proc: Procedure):
        with (
            tempfile.NamedTemporaryFile(
                prefix="oracle_", suffix=".sh", mode="w+", delete=self.delete
            ) as oracleFile,
            tempfile.NamedTemporaryFile(
                prefix="symo_", suffix=".sl", mode="w+", delete=self.delete
            ) as symoFile,
            tempfile.NamedTemporaryFile(
                prefix="cbmc_", suffix=".c", mode="w+", delete=self.delete
            ) as cbmcFile,
        ):
            # Generate oracle shell script
            oracle = self.generateOracle(name, proc, cbmcFile.name)
            oracleFile.write(oracle)
            oracleFile.flush()
            self.logger.info(f"Oracle written to {oracleFile.name}")
            self.logger.info(f"CBMC query written to {cbmcFile.name}")
            # Make oracle executable
            os.chmod(oracleFile.name, 0o755)

            # Generate SyMO query
            query = self.generateSyMOQuery(name, proc, oracleFile.name)
            symoFile.write(query)
            symoFile.flush()
            self.logger.info(f"Query written to {symoFile.name}")

            # Close files so that they can be run safely
            oracleFile.close()
            symoFile.close()
            cbmcFile.close()

            # Run SyMO solver
            smtlib = self.runSolver(symoFile.name)

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

    def generateOracle(self, name: str, proc: Procedure, cbmc_query_path: str):
        oracle = f"""#!/bin/bash
# Oracle for {name}
LOG=.oracle_{name}.log
FILE={proc.filepath} # Path to the procedure
# Translate the SMT expression to C
CMD="python3 src/smt2c.py {proc.filepath} {proc.jsonpath} \\\"$1\\\""
echo \"$CMD\" > $LOG
EXPR=$(eval \"$CMD\")
echo \"$EXPR\" >> $LOG

# Generate cbmc query
PRE="true"
POST="($EXPR)"
DEFINES="#define PRECONDITION $PRE\\n#define POSTCONDITION $POST\\n"
echo -e \"$DEFINES\" > {cbmc_query_path}
cat $FILE >> {cbmc_query_path}

# Log cbmc query to {cbmc_query_path}
echo "====================" >> $LOG
cat {cbmc_query_path} >> $LOG
echo "====================" >> $LOG

# run cbmc
CMD="python3 src/symo_call_cbmc.py {proc.filepath} {proc.jsonpath} \\\"$PRE\\\" \\\"$POST\\\""
echo \"$CMD\" >> $LOG
RES=$(eval \"$CMD\")
echo \"$RES\" >> $LOG
echo \"$RES\"
        """
        return oracle

    # TODO: Add negative examples to the query using constraints
    def generateSyMOQuery(self, name: str, proc: Procedure, oracle_path: str):
        fun = "progSummary"
        oracle_name = f"cbmcChecker_{name}"
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
        input_names = [n for n, t in inputs]
        input_types = [t for n, t in inputs]
        neg_ex = [
            [val for assgn in io for _, val in assgn] for io in proc.negative_examples
        ]
        tgt_types = [
            d["tgttype"]
            for d in list(io["inputs"].values()) + list(io["outputs"].values())
        ]
        neg_ex = [
            [tc.tgt2smtlib(val, t) for val, t in zip(ex, tgt_types)] for ex in neg_ex
        ]
        neg_constraints = "\n".join(
            [f"(constraint (not ({fun} {' '.join(ex)})))" for ex in neg_ex]
        )
        query = f"""; SyMO query for {name}
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
        ;     0 1
        ;     (+ I I) (- I I) (* I I)
        ;     (ite B I I)
        ; ))

        (BV (_ BitVec 32) (
            {' '.join(bv_names)}
            (_ bv0 32) (_ bv1 32)
            (bvadd BV BV) (bvsub BV BV) (bvneg BV) (bvmul BV BV)
            ; (bvurem BV BV)
            (ite B BV BV)
        ))
    )
)

(declare-oracle-fun {oracle_name}
    {oracle_path}
    ( (-> {' '.join(input_types)} Bool) )
    Bool
)

(oracle-constraint
    {oracle_path}
    (
        ( {fun} (-> {' '.join(input_types)} Bool) )
    )
    (
        ( valid Bool ) {' '.join([f"({n} {t})" for n, t in inputs])}
    )
    ( => (not valid) ({fun} {' '.join(input_names)}) )
)

(constraint ({oracle_name} {fun}))
; Below are negative examples
{neg_constraints}

(check-synth)
"""
        return query

    # Solve the SyMO query and return the smtlib string
    def runSolver(self, query_path: str):
        cmd = f"{self.EXE} {query_path}"
        fail = False
        try:
            # Capture stdout and stderr
            proc = subprocess.Popen(
                cmd,
                shell=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            self.logger.info(f"Running: {cmd}")
            stdout, stderr = proc.communicate(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            fail = True
            proc.kill()
            stdout, stderr = proc.communicate()
            self.logger.error(f"SyMO solver timed out after {self.timeout} seconds")

        self.logger.debug(f"stdout: {stdout}")

        if not fail:
            # NOTE: Code below is for the binaries from
            # https://github.com/polgreen/delphi/releases/download/0.1
            # A successful run should end with these two lines
            # SOLUTION:
            # <function name> = <smtlib expression>
            lines = stdout.splitlines()
            assert len(lines) > 2, lines
            if lines[-2] != "SOLUTION:":
                self.logger.error(f"SyMO solver failed:\n{stdout=}\n{stderr=}")
                return None
            #     raise ValueError(
            #         f"SyMO solver failed when running `{cmd}`:\n{stdout=}\n{stderr=}"
            #     )
            smtlib = lines[-1].split("=", 1)[1].strip()
            return smtlib
        else:
            self.logger.error(f"SyMO solver failed:\n{stdout=}\n{stderr=}")
            return None


if __name__ == "__main__":
    import sys

    logging.basicConfig(level=logging.DEBUG)

    synth = SyMOSynthesizer(
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
