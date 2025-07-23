import sys

from ..dsl_parser import str2Expr
from ..procedure import Procedure
from ..utils import Lang
from .smt_parser import ASTTransformer, defineFunParser

if __name__ == "__main__":
    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    smtlib = sys.argv[3]

    proc = Procedure(
        name="null",
        lang=Lang.C,
        filepath=codepath,
        jsonpath=jsonpath,
    )

    # Parse and transform
    parsed_tree = defineFunParser.parse(smtlib)
    expr = ASTTransformer().transform(parsed_tree)

    with open("smt2c.log", "a") as f:
        f.write(smtlib)
        f.write("\n")
        f.write(parsed_tree.pretty())
        f.write("\n")
        f.write(expr)

    exprObj = str2Expr(expr, proc.data)
    # NOTE: MAKE SURE THIS FILE ONLY PRINTS THIS LINE
    print(exprObj.translate(Lang.C))
