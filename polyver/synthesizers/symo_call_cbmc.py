import os
import sys

from ..procedure import Procedure
from ..utils import Lang, Result
from ..utils import TypeConverter as tc
from ..utils import getDefaultValue
from ..verifiers.cbmc_verifier import CbmcVerifier

if __name__ == "__main__":
    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    pre = sys.argv[3]
    post = sys.argv[4]

    name = os.path.basename(codepath).split(".")[0]
    proc = Procedure(
        name,
        Lang.C,
        codepath,
        jsonpath,
    )

    cv = CbmcVerifier(proc, delete=False, verbose=True)
    res, example = cv.verify(
        pre=pre,
        post=post,
    )

    io = list(proc.ucl2tgt_map.values())[0]
    tgt_types = [
        d["tgttype"] for d in list(io["inputs"].values()) + list(io["outputs"].values())
    ]
    if example is not None:
        # example is of the form (((<name>, <value>), ...), ((<name>, <value>), ...))
        # where the first tuple is the input name-value pairs
        # and the second tuple is the output name-value pairs
        # extract all the values from the example and put in a list
        # print(example)
        example = [val for tup in example for _, val in tup]
        example = [tc.tgt2smtlib(val, t) for val, t in zip(example, tgt_types)]
    else:
        example = [tc.tgt2smtlib(getDefaultValue(t), t) for t in tgt_types]

    # NOTE: MAKE SURE THIS FILE ONLY PRINTS THIS LINE
    print(str(res == Result.EXT_SUCCESS).lower(), " ".join(map(str, example)))
