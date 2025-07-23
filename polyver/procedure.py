import json
from dataclasses import dataclass, field

from .dsl import FalseExpr, TrueExpr
from .utils import Lang


@dataclass
class Procedure:
    """
    A class to represent procedures written in target languages like C or Rust.

    Attributes
    ----------
    name : str
        function name
    lang : str
        function's implementation language
    filepath : str
        path to file storing function implementation
    jsonpath : str
        path to file storing function metadata
    requires : list[str]
        history of requires
    ensures : list[str]
        history of ensures
    invocations : list
        stores all invocations (input/output args) in a uclid module
    positive_examples: set
        stores positive examples obtained from running the external verifier
    negative_examples: set
        stores negative examples obtained from running uclid
    synthesis_time : float
        time taken to synthesize the procedure
    synthesis_attempts : int
        number of attempts made to synthesize the procedure
    synthesize : bool
        whether to synthesize pre/post-conditions for the procedure
    """

    name: str
    lang: Lang
    filepath: str
    jsonpath: str
    # Pre/post-conditions are initialized to True and False
    requires: list = field(default_factory=lambda: [TrueExpr()])
    ensures: list = field(default_factory=lambda: [FalseExpr()])
    invocations: list = field(default_factory=list)
    positive_examples: set = field(default_factory=set)
    negative_examples: set = field(default_factory=set)
    synthesis_time: float = 0.0
    synthesis_attempts: int = 0
    # Whether to synthesize pre/post-conditions for the procedure
    synthesize: bool = True

    def __post_init__(self):
        with open(self.filepath, "r") as f:
            self.code = f.read()
        with open(self.jsonpath, "r") as f:
            self.data = json.load(f)

        self.buildNameMappings()

    def __str__(self):
        ret = """Name:\t{}
Lang:\t{}
Code: (path: {})
\t{}
Requires:\t{}
Ensures: \t{}
Invocations:\t{}
Pos examples:\t{}
Neg examples:\t{}
Data: \t{}
Name mapping tgt->ucl (pre/post translation):
\t{}
Name mapping ucl->tgt (cex parsing)
\t{}""".format(
            self.name,
            self.lang,
            self.filepath,
            self.code.replace("\n", "\n\t"),
            self.requires,
            self.ensures,
            self.invocations,
            self.positive_examples,
            self.negative_examples,
            self.data,
            self.tgt2ucl_map,
            self.ucl2tgt_map,
        )
        return ret

    def buildNameMappings(self):
        # tgt2ucl_map: tgtname -> uclname
        # ex: {"init_self": "t1.self", "self": "t.self"}
        self.tgt2ucl_map = {}
        for inp in self.data["inputs"]:
            self.tgt2ucl_map[inp["tgtname"]] = inp["uclname"]
        for out in self.data["outputs"]:
            self.tgt2ucl_map[out["tgtname"]] = out["uclname"]

        """
        ucl2tgt_map: flag -> {(inputs: {uclname -> {tgtname, tgttype, ucltype}},
                               outputs: {uclname -> {tgtname, tgttype, ucltype})}
        ex: {
              "traffic_light_reaction_2_fired": {
                "inputs": {
                  "t1.self._mode": {
                    "tgt_name": "init_self->_mode",
                    "tgttype": "int",
                    "ucltype": "bv64"
                  },
                  ...,
                }
                "outputs": {
                  "t2.self._mode": {
                    "tgt_name": "self->_mode",
                    "tgttype": "int",
                    "ucltype": "bv64"
                  },
                  ...
                },
              },
              ...
            }
        """

        self.ucl2tgt_map = {}
        for call in self.data["uclcalls"]:
            inputs, outputs, flag = call["inputs"], call["outputs"], call["flag"]
            # assert flag not in self.ucl2tgt_map.keys(), "Duplicate flag found"
            in_tgtnames, in_uclnames, out_tgtnames, out_uclnames = [], [], [], []
            for i, inp in enumerate(inputs):
                in_data = self.data["inputs"][i]
                in_uclnames += self.getFieldsWithName(
                    inp, in_data["ucltype"], Lang.UCLID5
                )
                in_tgtnames += self.getFieldsWithName(
                    in_data["tgtname"], in_data["tgttype"], Lang.C
                )
            for i, out in enumerate(outputs):
                out_data = self.data["outputs"][i]
                out_uclnames += self.getFieldsWithName(
                    out, out_data["ucltype"], Lang.UCLID5
                )
                out_tgtnames += self.getFieldsWithName(
                    out_data["tgtname"], out_data["tgttype"], Lang.C
                )
            self.ucl2tgt_map[flag] = {
                "inputs": {
                    uclname: {
                        "tgtname": tgtname,
                        "tgttype": tgttype,
                        "ucltype": ucltype,
                    }
                    for (uclname, ucltype), (tgtname, tgttype) in zip(
                        in_uclnames, in_tgtnames
                    )
                },
                "outputs": {
                    uclname: {
                        "tgtname": tgtname,
                        "tgttype": tgttype,
                        "ucltype": ucltype,
                    }
                    for (uclname, ucltype), (tgtname, tgttype) in zip(
                        out_uclnames, out_tgtnames
                    )
                },
            }

    def getFieldsWithName(self, name, typ, lang=Lang.UCLID5):
        return [(name + s, t) for s, t in self.getFieldNamesWithTypes(typ, lang)]

    # Returns a list of suffixes for a given type
    def getFieldNamesWithTypes(self, typ, lang=Lang.UCLID5):
        assert self.lang in [Lang.C, Lang.RUST], "Only C and Rust supported"
        # NOTE: Only handles single level of pointer
        is_pointer = typ[-1] == "*"
        use_pointer = lang in [Lang.C]
        use_arrow = use_pointer and is_pointer
        typ = typ[:-1].strip() if is_pointer else typ
        if typ not in self.data["types"].keys():
            return [("", typ)]

        suffixes = []
        t = "ucltype" if lang == Lang.UCLID5 else "tgttype"
        for field_name, field_data in self.data["types"][typ]["fields"].items():
            suffixes += [
                (("->" if use_arrow else ".") + field_name + s, t)
                for s, t in self.getFieldNamesWithTypes(field_data[t])
            ]

        return suffixes

    def getLatestUclidRequiresString(self):
        return self.requires[-1].translate(Lang.UCLID5)

    def getLatestUclidEnsuresString(self):
        return self.ensures[-1].translate(Lang.UCLID5)


if __name__ == "__main__":
    print(Procedure.__doc__)
    import sys

    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    proc = Procedure("null", Lang.C, codepath, jsonpath)
    print(proc)
