from pathlib import Path

from uclid.builder import *
from uclid.builder_sugar import *

from polyver.main import getModelChecker
from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang


class ExampleModule(Module):
    def __init__(self, delete=True, verbose=False):
        super().__init__("example", delete, verbose)
        foo = Procedure(
            name="foo",
            lang=Lang.C,
            filepath=Path(__file__).parent / "foo.c",
            jsonpath=Path(__file__).parent / "foo.json",
        )
        self.procs = {foo.name: foo}

    def buildUclidModule(self) -> UclidModule:
        bits = 32
        valType = UclidBVType(bits)
        m = UclidModule("main")
        x = m.mkVar("x", valType)
        y = m.mkVar("y", valType)
        init_y = m.mkVar("init_y", valType)
        i = UclidLiteral("i")
        r = UclidLiteral("r")
        foo_fired = m.mkVar("foo_fired", UclidBooleanType())

        requires = UclidRaw(self.procs["foo"].getLatestUclidRequiresString())
        ensures = UclidRaw(self.procs["foo"].getLatestUclidEnsuresString())
        proc_sig = UclidProcedureSig(
            inputs=[(i, valType)],
            modifies=None,
            returns=[(r, valType)],
            requires=requires,
            ensures=ensures,
            noinline=True,
        )
        foo = m.mkProcedure(
            "foo",
            proc_sig,
            UclidBlockStmt(
                [
                    UclidComment(self.procs["foo"].code),
                ]
            ),
        )

        step_sig = UclidProcedureSig(
            inputs=[],
            modifies=[x, y, init_y, foo_fired],
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )
        step = m.mkProcedure(
            "step",
            step_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(x, y),
                    UclidAssignStmt(init_y, y),
                    UclidAssignStmt(foo_fired, UclidBooleanLiteral(True)),
                    self.addProcedureCallStmt(foo, [init_y], [y]),
                ]
            ),
        )

        m.setInit(
            UclidInitBlock(
                [
                    UclidAssignStmt(x, UclidBVLiteral(0, bits)),
                    UclidAssignStmt(y, UclidBVLiteral(50, bits)),
                    UclidAssignStmt(init_y, y),
                    UclidAssignStmt(foo_fired, UclidBooleanLiteral(False)),
                ]
            )
        )

        m.setNext(
            UclidNextBlock(
                [UclidProcedureCallStmt(step, [], [])]
                # [
                #     UclidAssignStmt(x.p(), y),
                #     self.addProcedureCallStmt(foo, [y], [y.p()]),
                # ]
            )
        )

        m.mkProperty("diff", Ugte([Usub([y, x]), UclidBVLiteral(50, bits)]))

        m.setControl(
            UclidControlBlock(
                [
                    UclidBMCCommand("v", 3),
                    UclidCheckCommand(),
                    UclidPrintResultsCommand(),
                    UclidPrintCexJSONCommand("v", [x, y, init_y, foo_fired]),
                ]
            )
        )

        return m


if __name__ == "__main__":
    m = ExampleModule()
    # print(m.buildUclidModule().__inject__())
    mc = getModelChecker(m)
    mc.check()
    mc.report("./result.json")
