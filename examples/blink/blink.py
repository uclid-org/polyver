from pathlib import Path

from uclid.builder import *
from uclid.builder_sugar import *

from polyver.main import getModelChecker
from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang


class BlinkLEDModule(Module):
    def __init__(self, delete=True, verbose=False):
        super().__init__(delete, verbose)
        pico_set_led = Procedure(
            name="pico_set_led",
            lang=Lang.C,
            filepath=Path(__file__).parent / "blink.c",
            jsonpath=Path(__file__).parent / "blink.json",
        )
        self.procs = {pico_set_led.name: pico_set_led}

    def buildUclidModule(self) -> UclidModule:
        m = UclidModule("main")

        led_on = UclidBooleanVar("led_on")
        led_state = UclidBVVar("led_state", 32)
        led_state_prev = UclidBVVar("led_state_prev", 32)

        m.mkBooleanVar("led_on")
        m.mkBVVar("led_state", 32)
        m.mkBVVar("led_state_prev", 32)

        requires = UclidRaw(self.procs["pico_set_led"].getLatestUclidRequiresString())
        ensures = UclidRaw(self.procs["pico_set_led"].getLatestUclidEnsuresString())
        pico_set_led_sig = UclidProcedureSig(
            inputs=[],
            modifies=[led_state],
            returns=[],
            requires=requires,
            ensures=ensures,
            noinline=True,
        )
        pico_set_led_proc = m.mkProcedure(
            "pico_set_led",
            pico_set_led_sig,
            UclidBlockStmt(),
        )

        state_0_sig = UclidProcedureSig(
            inputs=[],
            modifies=[led_on, led_state, led_state_prev],
            returns=[],
            noinline=False,
        )
        state_0_proc = m.mkProcedure(
            "state_0",
            state_0_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(led_state_prev, led_state),
                    UclidAssignStmt(led_on, UclidBooleanLiteral(True)),
                    UclidProcedureCallStmt(pico_set_led_proc, [], []),
                    UclidAssignStmt(led_on, UclidBooleanLiteral(False)),
                    UclidProcedureCallStmt(pico_set_led_proc, [], []),
                ]
            ),
        )

        m.setInit(
            UclidInitBlock(
                [
                    UclidAssignStmt(led_on, UclidBooleanLiteral(False)),
                    UclidAssignStmt(led_state, UclidBVLiteral(0, 32)),
                    UclidAssignStmt(led_state_prev, UclidBVLiteral(0, 32)),
                ]
            )
        )

        m.setNext(
            UclidNextBlock(
                [
                    UclidProcedureCallStmt(state_0_proc, [], []),
                ]
            )
        )

        m.mkProperty(
            "same_state",
            Uand(
                [
                    Ueq(
                        [
                            led_state,
                            led_state_prev,
                        ]
                    ),
                    Ueq(
                        [
                            led_state_prev,
                            UclidBVLiteral(0, 32),
                        ]
                    ),
                ]
            ),
        )

        m.setControl(
            UclidControlBlock(
                [
                    UclidInductionCommand("v"),
                    UclidCheckCommand(),
                    UclidPrintResultsCommand(),
                    UclidPrintCexJSONCommand("v"),
                ]
            )
        )

        return m


if __name__ == "__main__":
    m = BlinkLEDModule()
    # print(m.buildUclidModule().__inject__())
    mc = getModelChecker(m)
    mc.check()
    mc.report("./result.json")
