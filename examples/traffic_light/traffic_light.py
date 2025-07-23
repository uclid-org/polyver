from pathlib import Path

from uclid.builder import *
from uclid.builder_sugar import *

from polyver.main import getModelChecker
from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang


class TrafficLightModule(Module):
    def __init__(self, delete=True, verbose=False):
        super().__init__("traffic_light", delete, verbose)
        pedestrian_reaction_1 = Procedure(
            name="pedestrian_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "pedestrian_reaction_1.c",
            jsonpath=Path(__file__).parent / "pedestrian_reaction_1.json",
        )
        traffic_light_reaction_1 = Procedure(
            name="traffic_light_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "traffic_light_reaction_1.c",
            jsonpath=Path(__file__).parent / "traffic_light_reaction_1.json",
        )
        traffic_light_reaction_2 = Procedure(
            name="traffic_light_reaction_2",
            lang=Lang.C,
            filepath=Path(__file__).parent / "traffic_light_reaction_2.c",
            jsonpath=Path(__file__).parent / "traffic_light_reaction_2.json",
        )
        traffic_light_reaction_3 = Procedure(
            name="traffic_light_reaction_3",
            lang=Lang.C,
            filepath=Path(__file__).parent / "traffic_light_reaction_3.c",
            jsonpath=Path(__file__).parent / "traffic_light_reaction_3.json",
        )
        self.procs = {
            pedestrian_reaction_1.name: pedestrian_reaction_1,
            traffic_light_reaction_1.name: traffic_light_reaction_1,
            traffic_light_reaction_2.name: traffic_light_reaction_2,
            traffic_light_reaction_3.name: traffic_light_reaction_3,
        }

    def buildUclidModule(self) -> UclidModule:
        m = UclidModule("main")
        flag_bit = 64
        value_bit = 64
        port_t = m.mkRecordType(
            "port_t",
            [
                ("is_present", UclidBVType(flag_bit)),
                ("value", UclidBVType(value_bit)),
            ],
        )

        trigger_t = m.mkRecordType(
            "trigger_t",
            [
                ("is_present", UclidBVType(flag_bit)),
            ],
        )

        pedestrian_t = m.mkRecordType(
            "pedestrian_t",
            [
                ("out", port_t),
            ],
        )

        traffic_light_self_t = m.mkRecordType(
            "traffic_light_self_t",
            [
                ("_mode", UclidBVType(value_bit)),
                ("count", UclidBVType(value_bit)),
            ],
        )

        traffic_light_t = m.mkRecordType(
            "traffic_light_t",
            [
                ("pedestrian", port_t),
                ("sigR", port_t),
                ("sigG", port_t),
                ("sigY", port_t),
                ("self", traffic_light_self_t),
                ("resetCount", trigger_t),
            ],
        )

        p = m.mkVar("p", pedestrian_t)
        p0 = m.mkVar("p0", pedestrian_t)
        p1 = m.mkVar("p1", pedestrian_t)
        t = m.mkVar("t", traffic_light_t)
        t0 = m.mkVar("t0", traffic_light_t)
        t1 = m.mkVar("t1", traffic_light_t)
        t2 = m.mkVar("t2", traffic_light_t)
        t3 = m.mkVar("t3", traffic_light_t)

        t_input = UclidLiteral("t")
        t_output = UclidLiteral("tp")
        p_input = UclidLiteral("p")
        p_output = UclidLiteral("pp")

        pedestrian_reaction_1_fired = m.mkVar("pedestrian_reaction_1_fired", UBool)
        traffic_light_reaction_1_fired = m.mkVar(
            "traffic_light_reaction_1_fired", UBool
        )
        traffic_light_reaction_2_fired = m.mkVar(
            "traffic_light_reaction_2_fired", UBool
        )
        traffic_light_reaction_3_fired = m.mkVar(
            "traffic_light_reaction_3_fired", UBool
        )

        reset_fire_sig = UclidProcedureSig(
            inputs=[],
            modifies=[
                pedestrian_reaction_1_fired,
                traffic_light_reaction_1_fired,
                traffic_light_reaction_2_fired,
                traffic_light_reaction_3_fired,
            ],
            returns=[],
            noinline=False,
        )

        reset_fire_proc = m.mkProcedure(
            "reset_fire",
            reset_fire_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(
                        pedestrian_reaction_1_fired, UclidBooleanLiteral(False)
                    ),
                    UclidAssignStmt(
                        traffic_light_reaction_1_fired, UclidBooleanLiteral(False)
                    ),
                    UclidAssignStmt(
                        traffic_light_reaction_2_fired, UclidBooleanLiteral(False)
                    ),
                    UclidAssignStmt(
                        traffic_light_reaction_3_fired, UclidBooleanLiteral(False)
                    ),
                ]
            ),
        )

        pedestrian_reaction_1_requires = UclidRaw(
            self.procs["pedestrian_reaction_1"].getLatestUclidRequiresString()
        )
        pedestrian_reaction_1_ensures = UclidRaw(
            self.procs["pedestrian_reaction_1"].getLatestUclidEnsuresString()
        )
        pedestrian_reaction_1_sig = UclidProcedureSig(
            inputs=[(p_input, pedestrian_t)],
            # modifies=[p],
            returns=[(p_output, pedestrian_t)],
            requires=pedestrian_reaction_1_requires,
            ensures=pedestrian_reaction_1_ensures,
            noinline=True,
        )
        pedestrian_reaction_1_proc = m.mkProcedure(
            "pedestrian_reaction_1",
            pedestrian_reaction_1_sig,
            UclidBlockStmt([]),
        )

        traffic_light_reaction_1_requires = UclidRaw(
            self.procs["traffic_light_reaction_1"].getLatestUclidRequiresString()
        )
        traffic_light_reaction_1_ensures = UclidRaw(
            self.procs["traffic_light_reaction_1"].getLatestUclidEnsuresString()
        )
        traffic_light_reaction_1_sig = UclidProcedureSig(
            inputs=[(t_input, traffic_light_t)],
            # modifies=[t],
            returns=[(t_output, traffic_light_t)],
            requires=traffic_light_reaction_1_requires,
            ensures=traffic_light_reaction_1_ensures,
            noinline=True,
        )
        traffic_light_reaction_1_proc = m.mkProcedure(
            "traffic_light_reaction_1",
            traffic_light_reaction_1_sig,
            UclidBlockStmt([]),
        )

        traffic_light_reaction_2_requires = UclidRaw(
            self.procs["traffic_light_reaction_2"].getLatestUclidRequiresString()
        )
        traffic_light_reaction_2_ensures = UclidRaw(
            self.procs["traffic_light_reaction_2"].getLatestUclidEnsuresString()
        )
        traffic_light_reaction_2_sig = UclidProcedureSig(
            inputs=[(t_input, traffic_light_t)],
            # modifies=[t],
            returns=[(t_output, traffic_light_t)],
            requires=traffic_light_reaction_2_requires,
            ensures=traffic_light_reaction_2_ensures,
            noinline=True,
        )
        traffic_light_reaction_2_proc = m.mkProcedure(
            "traffic_light_reaction_2",
            traffic_light_reaction_2_sig,
            UclidBlockStmt([]),
        )

        traffic_light_reaction_3_requires = UclidRaw(
            self.procs["traffic_light_reaction_3"].getLatestUclidRequiresString()
        )
        traffic_light_reaction_3_ensures = UclidRaw(
            self.procs["traffic_light_reaction_3"].getLatestUclidEnsuresString()
        )
        traffic_light_reaction_3_sig = UclidProcedureSig(
            inputs=[(t_input, traffic_light_t)],
            # modifies=[t],
            returns=[(t_output, traffic_light_t)],
            requires=traffic_light_reaction_3_requires,
            ensures=traffic_light_reaction_3_ensures,
            noinline=True,
        )
        traffic_light_reaction_3_proc = m.mkProcedure(
            "traffic_light_reaction_3",
            traffic_light_reaction_3_sig,
            UclidBlockStmt([]),
        )

        state_0_sig = UclidProcedureSig(
            inputs=[],
            modifies=[
                t,
                t0,
                t1,
                t2,
                t3,
                traffic_light_reaction_1_fired,
                traffic_light_reaction_2_fired,
                traffic_light_reaction_3_fired,
            ],
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )
        state_0_proc = m.mkProcedure(
            "state_0",
            state_0_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(t0, t),
                    UclidAssignStmt(
                        traffic_light_reaction_1_fired, UclidBooleanLiteral(True)
                    ),
                    UclidProcedureCallStmt(traffic_light_reaction_1_proc, [t], [t]),
                    UclidAssignStmt(t1, t),
                    UclidAssignStmt(
                        traffic_light_reaction_2_fired, UclidBooleanLiteral(True)
                    ),
                    UclidProcedureCallStmt(traffic_light_reaction_2_proc, [t], [t]),
                    UclidAssignStmt(t2, t),
                    UclidITEStmt(
                        Ueq(
                            [
                                UclidRecordSelect(t, "resetCount.is_present"),
                                UclidBVLiteral(1, flag_bit),
                            ]
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    traffic_light_reaction_3_fired,
                                    UclidBooleanLiteral(True),
                                ),
                                UclidProcedureCallStmt(
                                    traffic_light_reaction_3_proc, [t], [t]
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(t3, t),
                ]
            ),
        )

        state_1_sig = UclidProcedureSig(
            inputs=[],
            modifies=[
                p,
                p0,
                p1,
                t,
                t0,
                t1,
                t2,
                t3,
                pedestrian_reaction_1_fired,
                traffic_light_reaction_2_fired,
                traffic_light_reaction_3_fired,
            ],
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )
        state_1_proc = m.mkProcedure(
            "state_1",
            state_1_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(p0, p),
                    UclidAssignStmt(
                        pedestrian_reaction_1_fired, UclidBooleanLiteral(True)
                    ),
                    UclidProcedureCallStmt(pedestrian_reaction_1_proc, [p], [p]),
                    UclidAssignStmt(p1, p),
                    UclidAssignStmt(t1, t),
                    UclidAssignStmt(
                        traffic_light_reaction_2_fired, UclidBooleanLiteral(True)
                    ),
                    UclidProcedureCallStmt(traffic_light_reaction_2_proc, [t], [t]),
                    UclidAssignStmt(t2, t),
                    UclidITEStmt(
                        Ueq(
                            [
                                UclidRecordSelect(t, "resetCount.is_present"),
                                UclidBVLiteral(1, flag_bit),
                            ]
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    traffic_light_reaction_3_fired,
                                    UclidBooleanLiteral(True),
                                ),
                                UclidProcedureCallStmt(
                                    traffic_light_reaction_3_proc, [t], [t]
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(t3, t),
                ]
            ),
        )

        state_2_to_10_sig = UclidProcedureSig(
            inputs=[],
            modifies=[
                p,
                t,
                t1,
                t2,
                t3,
                traffic_light_reaction_2_fired,
                traffic_light_reaction_3_fired,
            ],
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )
        state_2_to_10_proc = m.mkProcedure(
            "state_2_to_10",
            state_2_to_10_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(t1, t),
                    UclidAssignStmt(
                        traffic_light_reaction_2_fired, UclidBooleanLiteral(True)
                    ),
                    UclidProcedureCallStmt(traffic_light_reaction_2_proc, [t], [t]),
                    UclidAssignStmt(t2, t),
                    UclidITEStmt(
                        Ueq(
                            [
                                UclidRecordSelect(t, "resetCount.is_present"),
                                UclidBVLiteral(1, flag_bit),
                            ]
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    traffic_light_reaction_3_fired,
                                    UclidBooleanLiteral(True),
                                ),
                                UclidProcedureCallStmt(
                                    traffic_light_reaction_3_proc, [t], [t]
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(t3, t),
                ]
            ),
        )

        state = m.mkVar("state", UInt)
        num_states = m.mkConst("num_states", UInt, UclidIntegerLiteral(11))
        cycle_start = m.mkConst("cycle_start", UInt, UclidIntegerLiteral(1))

        state_machine_sig = UclidProcedureSig(
            inputs=[],
            modifies=[
                t,
                t0,
                t1,
                t2,
                t3,
                p,
                p0,
                p1,
                pedestrian_reaction_1_fired,
                traffic_light_reaction_1_fired,
                traffic_light_reaction_2_fired,
                traffic_light_reaction_3_fired,
                state,
            ],
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )

        state_machine_proc = m.mkProcedure(
            "state_machine",
            state_machine_sig,
            UclidBlockStmt(
                [
                    UclidProcedureCallStmt(reset_fire_proc, [], []),
                    UclidCaseStmt(
                        [
                            Ueq([state, UclidIntegerLiteral(1)]),
                            Uand(
                                [
                                    Ugte([state, UclidIntegerLiteral(2)]),
                                    Ult([state, UclidIntegerLiteral(10)]),
                                ]
                            ),
                        ],
                        [
                            UclidProcedureCallStmt(state_1_proc, [], []),
                            UclidProcedureCallStmt(state_2_to_10_proc, [], []),
                        ],
                    ),
                    UclidITEStmt(
                        Ueq([state, Usub([num_states, UclidIntegerLiteral(1)])]),
                        UclidAssignStmt(state, cycle_start),
                        UclidAssignStmt(state, Uadd([state, UclidIntegerLiteral(1)])),
                    ),
                ]
            ),
        )

        # p_init = (
        #     "const_record(out := const_record(is_present := false, value := 0bv64))"
        # )
        # t_init = (
        #     "const_record(pedestrian := const_record(is_present := false, value := 0bv64),"
        #     "sigR := const_record(is_present := false, value := 0bv64),"
        #     "sigG := const_record(is_present := false, value := 0bv64),"
        #     "sigY := const_record(is_present := false, value := 0bv64),"
        #     "self := const_record(_mode := 0bv64, count := 0bv64),"
        #     "resetCount := const_record(is_present := false))"
        # )

        m.setInit(
            UclidInitBlock(
                [
                    # UclidRaw(f"p  = {p_init};"),
                    # UclidRaw(f"p0 = {p_init};"),
                    # UclidRaw(f"p1 = {p_init};"),
                    # UclidRaw(f"t  = {t_init};"),
                    # UclidRaw(f"t0 = {t_init};"),
                    # UclidRaw(f"t1 = {t_init};"),
                    # UclidRaw(f"t2 = {t_init};"),
                    # UclidRaw(f"t3 = {t_init};"),
                    UclidAssignStmt(
                        UclidRecordSelect(p, "out.is_present"),
                        UclidBVLiteral(0, flag_bit),
                    ),
                    UclidAssignStmt(
                        UclidRecordSelect(p, "out.value"), UclidBVLiteral(0, value_bit)
                    ),
                    # UclidHavocStmt(p),
                    UclidAssignStmt(p0, p),
                    UclidAssignStmt(p1, p),
                    UclidHavocStmt(t),
                    UclidAssignStmt(t0, t),
                    UclidAssignStmt(t1, t),
                    UclidAssignStmt(t2, t),
                    UclidAssignStmt(t3, t),
                    UclidProcedureCallStmt(reset_fire_proc, [], []),
                    UclidProcedureCallStmt(state_0_proc, [], []),
                    UclidAssignStmt(state, UclidIntegerLiteral(1)),
                ]
            )
        )

        m.setNext(
            UclidNextBlock(
                UclidProcedureCallStmt(state_machine_proc, [], [])
                # [
                #     UclidCaseStmt(
                #         [
                #             Ueq([state, UclidIntegerLiteral(1)]),
                #             Uand(
                #                 [
                #                     Ugte([state, UclidIntegerLiteral(2)]),
                #                     Ult([state, UclidIntegerLiteral(10)]),
                #                 ]
                #             ),
                #         ],
                #         [
                #             UclidProcedureCallStmt(state_1_proc, [], []),
                #             UclidProcedureCallStmt(state_2_to_10_proc, [], []),
                #         ],
                #     ),
                #     UclidITEStmt(
                #         Ueq([state, Usub([num_states, UclidIntegerLiteral(1)])]),
                #         UclidAssignStmt(state.p(), cycle_start),
                #         UclidAssignStmt(
                #             state.p(), Uadd([state, UclidIntegerLiteral(1)])
                #         ),
                #     ),
                # ]
            )
        )

        m.mkProperty(
            "RED_LE_60",
            Uimplies(
                [
                    Ueq(
                        [
                            UclidRecordSelect(t, "self._mode"),
                            UclidBVLiteral(0, value_bit),
                        ]
                    ),
                    Ulte(
                        [
                            UclidRecordSelect(t, "self.count"),
                            UclidBVLiteral(60, value_bit),
                        ]
                    ),
                ]
            ),
        )

        m.setControl(
            UclidControlBlock(
                [
                    UclidBMCCommand("v", 5),
                    UclidCheckCommand(),
                    UclidPrintResultsCommand(),
                    UclidPrintCexJSONCommand(
                        "v",
                        sum(
                            [
                                [
                                    UclidRecordSelect(v, f"out.{attr}")
                                    for attr in ["is_present", "value"]
                                ]
                                for v in [p, p0, p1]
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"{attr}.is_present")
                                    for attr in ["resetCount", "sigR", "sigG", "sigY"]
                                ]
                                + [
                                    UclidRecordSelect(v, f"{attr}.value")
                                    for attr in ["sigR", "sigG", "sigY"]
                                ]
                                + [
                                    UclidRecordSelect(v, f"self.{attr}")
                                    for attr in ["_mode", "count"]
                                ]
                                for v in [t, t0, t1, t2, t3]
                            ]
                            + [
                                [
                                    pedestrian_reaction_1_fired,
                                    traffic_light_reaction_1_fired,
                                    traffic_light_reaction_2_fired,
                                    traffic_light_reaction_3_fired,
                                ]
                            ],
                            [],
                        ),
                    ),
                ]
            )
        )

        return m


if __name__ == "__main__":
    m = TrafficLightModule()
    # print(m.buildUclidModule().__inject__())
    mc = getModelChecker(m)
    res = mc.check()
    mc.report("./result.json")
