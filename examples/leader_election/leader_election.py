from pathlib import Path

from uclid.builder import *
from uclid.builder_sugar import *

from polyver.main import getModelChecker
from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang


class LeaderElectionModule(Module):
    def __init__(self, num_nodes, delete=True, verbose=False):
        super().__init__("leader_election", delete, verbose)
        step = Procedure(
            name="step",
            lang=Lang.C,
            filepath=Path(__file__).parent / "step.c",
            jsonpath=Path(__file__).parent / "step.json",
        )
        self.procs = {step.name: step}
        self.num_nodes = num_nodes

    def buildUclidModule(self) -> UclidModule:
        m = UclidModule("main")
        node_t = m.mkRecordType(
            "node_t",
            [
                ("id", UclidBVType(32)),
                ("m", UclidBVType(32)),
                ("win", UclidBVType(32)),
                # ("id", UInt),
                # ("m", UInt),
                # ("win", UInt),
            ],
        )
        one = UclidBVLiteral(1, 32)
        zero = UclidBVLiteral(0, 32)
        # one = UclidIntegerLiteral(1)
        # zero = UclidIntegerLiteral(0)

        nodes = [m.mkVar(f"n{i}", node_t) for i in range(self.num_nodes)]
        tmp_nodes = [m.mkVar(f"n{i}p", node_t) for i in range(self.num_nodes)]
        src = UclidLiteral("src")
        dst = UclidLiteral("dst")
        r = UclidLiteral("r")

        fired = [
            m.mkVar(f"step_fired_{i}", UclidBooleanType())
            for i in range(self.num_nodes)
        ]

        requires = UclidRaw(self.procs["step"].getLatestUclidRequiresString())
        ensures = UclidRaw(self.procs["step"].getLatestUclidEnsuresString())
        step_sig = UclidProcedureSig(
            inputs=[(src, node_t), (dst, node_t)],
            modifies=None,
            returns=[(r, node_t)],
            requires=requires,
            ensures=ensures,
            noinline=True,
        )
        step_proc = m.mkProcedure(
            "step",
            step_sig,
            UclidBlockStmt(
                [
                    UclidAssignStmt(r, dst),
                    UclidITEStmt(
                        Ueq(
                            [UclidRecordSelect(src, "m"), UclidRecordSelect(dst, "id")]
                        ),
                        UclidAssignStmt(UclidRecordSelect(r, "win"), one),
                    ),
                    UclidITEStmt(
                        Ugte(
                            [UclidRecordSelect(src, "m"), UclidRecordSelect(dst, "id")]
                        ),
                        UclidAssignStmt(
                            UclidRecordSelect(r, "m"), UclidRecordSelect(src, "m")
                        ),
                    ),
                ]
            ),
        )

        udpate_sig = UclidProcedureSig(
            inputs=[],
            modifies=nodes + tmp_nodes + fired,
            returns=[],
            requires=None,
            ensures=None,
            noinline=False,
        )
        update_proc = m.mkProcedure(
            "update",
            udpate_sig,
            UclidBlockStmt(
                [UclidAssignStmt(tmp_nodes[i], nodes[i]) for i in range(len(nodes))]
                + [UclidAssignStmt(f, UclidBooleanLiteral(True)) for f in fired]
                + [
                    self.addProcedureCallStmt(
                        step_proc, [tmp_nodes[i], tmp_nodes[i + 1]], [nodes[i + 1]]
                    )
                    for i in range(len(nodes) - 1)
                ]
                + [
                    self.addProcedureCallStmt(
                        step_proc, [tmp_nodes[-1], tmp_nodes[0]], [nodes[0]]
                    )
                ]
            ),
        )

        m.mkAxiom(
            "distinct_id",
            Uand(
                [
                    Uneq(
                        [
                            UclidRecordSelect(nodes[i], "id"),
                            UclidRecordSelect(nodes[j], "id"),
                        ]
                    )
                    for i in range(len(nodes) - 1)
                    for j in range(i + 1, len(nodes))
                ]
            ),
        )

        m.setInit(
            UclidInitBlock(
                [
                    UclidAssumeStmt(
                        Uand(
                            [
                                Ueq(
                                    [
                                        UclidRecordSelect(n, "id"),
                                        UclidRecordSelect(n, "m"),
                                    ]
                                ),
                                Ueq(
                                    [
                                        UclidRecordSelect(n, "win"),
                                        zero,
                                    ]
                                ),
                            ]
                        )
                    )
                    for n in nodes
                ]
                + [UclidAssignStmt(tmp_n, n) for n, tmp_n in zip(nodes, tmp_nodes)]
                + [UclidAssignStmt(f, UclidBooleanLiteral(False)) for f in fired]
            )
        )

        m.setNext(
            UclidNextBlock(
                [
                    UclidProcedureCallStmt(update_proc, [], []),
                ]
            )
        )

        m.mkProperty(
            "unique_leader",
            Uand(
                [
                    Uimplies(
                        [
                            Uand(
                                [
                                    Ueq(
                                        [
                                            UclidRecordSelect(nodes[i], "win"),
                                            one,
                                        ]
                                    ),
                                    Ueq(
                                        [
                                            UclidRecordSelect(nodes[j], "win"),
                                            one,
                                        ]
                                    ),
                                ]
                            ),
                            Ueq(
                                [
                                    UclidRecordSelect(nodes[i], "id"),
                                    UclidRecordSelect(nodes[j], "id"),
                                ]
                            ),
                        ]
                    )
                    for i in range(len(nodes) - 1)
                    for j in range(i + 1, len(nodes))
                ]
            ),
        )

        m.setControl(
            UclidControlBlock(
                [
                    UclidBMCCommand("v", self.num_nodes),
                    UclidCheckCommand(),
                    UclidPrintResultsCommand(),
                    # UclidPrintCexJSONCommand(
                    UclidPrintCexCommand(
                        "v",
                        sum(
                            [
                                [
                                    UclidRecordSelect(n, attr)
                                    for attr in ["id", "m", "win"]
                                ]
                                for n in nodes + tmp_nodes
                            ]
                            + [fired],
                            [],
                        ),
                    ),
                ]
            )
        )

        return m


if __name__ == "__main__":
    m = LeaderElectionModule(4)
    # print(m.buildUclidModule().__inject__())
    mc = getModelChecker(m)
    res = mc.check()
    mc.report("./result.json")
