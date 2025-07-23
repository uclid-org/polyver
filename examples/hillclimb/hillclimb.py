from pathlib import Path

from uclid.builder import *
from uclid.builder_sugar import *

from polyver.main import getModelChecker
from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang


class HillClimbModule(Module):
    def __init__(self, delete=True, verbose=False):
        super().__init__("hillclimb", delete, verbose)
        hillclimb_reaction_1 = Procedure(
            name="hillclimb_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_reaction_1.c",
            jsonpath=Path(__file__).parent / "hillclimb_reaction_1.json",
        )
        hillclimb_reaction_2 = Procedure(
            name="hillclimb_reaction_2",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_reaction_2.c",
            jsonpath=Path(__file__).parent / "hillclimb_reaction_2.json",
        )
        hillclimb_climbing_reaction_1 = Procedure(
            name="hillclimb_climbing_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_climbing_reaction_1.c",
            jsonpath=Path(__file__).parent / "hillclimb_climbing_reaction_1.json",
        )
        hillclimb_climbing_reaction_2 = Procedure(
            name="hillclimb_climbing_reaction_2",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_climbing_reaction_2.c",
            jsonpath=Path(__file__).parent / "hillclimb_climbing_reaction_2.json",
        )
        hillclimb_rotate_reaction_1 = Procedure(
            name="hillclimb_rotate_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_rotate_reaction_1.c",
            jsonpath=Path(__file__).parent / "hillclimb_rotate_reaction_1.json",
        )
        hillclimb_straight_reaction_1 = Procedure(
            name="hillclimb_straight_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "hillclimb_straight_reaction_1.c",
            jsonpath=Path(__file__).parent / "hillclimb_straight_reaction_1.json",
        )
        accelerometer_reaction_1 = Procedure(
            name="accelerometer_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "accelerometer_reaction_1.c",
            jsonpath=Path(__file__).parent / "accelerometer_reaction_1.json",
        )
        tilt_reaction_1 = Procedure(
            name="tilt_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "tilt_reaction_1.c",
            jsonpath=Path(__file__).parent / "tilt_reaction_1.json",
        )
        gyro_reaction_1 = Procedure(
            name="gyro_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "gyro_reaction_1.c",
            jsonpath=Path(__file__).parent / "gyro_reaction_1.json",
        )
        trapezoidalintegrator_reaction_1 = Procedure(
            name="trapezoidalintegrator_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "trapezoidalintegrator_reaction_1.c",
            jsonpath=Path(__file__).parent / "trapezoidalintegrator_reaction_1.json",
        )
        motors_reaction_1 = Procedure(
            name="motors_reaction_1",
            lang=Lang.C,
            filepath=Path(__file__).parent / "motors_reaction_1.c",
            jsonpath=Path(__file__).parent / "motors_reaction_1.json",
        )
        motors_reaction_2 = Procedure(
            name="motors_reaction_2",
            lang=Lang.C,
            filepath=Path(__file__).parent / "motors_reaction_2.c",
            jsonpath=Path(__file__).parent / "motors_reaction_2.json",
        )
        self.procs = {
            hillclimb_reaction_1.name: hillclimb_reaction_1,
            hillclimb_reaction_2.name: hillclimb_reaction_2,
            hillclimb_climbing_reaction_1.name: hillclimb_climbing_reaction_1,
            hillclimb_climbing_reaction_2.name: hillclimb_climbing_reaction_2,
            hillclimb_rotate_reaction_1.name: hillclimb_rotate_reaction_1,
            hillclimb_straight_reaction_1.name: hillclimb_straight_reaction_1,
            accelerometer_reaction_1.name: accelerometer_reaction_1,
            tilt_reaction_1.name: tilt_reaction_1,
            gyro_reaction_1.name: gyro_reaction_1,
            trapezoidalintegrator_reaction_1.name: trapezoidalintegrator_reaction_1,
            motors_reaction_1.name: motors_reaction_1,
            motors_reaction_2.name: motors_reaction_2,
        }

    def buildUclidModule(self) -> UclidModule:
        m = UclidModule("main")
        UBoolFalse = UclidBooleanLiteral(False)
        UBoolTrue = UclidBooleanLiteral(True)
        value_bitwidth = 32
        bv = UclidBVType(value_bitwidth)

        port_t = m.mkRecordType(
            "port_t",
            [
                ("is_present", UBool),
                ("value", bv),
            ],
        )

        bool_port_t = m.mkRecordType(
            "bool_port_t",
            [
                ("is_present", UBool),
                ("value", UBool),
            ],
        )

        accelerometer_t = m.mkRecordType(
            "accelerometer_t",
            [
                ("x", port_t),
                ("y", port_t),
                ("z", port_t),
                ("trigger", bool_port_t),
            ],
        )

        gyro_t = m.mkRecordType(
            "gyro_t",
            [
                ("x", port_t),
                ("y", port_t),
                ("z", port_t),
                ("trigger", bool_port_t),
            ],
        )

        trapezoidalintegrator_self_t = m.mkRecordType(
            "trapezoidalintegrator_self_t",
            [
                ("s", bv),
                ("prev_in", bv),
                ("prev_time", bv),
            ],
        )

        trapezoidalintegrator_t = m.mkRecordType(
            "trapezoidalintegrator_t",
            [
                ("inp", port_t),
                ("out", port_t),
                ("self", trapezoidalintegrator_self_t),
            ],
        )

        tilt_t = m.mkRecordType(
            "tilt_t",
            [
                ("x", port_t),
                ("y", port_t),
                ("z", port_t),
                ("roll", port_t),
                ("pitch", port_t),
            ],
        )

        motors_t = m.mkRecordType(
            "motors_t",
            [
                ("left_power", port_t),
                ("right_power", port_t),
            ],
        )

        hillclimb_self_t = m.mkRecordType(
            "hillclimb_self_t",
            [
                ("last_angle", bv),
                ("uphill", UBool),
            ],
        )

        hillclimb_t = m.mkRecordType(
            "hillclimb_t",
            [
                ("self", hillclimb_self_t),
            ],
        )

        a = [m.mkVar(f"a{i}", accelerometer_t) for i in range(3)] + [
            m.mkVar("a", accelerometer_t)
        ]
        g = [m.mkVar(f"g{i}", gyro_t) for i in range(3)] + [m.mkVar("g", gyro_t)]
        trap = [m.mkVar(f"trap{i}", trapezoidalintegrator_t) for i in range(2)] + [
            m.mkVar("trap", trapezoidalintegrator_t)
        ]
        tilt = [m.mkVar(f"tilt{i}", tilt_t) for i in range(2)] + [
            m.mkVar("tilt", tilt_t)
        ]
        mo = [m.mkVar(f"m{i}", motors_t) for i in range(3)] + [m.mkVar("m", motors_t)]
        h = [m.mkVar(f"h{i}", hillclimb_t) for i in range(5)] + [
            m.mkVar("h", hillclimb_t)
        ]

        a_trigger = UclidLiteral("a_trigger")
        a_x = UclidLiteral("a_x")
        a_y = UclidLiteral("a_y")
        a_z = UclidLiteral("a_z")
        g_trigger = UclidLiteral("g_trigger")
        g_x = UclidLiteral("g_x")
        g_y = UclidLiteral("g_y")
        g_z = UclidLiteral("g_z")
        trap_inp = UclidLiteral("trap_inp")
        trap_out = UclidLiteral("trap_out")
        trap_self_input = UclidLiteral("trap_self")
        trap_self_output = UclidLiteral("trap_self_p")
        tilt_x = UclidLiteral("tilt_x")
        tilt_y = UclidLiteral("tilt_y")
        tilt_z = UclidLiteral("tilt_z")
        tilt_roll = UclidLiteral("tilt_roll")
        tilt_pitch = UclidLiteral("tilt_pitch")
        mo_left_power = UclidLiteral("mo_left_power")
        mo_right_power = UclidLiteral("mo_right_power")
        h_self_input = UclidLiteral("h_self")
        h_self_output = UclidLiteral("h_self_p")

        mode = [m.mkVar(f"mode{i}", UInt) for i in range(2)] + [m.mkVar("mode", UInt)]
        mode_input = UclidLiteral("mode")
        mode_output = UclidLiteral("mode_p")

        CLIMBING = m.mkConst("CLIMBING", UInt, UclidIntegerLiteral(0))
        ROTATE = m.mkConst("ROTATE", UInt, UclidIntegerLiteral(1))
        STRAIGHT = m.mkConst("STRAIGHT", UInt, UclidIntegerLiteral(2))

        hillclimb_reaction_1_fired = m.mkVar("hillclimb_reaction_1_fired", UBool)
        hillclimb_reaction_2_fired = m.mkVar("hillclimb_reaction_2_fired", UBool)
        hillclimb_climbing_reaction_1_fired = m.mkVar(
            "hillclimb_climbing_reaction_1_fired", UBool
        )
        hillclimb_climbing_reaction_2_fired = m.mkVar(
            "hillclimb_climbing_reaction_2_fired", UBool
        )
        hillclimb_rotate_reaction_1_fired = m.mkVar(
            "hillclimb_rotate_reaction_1_fired", UBool
        )
        hillclimb_straight_reaction_1_fired = m.mkVar(
            "hillclimb_straight_reaction_1_fired", UBool
        )
        accelerometer_reaction_1_fired = m.mkVar(
            "accelerometer_reaction_1_fired", UBool
        )
        tilt_reaction_1_fired = m.mkVar("tilt_reaction_1_fired", UBool)
        gyro_reaction_1_fired = m.mkVar("gyro_reaction_1_fired", UBool)
        trapezoidalintegrator_reaction_1_fired = m.mkVar(
            "trapezoidalintegrator_reaction_1_fired", UBool
        )
        motors_reaction_1_fired_1 = m.mkVar("motors_reaction_1_fired_1", UBool)
        motors_reaction_2_fired_1 = m.mkVar("motors_reaction_2_fired_1", UBool)
        motors_reaction_1_fired_2 = m.mkVar("motors_reaction_1_fired_2", UBool)
        motors_reaction_2_fired_2 = m.mkVar("motors_reaction_2_fired_2", UBool)

        fired = [
            hillclimb_reaction_1_fired,
            hillclimb_reaction_2_fired,
            hillclimb_climbing_reaction_1_fired,
            hillclimb_climbing_reaction_2_fired,
            hillclimb_rotate_reaction_1_fired,
            hillclimb_straight_reaction_1_fired,
            accelerometer_reaction_1_fired,
            tilt_reaction_1_fired,
            gyro_reaction_1_fired,
            trapezoidalintegrator_reaction_1_fired,
            motors_reaction_1_fired_1,
            motors_reaction_2_fired_1,
            motors_reaction_1_fired_2,
            motors_reaction_2_fired_2,
        ]

        # p = m.mkVar("p", pedestrian_t)
        # p0 = m.mkVar("p0", pedestrian_t)
        # p1 = m.mkVar("p1", pedestrian_t)
        # t = m.mkVar("t", traffic_light_t)
        # t0 = m.mkVar("t0", traffic_light_t)
        # t1 = m.mkVar("t1", traffic_light_t)
        # t2 = m.mkVar("t2", traffic_light_t)
        # t3 = m.mkVar("t3", traffic_light_t)

        # pedestrian_reaction_1_fired = m.mkVar("pedestrian_reaction_1_fired", UBool)
        # traffic_light_reaction_1_fired = m.mkVar(
        #     "traffic_light_reaction_1_fired", UBool
        # )
        # traffic_light_reaction_2_fired = m.mkVar(
        #     "traffic_light_reaction_2_fired", UBool
        # )
        # traffic_light_reaction_3_fired = m.mkVar(
        #     "traffic_light_reaction_3_fired", UBool
        # )

        reset_fire_sig = UclidProcedureSig(
            inputs=[],
            modifies=fired,
            returns=[],
            noinline=False,
        )
        reset_fire_proc = m.mkProcedure(
            "reset_fire",
            reset_fire_sig,
            UclidBlockStmt([UclidAssignStmt(f, UBoolFalse) for f in fired]),
        )

        hillclimb_reaction_1_requires = UclidRaw(
            self.procs["hillclimb_reaction_1"].getLatestUclidRequiresString()
        )
        hillclimb_reaction_1_ensures = UclidRaw(
            self.procs["hillclimb_reaction_1"].getLatestUclidEnsuresString()
        )
        hillclimb_reaction_1_sig = UclidProcedureSig(
            inputs=[(h_self_input, hillclimb_self_t)],
            # modifies=[mo[-1]],
            returns=[
                (mo_left_power, port_t),
                (mo_right_power, port_t),
                (h_self_output, hillclimb_self_t),
            ],
            requires=hillclimb_reaction_1_requires,
            ensures=hillclimb_reaction_1_ensures,
            noinline=True,
        )
        hillclimb_reaction_1_proc = m.mkProcedure(
            "hillclimb_reaction_1",
            hillclimb_reaction_1_sig,
            UclidBlockStmt([]),
        )

        hillclimb_reaction_2_requires = UclidRaw(
            self.procs["hillclimb_reaction_2"].getLatestUclidRequiresString()
        )
        hillclimb_reaction_2_ensures = UclidRaw(
            self.procs["hillclimb_reaction_2"].getLatestUclidEnsuresString()
        )
        hillclimb_reaction_2_sig = UclidProcedureSig(
            inputs=[(h_self_input, hillclimb_self_t)],
            # modifies=[a[-1], g[-1]],
            returns=[
                (a_trigger, bool_port_t),
                (g_trigger, bool_port_t),
                (h_self_output, hillclimb_self_t),
            ],
            requires=hillclimb_reaction_2_requires,
            ensures=hillclimb_reaction_2_ensures,
            noinline=True,
        )
        hillclimb_reaction_2_proc = m.mkProcedure(
            "hillclimb_reaction_2",
            hillclimb_reaction_2_sig,
            UclidBlockStmt([]),
        )

        hillclimb_climbing_reaction_1_requires = UclidRaw(
            self.procs["hillclimb_climbing_reaction_1"].getLatestUclidRequiresString()
        )
        hillclimb_climbing_reaction_1_ensures = UclidRaw(
            self.procs["hillclimb_climbing_reaction_1"].getLatestUclidEnsuresString()
        )
        hillclimb_climbing_reaction_1_sig = UclidProcedureSig(
            inputs=[(tilt_roll, port_t), (h_self_input, hillclimb_self_t)],
            # modifies=[h[-1], mo[-1]],
            returns=[
                (mo_left_power, port_t),
                (mo_right_power, port_t),
                (h_self_output, hillclimb_self_t),
            ],
            requires=hillclimb_climbing_reaction_1_requires,
            ensures=hillclimb_climbing_reaction_1_ensures,
            noinline=True,
        )
        hillclimb_climbing_reaction_1_proc = m.mkProcedure(
            "hillclimb_climbing_reaction_1",
            hillclimb_climbing_reaction_1_sig,
            UclidBlockStmt([]),
        )

        hillclimb_climbing_reaction_2_requires = UclidRaw(
            self.procs["hillclimb_climbing_reaction_2"].getLatestUclidRequiresString()
        )
        hillclimb_climbing_reaction_2_ensures = UclidRaw(
            self.procs["hillclimb_climbing_reaction_2"].getLatestUclidEnsuresString()
        )
        hillclimb_climbing_reaction_2_sig = UclidProcedureSig(
            inputs=[
                (tilt_pitch, port_t),
                (trap_out, port_t),
                (mode_input, UInt),
                (h_self_input, hillclimb_self_t),
            ],
            # modifies=[h[-1], mo[-1], mode[-1]],
            returns=[
                (mo_left_power, port_t),
                (mo_right_power, port_t),
                (mode_output, UInt),
                (h_self_output, hillclimb_self_t),
            ],
            requires=hillclimb_climbing_reaction_2_requires,
            ensures=hillclimb_climbing_reaction_2_ensures,
            noinline=True,
        )
        hillclimb_climbing_reaction_2_proc = m.mkProcedure(
            "hillclimb_climbing_reaction_2",
            hillclimb_climbing_reaction_2_sig,
            UclidBlockStmt([]),
        )

        hillclimb_rotate_reaction_1_requires = UclidRaw(
            self.procs["hillclimb_rotate_reaction_1"].getLatestUclidRequiresString()
        )
        hillclimb_rotate_reaction_1_ensures = UclidRaw(
            self.procs["hillclimb_rotate_reaction_1"].getLatestUclidEnsuresString()
        )
        hillclimb_rotate_reaction_1_sig = UclidProcedureSig(
            inputs=[
                (trap_out, port_t),
                (mode_input, UInt),
                (h_self_input, hillclimb_self_t),
            ],
            # modifies=[h[-1], mo[-1], mode[-1]],
            returns=[
                (mo_left_power, port_t),
                (mo_right_power, port_t),
                (mode_output, UInt),
                (h_self_output, hillclimb_self_t),
            ],
            requires=hillclimb_rotate_reaction_1_requires,
            ensures=hillclimb_rotate_reaction_1_ensures,
            noinline=True,
        )
        hillclimb_rotate_reaction_1_proc = m.mkProcedure(
            "hillclimb_rotate_reaction_1",
            hillclimb_rotate_reaction_1_sig,
            UclidBlockStmt([]),
        )

        hillclimb_straight_reaction_1_requires = UclidRaw(
            self.procs["hillclimb_straight_reaction_1"].getLatestUclidRequiresString()
        )
        hillclimb_straight_reaction_1_ensures = UclidRaw(
            self.procs["hillclimb_straight_reaction_1"].getLatestUclidEnsuresString()
        )
        hillclimb_straight_reaction_1_sig = UclidProcedureSig(
            inputs=[
                (tilt_pitch, port_t),
                (mode_input, UInt),
                (h_self_input, hillclimb_self_t),
            ],
            # modifies=[h[-1], mode[-1]],
            returns=[(mode_output, UInt), (h_self_output, hillclimb_self_t)],
            requires=hillclimb_straight_reaction_1_requires,
            ensures=hillclimb_straight_reaction_1_ensures,
            noinline=True,
        )
        hillclimb_straight_reaction_1_proc = m.mkProcedure(
            "hillclimb_straight_reaction_1",
            hillclimb_straight_reaction_1_sig,
            UclidBlockStmt([]),
        )

        accelerometer_reaction_1_requires = UclidRaw(
            self.procs["accelerometer_reaction_1"].getLatestUclidRequiresString()
        )
        accelerometer_reaction_1_ensures = UclidRaw(
            self.procs["accelerometer_reaction_1"].getLatestUclidEnsuresString()
        )
        accelerometer_reaction_1_sig = UclidProcedureSig(
            inputs=[(a_trigger, bool_port_t)],
            # modifies=[a[-1]],
            returns=[(a_x, port_t), (a_y, port_t), (a_z, port_t)],
            requires=accelerometer_reaction_1_requires,
            ensures=accelerometer_reaction_1_ensures,
            noinline=True,
        )
        accelerometer_reaction_1_proc = m.mkProcedure(
            "accelerometer_reaction_1",
            accelerometer_reaction_1_sig,
            UclidBlockStmt([]),
        )

        tilt_reaction_1_requires = UclidRaw(
            self.procs["tilt_reaction_1"].getLatestUclidRequiresString()
        )
        tilt_reaction_1_ensures = UclidRaw(
            self.procs["tilt_reaction_1"].getLatestUclidEnsuresString()
        )
        tilt_reaction_1_sig = UclidProcedureSig(
            inputs=[(tilt_x, port_t), (tilt_y, port_t), (tilt_z, port_t)],
            # modifies=[tilt[-1]],
            returns=[(tilt_roll, port_t), (tilt_pitch, port_t)],
            requires=tilt_reaction_1_requires,
            ensures=tilt_reaction_1_ensures,
            noinline=True,
        )
        tilt_reaction_1_proc = m.mkProcedure(
            "tilt_reaction_1",
            tilt_reaction_1_sig,
            UclidBlockStmt([]),
        )

        gyro_reaction_1_requires = UclidRaw(
            self.procs["gyro_reaction_1"].getLatestUclidRequiresString()
        )
        gyro_reaction_1_ensures = UclidRaw(
            self.procs["gyro_reaction_1"].getLatestUclidEnsuresString()
        )
        gyro_reaction_1_sig = UclidProcedureSig(
            inputs=[(g_trigger, bool_port_t)],
            # modifies=[g[-1]],
            returns=[(g_x, port_t), (g_y, port_t), (g_z, port_t)],
            requires=gyro_reaction_1_requires,
            ensures=gyro_reaction_1_ensures,
            noinline=True,
        )
        gyro_reaction_1_proc = m.mkProcedure(
            "gyro_reaction_1",
            gyro_reaction_1_sig,
            UclidBlockStmt([]),
        )

        trapezoidalintegrator_reaction_1_requires = UclidRaw(
            self.procs[
                "trapezoidalintegrator_reaction_1"
            ].getLatestUclidRequiresString()
        )
        trapezoidalintegrator_reaction_1_ensures = UclidRaw(
            self.procs["trapezoidalintegrator_reaction_1"].getLatestUclidEnsuresString()
        )
        trapezoidalintegrator_reaction_1_sig = UclidProcedureSig(
            inputs=[
                (trap_inp, port_t),
                (trap_self_input, trapezoidalintegrator_self_t),
            ],
            # modifies=[trap[-1]],
            returns=[
                (trap_out, port_t),
                (trap_self_output, trapezoidalintegrator_self_t),
            ],
            requires=trapezoidalintegrator_reaction_1_requires,
            ensures=trapezoidalintegrator_reaction_1_ensures,
            noinline=True,
        )
        trapezoidalintegrator_reaction_1_proc = m.mkProcedure(
            "trapezoidalintegrator_reaction_1",
            trapezoidalintegrator_reaction_1_sig,
            UclidBlockStmt([]),
        )

        motors_reaction_1_requires = UclidRaw(
            self.procs["motors_reaction_1"].getLatestUclidRequiresString()
        )
        motors_reaction_1_ensures = UclidRaw(
            self.procs["motors_reaction_1"].getLatestUclidEnsuresString()
        )
        motors_reaction_1_sig = UclidProcedureSig(
            inputs=[(mo_left_power, port_t)],
            # modifies=[],
            returns=[],
            requires=motors_reaction_1_requires,
            ensures=motors_reaction_1_ensures,
            noinline=True,
        )
        motors_reaction_1_proc = m.mkProcedure(
            "motors_reaction_1",
            motors_reaction_1_sig,
            UclidBlockStmt([]),
        )

        motors_reaction_2_requires = UclidRaw(
            self.procs["motors_reaction_2"].getLatestUclidRequiresString()
        )
        motors_reaction_2_ensures = UclidRaw(
            self.procs["motors_reaction_2"].getLatestUclidEnsuresString()
        )
        motors_reaction_2_sig = UclidProcedureSig(
            inputs=[(mo_right_power, port_t)],
            # modifies=[],
            returns=[],
            requires=motors_reaction_2_requires,
            ensures=motors_reaction_2_ensures,
            noinline=True,
        )
        motors_reaction_2_proc = m.mkProcedure(
            "motors_reaction_2",
            motors_reaction_2_sig,
            UclidBlockStmt([]),
        )

        state_0_sig = UclidProcedureSig(
            inputs=[],
            modifies=a + g + trap + tilt + mo + h + mode + fired,
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
                    UclidAssignStmt(h[0], h[-1]),
                    UclidAssignStmt(hillclimb_reaction_1_fired, UBoolTrue),
                    UclidProcedureCallStmt(
                        hillclimb_reaction_1_proc,
                        [UclidRecordSelect(h[-1], "self")],
                        [
                            UclidRecordSelect(mo[-1], "left_power"),
                            UclidRecordSelect(mo[-1], "right_power"),
                            UclidRecordSelect(h[-1], "self"),
                        ],
                    ),
                    UclidAssignStmt(h[1], h[-1]),
                    UclidAssignStmt(mo[0], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "left_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_1_fired_1, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_1_proc,
                                    [UclidRecordSelect(mo[-1], "left_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(mo[0], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "right_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_2_fired_1, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_2_proc,
                                    [UclidRecordSelect(mo[-1], "right_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(h[1], h[-1]),
                    UclidAssignStmt(a[0], a[-1]),
                    UclidAssignStmt(g[0], g[-1]),
                    UclidAssignStmt(hillclimb_reaction_2_fired, UBoolTrue),
                    UclidProcedureCallStmt(
                        hillclimb_reaction_2_proc,
                        [UclidRecordSelect(h[-1], "self")],
                        [
                            UclidRecordSelect(a[-1], "trigger"),
                            UclidRecordSelect(g[-1], "trigger"),
                            UclidRecordSelect(h[-1], "self"),
                        ],
                    ),
                    UclidAssignStmt(h[2], h[-1]),
                    UclidAssignStmt(a[1], a[-1]),
                    UclidAssignStmt(g[1], g[-1]),
                    UclidAssignStmt(a[1], a[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(a[-1], "trigger.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    accelerometer_reaction_1_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    accelerometer_reaction_1_proc,
                                    [UclidRecordSelect(a[-1], "trigger")],
                                    [
                                        UclidRecordSelect(a[-1], "x"),
                                        UclidRecordSelect(a[-1], "y"),
                                        UclidRecordSelect(a[-1], "z"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(a[2], a[-1]),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "x"), UclidRecordSelect(a[-1], "x")
                    ),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "y"), UclidRecordSelect(a[-1], "y")
                    ),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "z"), UclidRecordSelect(a[-1], "z")
                    ),
                    UclidAssignStmt(tilt[0], tilt[-1]),
                    UclidITEStmt(
                        Uor(
                            [
                                UclidRecordSelect(tilt[-1], "x.is_present"),
                                UclidRecordSelect(tilt[-1], "y.is_present"),
                                UclidRecordSelect(tilt[-1], "z.is_present"),
                            ]
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(tilt_reaction_1_fired, UBoolTrue),
                                UclidProcedureCallStmt(
                                    tilt_reaction_1_proc,
                                    [
                                        UclidRecordSelect(tilt[-1], "x"),
                                        UclidRecordSelect(tilt[-1], "y"),
                                        UclidRecordSelect(tilt[-1], "z"),
                                    ],
                                    [
                                        UclidRecordSelect(tilt[-1], "roll"),
                                        UclidRecordSelect(tilt[-1], "pitch"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(tilt[1], tilt[-1]),
                    UclidAssignStmt(g[1], g[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(g[-1], "trigger.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(gyro_reaction_1_fired, UBoolTrue),
                                UclidProcedureCallStmt(
                                    gyro_reaction_1_proc,
                                    [UclidRecordSelect(g[-1], "trigger")],
                                    [
                                        UclidRecordSelect(g[-1], "x"),
                                        UclidRecordSelect(g[-1], "y"),
                                        UclidRecordSelect(g[-1], "z"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(g[2], g[-1]),
                    UclidAssignStmt(
                        UclidRecordSelect(trap[-1], "inp"),
                        UclidRecordSelect(g[-1], "z"),
                    ),
                    UclidAssignStmt(trap[0], trap[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(trap[-1], "inp.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    trapezoidalintegrator_reaction_1_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    trapezoidalintegrator_reaction_1_proc,
                                    [
                                        UclidRecordSelect(trap[-1], "inp"),
                                        UclidRecordSelect(trap[-1], "self"),
                                    ],
                                    [
                                        UclidRecordSelect(trap[-1], "out"),
                                        UclidRecordSelect(trap[-1], "self"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(trap[1], trap[-1]),
                    UclidAssignStmt(h[2], h[-1]),
                    UclidAssignStmt(tilt[1], tilt[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(tilt[-1], "roll.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    hillclimb_climbing_reaction_1_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    hillclimb_climbing_reaction_1_proc,
                                    [
                                        UclidRecordSelect(tilt[-1], "roll"),
                                        UclidRecordSelect(h[-1], "self"),
                                    ],
                                    [
                                        UclidRecordSelect(mo[-1], "left_power"),
                                        UclidRecordSelect(mo[-1], "right_power"),
                                        UclidRecordSelect(h[-1], "self"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(h[3], h[-1]),
                    UclidAssignStmt(mo[1], mo[-1]),
                    UclidAssignStmt(h[3], h[-1]),
                    UclidAssignStmt(tilt[1], tilt[-1]),
                    UclidAssignStmt(trap[1], trap[-1]),
                    UclidAssignStmt(mode[0], mode[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(tilt[-1], "pitch.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    hillclimb_climbing_reaction_2_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    hillclimb_climbing_reaction_2_proc,
                                    [
                                        UclidRecordSelect(tilt[-1], "pitch"),
                                        UclidRecordSelect(trap[-1], "out"),
                                        mode[-1],
                                        UclidRecordSelect(h[-1], "self"),
                                    ],
                                    [
                                        UclidRecordSelect(mo[-1], "left_power"),
                                        UclidRecordSelect(mo[-1], "right_power"),
                                        mode[-1],
                                        UclidRecordSelect(h[-1], "self"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(h[4], h[-1]),
                    UclidAssignStmt(mo[2], mo[-1]),
                    UclidAssignStmt(mode[1], mode[-1]),
                    UclidAssignStmt(mo[2], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "left_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_1_fired_2, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_1_proc,
                                    [UclidRecordSelect(mo[-1], "left_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(mo[2], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "right_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_2_fired_2, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_2_proc,
                                    [UclidRecordSelect(mo[-1], "right_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                ]
            ),
        )

        state_1_sig = UclidProcedureSig(
            inputs=[],
            modifies=a + g + trap + tilt + mo + h + mode + fired,
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
                    UclidAssignStmt(h[1], h[-1]),
                    UclidAssignStmt(a[0], a[-1]),
                    UclidAssignStmt(g[0], g[-1]),
                    UclidAssignStmt(hillclimb_reaction_2_fired, UBoolTrue),
                    UclidProcedureCallStmt(
                        hillclimb_reaction_2_proc,
                        [UclidRecordSelect(h[-1], "self")],
                        [
                            UclidRecordSelect(a[-1], "trigger"),
                            UclidRecordSelect(g[-1], "trigger"),
                            UclidRecordSelect(h[-1], "self"),
                        ],
                    ),
                    UclidAssignStmt(h[2], h[-1]),
                    UclidAssignStmt(a[1], a[-1]),
                    UclidAssignStmt(g[1], g[-1]),
                    UclidAssignStmt(a[1], a[-1]),
                    UclidITEStmt(
                        # UclidRecordSelect(a[-1], "trigger.is_present"),
                        UclidRecordSelect(
                            UclidRecordSelect(a[-1], "trigger"), "is_present"
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    accelerometer_reaction_1_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    accelerometer_reaction_1_proc,
                                    [UclidRecordSelect(a[-1], "trigger")],
                                    [
                                        UclidRecordSelect(a[-1], "x"),
                                        UclidRecordSelect(a[-1], "y"),
                                        UclidRecordSelect(a[-1], "z"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(a[2], a[-1]),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "x"), UclidRecordSelect(a[-1], "x")
                    ),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "y"), UclidRecordSelect(a[-1], "y")
                    ),
                    UclidAssignStmt(
                        UclidRecordSelect(tilt[-1], "z"), UclidRecordSelect(a[-1], "z")
                    ),
                    UclidAssignStmt(tilt[0], tilt[-1]),
                    UclidITEStmt(
                        Uor(
                            [
                                UclidRecordSelect(tilt[-1], "x.is_present"),
                                UclidRecordSelect(tilt[-1], "y.is_present"),
                                UclidRecordSelect(tilt[-1], "z.is_present"),
                            ]
                        ),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(tilt_reaction_1_fired, UBoolTrue),
                                UclidProcedureCallStmt(
                                    tilt_reaction_1_proc,
                                    [
                                        UclidRecordSelect(tilt[-1], "x"),
                                        UclidRecordSelect(tilt[-1], "y"),
                                        UclidRecordSelect(tilt[-1], "z"),
                                    ],
                                    [
                                        UclidRecordSelect(tilt[-1], "roll"),
                                        UclidRecordSelect(tilt[-1], "pitch"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(tilt[1], tilt[-1]),
                    UclidAssignStmt(g[1], g[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(g[-1], "trigger.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(gyro_reaction_1_fired, UBoolTrue),
                                UclidProcedureCallStmt(
                                    gyro_reaction_1_proc,
                                    [UclidRecordSelect(g[-1], "trigger")],
                                    [
                                        UclidRecordSelect(g[-1], "x"),
                                        UclidRecordSelect(g[-1], "y"),
                                        UclidRecordSelect(g[-1], "z"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(g[2], g[-1]),
                    UclidAssignStmt(
                        UclidRecordSelect(trap[-1], "inp"),
                        UclidRecordSelect(g[-1], "z"),
                    ),
                    UclidAssignStmt(trap[0], trap[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(trap[-1], "inp.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(
                                    trapezoidalintegrator_reaction_1_fired, UBoolTrue
                                ),
                                UclidProcedureCallStmt(
                                    trapezoidalintegrator_reaction_1_proc,
                                    [
                                        UclidRecordSelect(trap[-1], "inp"),
                                        UclidRecordSelect(trap[-1], "self"),
                                    ],
                                    [
                                        UclidRecordSelect(trap[-1], "out"),
                                        UclidRecordSelect(trap[-1], "self"),
                                    ],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(trap[1], trap[-1]),
                    UclidCaseStmt(
                        [
                            Ueq([mode[-1], CLIMBING]),
                            Ueq([mode[-1], ROTATE]),
                            Ueq([mode[-1], STRAIGHT]),
                        ],
                        [
                            UclidBlockStmt(
                                [
                                    UclidAssignStmt(h[2], h[-1]),
                                    UclidAssignStmt(tilt[1], tilt[-1]),
                                    UclidITEStmt(
                                        UclidRecordSelect(tilt[-1], "roll.is_present"),
                                        UclidBlockStmt(
                                            [
                                                UclidAssignStmt(
                                                    hillclimb_climbing_reaction_1_fired,
                                                    UBoolTrue,
                                                ),
                                                UclidProcedureCallStmt(
                                                    hillclimb_climbing_reaction_1_proc,
                                                    [
                                                        UclidRecordSelect(
                                                            tilt[-1], "roll"
                                                        ),
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                    [
                                                        UclidRecordSelect(
                                                            mo[-1], "left_power"
                                                        ),
                                                        UclidRecordSelect(
                                                            mo[-1], "right_power"
                                                        ),
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                ),
                                            ]
                                        ),
                                    ),
                                    UclidAssignStmt(h[3], h[-1]),
                                    UclidAssignStmt(mo[1], mo[-1]),
                                    UclidAssignStmt(h[3], h[-1]),
                                    UclidAssignStmt(tilt[1], tilt[-1]),
                                    UclidAssignStmt(trap[1], trap[-1]),
                                    UclidAssignStmt(mode[0], mode[-1]),
                                    UclidITEStmt(
                                        UclidRecordSelect(tilt[-1], "pitch.is_present"),
                                        UclidBlockStmt(
                                            [
                                                UclidAssignStmt(
                                                    hillclimb_climbing_reaction_2_fired,
                                                    UBoolTrue,
                                                ),
                                                UclidProcedureCallStmt(
                                                    hillclimb_climbing_reaction_2_proc,
                                                    [
                                                        UclidRecordSelect(
                                                            tilt[-1], "pitch"
                                                        ),
                                                        UclidRecordSelect(
                                                            trap[-1], "out"
                                                        ),
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                    [
                                                        UclidRecordSelect(
                                                            mo[-1], "left_power"
                                                        ),
                                                        UclidRecordSelect(
                                                            mo[-1], "right_power"
                                                        ),
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                ),
                                            ]
                                        ),
                                    ),
                                    UclidAssignStmt(h[4], h[-1]),
                                    UclidAssignStmt(mo[2], mo[-1]),
                                    UclidAssignStmt(mode[1], mode[-1]),
                                ]
                            ),
                            UclidBlockStmt(
                                [
                                    UclidAssignStmt(h[2], h[-1]),
                                    UclidAssignStmt(trap[1], trap[-1]),
                                    UclidAssignStmt(mode[0], mode[-1]),
                                    UclidITEStmt(
                                        UclidRecordSelect(trap[-1], "out.is_present"),
                                        UclidBlockStmt(
                                            [
                                                UclidAssignStmt(
                                                    hillclimb_rotate_reaction_1_fired,
                                                    UBoolTrue,
                                                ),
                                                UclidProcedureCallStmt(
                                                    hillclimb_rotate_reaction_1_proc,
                                                    [
                                                        UclidRecordSelect(
                                                            trap[-1], "out"
                                                        ),
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                    [
                                                        UclidRecordSelect(
                                                            mo[-1], "left_power"
                                                        ),
                                                        UclidRecordSelect(
                                                            mo[-1], "right_power"
                                                        ),
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                ),
                                            ]
                                        ),
                                    ),
                                    UclidAssignStmt(h[3], h[-1]),
                                    UclidAssignStmt(mo[1], mo[-1]),
                                    UclidAssignStmt(mode[1], mode[-1]),
                                ]
                            ),
                            UclidBlockStmt(
                                [
                                    UclidAssignStmt(h[2], h[-1]),
                                    UclidAssignStmt(tilt[1], tilt[-1]),
                                    UclidAssignStmt(mode[0], mode[-1]),
                                    UclidITEStmt(
                                        UclidRecordSelect(tilt[-1], "pitch.is_present"),
                                        UclidBlockStmt(
                                            [
                                                UclidAssignStmt(
                                                    hillclimb_straight_reaction_1_fired,
                                                    UBoolTrue,
                                                ),
                                                UclidProcedureCallStmt(
                                                    hillclimb_straight_reaction_1_proc,
                                                    [
                                                        UclidRecordSelect(
                                                            tilt[-1], "pitch"
                                                        ),
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                    [
                                                        mode[-1],
                                                        UclidRecordSelect(
                                                            h[-1], "self"
                                                        ),
                                                    ],
                                                ),
                                            ]
                                        ),
                                    ),
                                    UclidAssignStmt(h[3], h[-1]),
                                    UclidAssignStmt(mode[1], mode[-1]),
                                ]
                            ),
                        ],
                    ),
                    UclidAssignStmt(mo[2], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "left_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_1_fired_2, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_1_proc,
                                    [UclidRecordSelect(mo[-1], "left_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                    UclidAssignStmt(mo[2], mo[-1]),
                    UclidITEStmt(
                        UclidRecordSelect(mo[-1], "right_power.is_present"),
                        UclidBlockStmt(
                            [
                                UclidAssignStmt(motors_reaction_2_fired_2, UBoolTrue),
                                UclidProcedureCallStmt(
                                    motors_reaction_2_proc,
                                    [UclidRecordSelect(mo[-1], "right_power")],
                                    [],
                                ),
                            ]
                        ),
                    ),
                ]
            ),
        )

        state = m.mkVar("state", UInt)
        num_states = m.mkConst("num_states", UInt, UclidIntegerLiteral(2))
        cycle_start = m.mkConst("cycle_start", UInt, UclidIntegerLiteral(1))

        state_machine_sig = UclidProcedureSig(
            inputs=[],
            modifies=a + g + trap + tilt + mo + h + mode + fired + [state],
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
                        ],
                        [
                            UclidProcedureCallStmt(state_1_proc, [], []),
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

        m.setInit(
            UclidInitBlock(
                [
                    UclidHavocStmt(a[-1]),
                    UclidHavocStmt(g[-1]),
                    UclidHavocStmt(trap[-1]),
                    UclidHavocStmt(tilt[-1]),
                    UclidHavocStmt(mo[-1]),
                    UclidHavocStmt(h[-1]),
                    UclidAssignStmt(mode[-1], CLIMBING),
                ]
                + [UclidAssignStmt(v, a[-1]) for v in a[:-1]]
                + [UclidAssignStmt(v, g[-1]) for v in g[:-1]]
                + [UclidAssignStmt(v, trap[-1]) for v in trap[:-1]]
                + [UclidAssignStmt(v, tilt[-1]) for v in tilt[:-1]]
                + [UclidAssignStmt(v, mo[-1]) for v in mo[:-1]]
                + [UclidAssignStmt(v, h[-1]) for v in h[:-1]]
                + [UclidAssignStmt(v, mode[-1]) for v in mode[:-1]]
                + [
                    UclidProcedureCallStmt(reset_fire_proc, [], []),
                    UclidProcedureCallStmt(state_0_proc, [], []),
                    UclidAssignStmt(state, UclidIntegerLiteral(1)),
                ]
            )
        )

        m.setNext(UclidNextBlock(UclidProcedureCallStmt(state_machine_proc, [], [])))

        m.mkProperty(
            "PROP",
            Uimplies(
                [
                    Ueq([mode[-1], CLIMBING]),
                    Uor(
                        [
                            Ugte(
                                [
                                    UclidRecordSelect(tilt[-1], "pitch.value"),
                                    UclidBVLiteral(3, value_bitwidth),
                                ]
                            ),
                            Ulte(
                                [
                                    UclidRecordSelect(tilt[-1], "pitch.value"),
                                    UclidBVLiteral(-3, value_bitwidth),
                                ]
                            ),
                        ]
                    ),
                ]
            ),
        )

        m.setControl(
            UclidControlBlock(
                [
                    UclidBMCCommand("v", 2),
                    UclidCheckCommand(),
                    UclidPrintResultsCommand(),
                    UclidPrintCexJSONCommand(
                        "v",
                        sum(
                            [
                                [
                                    UclidRecordSelect(v, f"{p}.{attr}")
                                    for attr in ["is_present", "value"]
                                    for p in ["x", "y", "z", "trigger"]
                                ]
                                for v in a
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"{p}.{attr}")
                                    for attr in ["is_present", "value"]
                                    for p in ["x", "y", "z", "trigger"]
                                ]
                                for v in g
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"{p}.{attr}")
                                    for attr in ["is_present", "value"]
                                    for p in ["inp", "out"]
                                ]
                                + [
                                    UclidRecordSelect(v, f"self.{attr}")
                                    for attr in ["s", "prev_in", "prev_time"]
                                ]
                                for v in trap
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"{p}.{attr}")
                                    for attr in ["is_present", "value"]
                                    for p in ["x", "y", "z", "roll", "pitch"]
                                ]
                                for v in tilt
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"{p}.{attr}")
                                    for attr in ["is_present", "value"]
                                    for p in ["left_power", "right_power"]
                                ]
                                for v in mo
                            ]
                            + [
                                [
                                    UclidRecordSelect(v, f"self.{attr}")
                                    for attr in ["last_angle", "uphill"]
                                ]
                                for v in h
                            ]
                            + [mode]
                            + [fired],
                            [],
                        ),
                    ),
                ]
            )
        )

        return m


if __name__ == "__main__":
    m = HillClimbModule()
    # print(m.buildUclidModule.__inject__())
    mc = getModelChecker(m)
    res = mc.check()
    mc.report("./result.json")
