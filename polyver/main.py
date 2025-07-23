from pathlib import Path

from .checker import ModelChecker
from .parse_args import polyver_args


def getModelChecker(module):
    match polyver_args.synthesizer:
        case "human":
            from .synthesizers.human_synthesizer import HumanSynthesizer

            synthesizer = HumanSynthesizer()
        case "llm":
            from .synthesizers.llm_synthesizer import LLMSynthesizer

            synthesizer = LLMSynthesizer(
                model=polyver_args.model,
                method=polyver_args.method,
                num_calls=polyver_args.parallel_calls,
                max_attempts=polyver_args.max_attempts,
                error_feedback=polyver_args.error_feedback,
                verbose=polyver_args.verbose,
                # FIXME: The getLogger('ModelCheckerLogger') is officially created in
                # ModelChecker below. Not sure if calling it here is the best practice.
            )
        case "symo":
            from .synthesizers.symo_synthesizer import SyMOSynthesizer

            synthesizer = SyMOSynthesizer(
                verbose=polyver_args.verbose,
                delete=False,
            )
        case "sygus":
            from .synthesizers.sygus_synthesizer import SyGuSSynthesizer

            synthesizer = SyGuSSynthesizer(
                verbose=polyver_args.verbose,
                delete=False,
            )
        case _:
            raise ValueError(f"Unknown synthesizer: {polyver_args.synthesizer}")

    if polyver_args.log_base:
        basename = Path(polyver_args.log_base)
    else:
        basename = Path("/tmp") / "logs" / type(module).__name__

    init_solution = None
    if polyver_args.init_solution:
        import json

        with open(polyver_args.init_solution) as f:
            result = json.load(f)
        init_solution = result["witness"]

    mc = ModelChecker(
        module,
        synthesizer=synthesizer,
        parallel_synth=polyver_args.parallel_synth,
        cegis_iter_limit=polyver_args.cegis_iter_limit,
        cegar_iter_limit=polyver_args.cegar_iter_limit,
        verif_timeout=polyver_args.verif_timeout,
        synth_timeout=polyver_args.synth_timeout,
        delete=False,
        verbose=polyver_args.verbose,
        shepherd=polyver_args.shepherd,
        log_base=basename,
        init_solution=init_solution,
        json_report=polyver_args.json_report,
    )
    return mc
