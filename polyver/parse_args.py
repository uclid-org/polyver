import argparse

polyver_parser = argparse.ArgumentParser(description="Polyglot verification")

polyver_parser.add_argument(
    "-s",
    "--synthesizer",
    type=str,
    default="llm",
    choices=["llm", "human", "symo", "sygus"],
    help="type of synthesizer",
)
polyver_parser.add_argument(
    "--model",
    type=str,
    default="gpt-4o-2024-08-06",
    choices=["gpt-4o-2024-08-06", "gpt-4", "o1-preview", "o1-mini", "o3-mini"],
    help="model name",
)
polyver_parser.add_argument(
    "--method",
    type=str,
    default="chain-of-thought",
    choices=["chain-of-thought", "zero-shot"],
    help="LLM technique",
)
polyver_parser.add_argument(
    "--cegis_iter_limit", type=int, default=5, help="CEGIS iteration limit"
)
polyver_parser.add_argument(
    "--cegar_iter_limit", type=int, default=5, help="CEGAR iteration limit"
)
polyver_parser.add_argument(
    "--verif_timeout", type=int, default=120, help="external verifier timeout"
)
polyver_parser.add_argument(
    "--synth_timeout", type=int, default=120, help="synthesizer timeout"
)
polyver_parser.add_argument(
    "--parallel_calls", type=int, default=3, help="parallel calls to llm"
)
polyver_parser.add_argument(
    "--parallel_synth",
    action="store_true",
    help="synthesize contracts for all procedures in parallel",
)
polyver_parser.add_argument(
    "--max_attempts", type=int, default=3, help="max attempts to synthesize"
)
polyver_parser.add_argument(
    "--error_feedback", action="store_true", help="cex feedback for synthesis"
)
polyver_parser.add_argument(
    "--shepherd", action="store_true", help="ask for key press to continue"
)
polyver_parser.add_argument(
    "-v", "--verbose", action="store_true", help="print debug logs"
)
polyver_parser.add_argument(
    "--log_base",
    type=str,
    default=None,
    help="log file basename, default: None",
)

polyver_parser.add_argument(
    "--json_report",
    type=str,
    default="result.json",
    help="json report file name, default: result.json",
)

polyver_parser.add_argument(
    "--abort_synth_fail",
    action="store_true",
    help="abort on synthesis failure",
)

polyver_parser.add_argument(
    "--init_solution",
    type=str,
    default=None,
    help="initial solution file",
)

polyver_args = polyver_parser.parse_args()
