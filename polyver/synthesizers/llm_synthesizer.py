import json
import logging

from openai import OpenAI

from ..dsl import *
from ..dsl_parser import str2Expr
from ..procedure import Procedure
from ..synthesizer import Synthesizer
from ..utils import invoke_parallel
from .llm_utils import (
    ChatHistory,
    get_assignment_string,
    getDSLDoc,
    getDSLExample,
    parse_return_string_from_python_function,
)

# import random


class LLMSynthesizer(Synthesizer):
    """
    A class to synthesize preconditions and postconditions
    for a given piece of code using OpenAI's model.

    Attributes
    ----------
    openai : OpenAI
        An instance of OpenAI class to interact with OpenAI's API
    model : str
        The name of the model to use for synthesis (default "gpt-3.5-turbo")
        Possible values: "gpt-3.5-turbo", "gpt-4", "gpt-4-turbo-preview"
    max_tokens : int
        The maximum number of tokens to use for synthesis (default 1000)
    method : str
        The method to use for synthesis. (default "zero-shot")
        Possible values: "zero-shot", "chain-of-thought"

    Methods
    -------
    synthesizeZeroShot(proc: Procedure) -> str
        Synthesizes preconditions and postconditions
        for the given procedure using zero-shot method
    synthesizeChainOfThought(proc: Procedure) -> str
        Synthesizes preconditions and postconditions
        for the given procedure using chain-of-thought method
    getSystemMessage(proc: Procedure) -> str
        Returns the system message for the given procedure
    getUserMessage(proc: Procedure) -> str
        Returns the user message for the given procedure
    callOpenAI(messages: list) -> str
        Calls OpenAI's API with the given messages and returns the response
    """

    def __init__(
        self,
        model: str = "gpt-3.5-turbo",
        method: str = "zero-shot",
        num_calls: int = 1,
        max_attempts: int = 1,
        error_feedback=True,
        verbose=False,
        logger=None,
    ):
        super().__init__(verbose)
        self.openai = OpenAI()
        self.model = model
        self.method = method
        self.num_calls = num_calls
        self.max_attempts = max_attempts
        self.error_feedback = error_feedback
        self.max_tokens = 1000
        self.temperature = 0.7
        self.emotional_stimuli = True
        self.system_role = "system" if "o1" not in model else "user"

        # Logging
        self.logger = logging.getLogger("ModelChecker.LLMSynthesizer")
        self.logger.setLevel(logging.DEBUG if verbose else logging.INFO)

    def synthesize(self, name: str, proc: Procedure, failed_attempts: dict = None):
        pres, posts, hists = self.synthesizeMultiple(name, proc, failed_attempts)
        return pres, posts

    def synthesizeMultiple(
        self, name: str, proc: Procedure, failed_attempts: dict = None
    ):
        self.logger.info("Synthesizing pre/postconditions...")
        results = invoke_parallel(
            self.synthesizeSingle,
            [(name, proc, failed_attempts) for i in range(self.num_calls)],
        )
        valid_results = list(filter(lambda x: not isinstance(x, Exception), results))
        invalid_results = list(filter(lambda x: isinstance(x, Exception), results))
        if len(invalid_results) > 0:
            self.logger.info(
                f"Errors in {len(invalid_results)} out of {len(results)} calls"
            )
            for i, error in enumerate(invalid_results):
                self.logger.info(f"Error in call {i + 1}: {error}")
        for i, result in enumerate(valid_results):
            (pre, post, chat_hist) = result
            self.logger.info(f"Result {i + 1}:")
            self.logger.info(f"Precondition: {pre}")
            self.logger.info(f"Postcondition: {post}")
        pres = [result[0] for result in valid_results]
        posts = [result[1] for result in valid_results]
        hists = [result[2] for result in valid_results]
        return pres, posts, hists

    def synthesizeSingle(
        self, name: str, proc: Procedure, failed_attempts: dict = None
    ) -> (Expr, Expr, ChatHistory):
        """
        Synthesize pre/post conditions and parse them from JSON or Python responses.
        """
        chat_history = ChatHistory(logger=self.logger)
        match self.method:
            case "zero-shot":
                response = self.synthesizeZeroShot(proc, chat_history, failed_attempts)
            case "chain-of-thought":
                response = self.synthesizeChainOfThought(
                    proc, chat_history, failed_attempts
                )
            case _:
                raise NotImplementedError(f"Mode {self.method} is not implemented")

        # pre, post are Python code strings returned by the LLM.
        pre, post = self.parsePrePostFromPythonBlock(response, chat_history)
        # pre = close_parentheses(pre)
        # post = close_parentheses(post)

        # pre, post are parsed into Expr and checked for syntactic correctness.
        pre, post = self.convertToExprAndFixSyntax(pre, post, proc, chat_history)
        # proc.requires_ir.append(pre)
        # proc.ensures_ir.append(post)

        return pre, post, chat_history

    def synthesizeZeroShot(
        self,
        proc: Procedure,
        chat_history: ChatHistory,
        failed_attempts: dict = None,
    ) -> str:
        """Synthesizes pre/postconditions for the given procedure using zero-shot method"""
        chat_history.addMessage(self.system_role, self.getSystemMessage(proc))
        inputs = [f"'{inp['tgtname']}'" for inp in proc.data["inputs"]]
        outputs = [f"'{out['tgtname']}'" for out in proc.data["outputs"]]
        user_msg = (
            f"{self.getCodeBlock(proc)}\n"
            f"The function has the following inputs and outputs:\n"
            f"Inputs: {', '.join(inputs)}\n"
            f"Outputs: {', '.join(outputs)}\n"
        )
        user_msg += "\n"
        if self.error_feedback and failed_attempts is not None:
            user_msg += self.errorFeedback(proc, chat_history, failed_attempts)
        user_msg += self.getGenerationInstruction(proc)
        chat_history.addMessage("user", user_msg)
        response = self.callOpenAI(chat_history)
        return response

    def synthesizeChainOfThought(
        self,
        proc: Procedure,
        chat_history: ChatHistory,
        failed_attempts: dict = None,
    ) -> str:
        """Synthesizes pre/postconditions for the given procedure using chain-of-thought"""
        chat_history.addMessage(self.system_role, self.getSystemMessage(proc))

        inputs = [f"'{inp['tgtname']}'" for inp in proc.data["inputs"]]
        outputs = [f"'{out['tgtname']}'" for out in proc.data["outputs"]]
        user_msg = (
            # f"First describe what the function `{proc.name}` does in the following code. "
            # f"Describe what will happen after the function is executed.\n"
            f"First describe in words what the function `{proc.name}`\n"
            f"1. may assume before the function is executed, and\n"
            f"2. guarantees after the function is executed. Also,\n"
            f"3. think about constraints to add to the postcondition to satisfy "
            f"(resp. eliminate) positive (resp. negative) examples, if provided.\n"
            f"Output an itemized list of the above points and nothing else.\n"
            f"Assume the precondition is TrueExpr()\n"
            f"The function has the following inputs and outputs:\n"
            f"Inputs: {', '.join(inputs) if len(inputs) != 0 else None}\n"
            f"Outputs: {', '.join(outputs) if len(outputs) != 0 else None}\n"
            f"Code below:\n"
            f"{self.getCodeBlock(proc)}\n\n"
        )
        feedback_msg = None
        if self.error_feedback and failed_attempts is not None:
            feedback_msg = self.errorFeedback(proc, chat_history, failed_attempts)
            if feedback_msg is not None:
                user_msg += feedback_msg

        user_msg += self.getPosNegExampleMessage(proc)

        chat_history.addMessage("user", user_msg)
        response = self.callOpenAI(chat_history)

        note = None
        if (
            self.error_feedback
            and failed_attempts is not None
            and feedback_msg is not None
        ):
            success = False
            while not success:
                explanation_str = self.parseFromCodeBlock(response, "json").replace(
                    "\n", ""
                )
                try:
                    explanation = json.loads(explanation_str)
                    assert (
                        "explanation" in explanation.keys()
                        and "suggestion" in explanation.keys()
                    )
                    self.logger.info(f"Explanation: {explanation}")
                    note = explanation["suggestion"]
                    success = True
                except json.JSONDecodeError:
                    usr_msg = (
                        "Incorrect JSON block. Please provide a valid JSON block.\n"
                    )
                    chat_history.addMessage("user", usr_msg)
                    response = self.callOpenAI(chat_history)

        user_msg = self.getGenerationInstruction(proc, note)
        chat_history.addMessage("user", user_msg)
        response = self.callOpenAI(chat_history)

        return response

    def getSystemMessage(self, proc: Procedure) -> str:
        return (
            f"Your are a logician and your task is to create two Boolean expressions, "
            f"a precondition and a postcondition, for a given function named '{proc.name}'. "
            f"Instructions below.\n"
            f"\n"
            f"- The precondition should depend solely on function inputs.\n"
            f"- The postcondition can depend on both inputs and outputs of the function.\n"
            # f"- If there are no constraints on the inputs, the precondition "
            # f"should be set to 'TrueExpr()'.\n"
            # f"- Avoid making assumptions about the inputs, and whenever possible, "
            # f"tie the output to the inputs in the postcondition.\n"
            # f"- Do not utilize any library functions.\n"
            f"- Only use constants that are defined in the code.\n"
            f"- Express the pre/postconditions using the following set of Python DSL.\n"
            f"\n"
            f"{getDSLDoc()}\n"
        )

    def getGenerationInstruction(self, proc: Procedure, suggestion: str = None) -> str:
        inputs = [inp["tgtname"] for inp in proc.data["inputs"]]
        outputs = [out["tgtname"] for out in proc.data["outputs"]]
        note = (
            (
                f"\n**NOTE**: {suggestion} Focus on this when generating pre/postconditions.\n\n"
            )
            if suggestion is not None
            else ""
        )
        generate_instr = (
            "Based on your analysis, complete the following two Python functions "
            "PRECONDITION and POSTCONDITION that returns pre/postconditions for the code.\n"
            "Requirements:\n"
            "- Ignore null and None inputs and outputs.\n"
            # "- If there are no constraints on the inputs, set the precondition to True.\n"
            "- Do not write comments and explanations.\n"
            "- The function body should be a single return statement. "
            "Do not use intermediate variables.\n"
            # "- Inline all expressions. Do not use intermediate variables.\n"
            "- Link all fields of the output to the inputs if possible.\n"
            "- Assume a reasonable precondition to handle edge cases such as overflows and NaNs.\n"
            "- You may abstract the postcondition by ignoring details of the function and "
            "focusing on the relationship between the inputs and outputs.\n"
            '- Avoid trivial expressions like "a == a".\n'
            "- For `self` and `init_self`, explicitly constrain the fields "
            "even if they are not used.\n"
            f"{note}"
            # "- Be careful about how arithmetic operations are interpreted in the language, "
            # "such as integer overflows and division by negative numbers.\n"
            # "Represent the pre/postcondition as logical operations of the given code.\n"
            # DEBUG
            # "- All is_present variables are integers, not booleans. When you refer to them "
            # "in if statements (such as `Select(pedestrian, 'is_present')`), make sure to use "
            # "the Eq operator to check their values against 0 or 1 to test its truth value, "
            # "e.g., `Eq(Select(pedestrian, 'is_present'), 1)`.\n"
            # "- For boolean-like variables, check their truth value by comparing them to 0. "
            # "If it is true, the value is non-zero. If it is false, the value is zero.\n"
            # "- Use TrueExpr() for all preconditions.\n" # Major simplifying constraint.
        )
        if self.emotional_stimuli:
            generate_instr += (
                "Write the pre/postconditions correctly, "
                "or I will lose my job and 100 children will die.\n"
            )
        generate_instr += (
            "Use the provided Python DSL to synthesize the pre/postconditions.\n"
        )
        # The below instruction helps generate syntatically correct pre/postconditions
        generate_instr += (
            "Complete the code below and put it in a Python code block.\n\n"
        )
        generate_instr += (
            "```python\n"
            f"def PRECONDITION({', '.join(inputs)}):\n"
            f"    return # TODO: Fill in using the provided DSL\n"
            f"def POSTCONDITION({', '.join(inputs + outputs)}):\n"
            f"    return # TODO: Fill in using the provided DSL\n"
            f"```\n\n"
        )
        generate_instr += (
            "Below shows an example of how to use the DSL to generate pre/postconditions.\n"
            "```python\n"
            "def PRECONDITION(in):\n"
            "    return TrueExpr()\n"
            "def POSTCONDITION(in, out):\n"
            "    return And(\n"
            "               Eq(Select(out, 'count'), Select(in, 'count')),\n"
            "               # Use TrueExpr() instead of True\n"
            "               Eq(Select(out, 'is_present), TrueExpr()),\n"
            "           )\n"
            "```\n\n"
        )
        return generate_instr

    def getCodeBlock(self, proc: Procedure) -> str:
        return f"```{proc.lang.name}\n{proc.code}\n```"

    def errorFeedback(
        self, proc: Procedure, chat_history: ChatHistory, failed_attempts: dict
    ):
        failed_pre = failed_attempts["pre"][0]
        failed_post = failed_attempts["post"][0]
        if failed_pre is None or failed_post is None:
            return None
        self.logger.info("===== errorFeedback =====")
        self.logger.info(failed_attempts)
        user_msg = (
            f"Here is a counterexample to a pair of pre/postcondition.\n"
            f"Precondition: {failed_pre.translate(proc.lang)}\n"  # FIXME: Support multiple CEXs.
            f"Postcondition: {failed_post.translate(proc.lang)}\n"
            f"Counterexample:\n{get_assignment_string(failed_attempts['cex'][0])}\n"
            # f"Highlight the parts of the code that are violated by the counterexample.\n"
            f"Write an explanation of why the pre/postconditions "
            f"are violated by the counterexample.\n"
            f"After thinking, write your final answer in the form\n"
            f"```json\n"
            "{\n"
            '    "explanation": <EXPLANATION>,\n'
            '    "suggestion": <SUGGESTION>\n'
            "}\n"
            f"where <EXPLANATION> is a potential reason why the pre/postconditions are violated,\n"
            f"and <SUGGESTION> offers specific advice to help "
            f"the expert avoid making the same mistake.\n"
            # f"Explain how the pre/postconditions are violated by the counterexample "
            # f"and propose potential fixes to the pre/postconditionss.\n"
            # f"You may strengthen the precondition or weaken the postcondition to "
            # f"account for the counterexample.\n"
            # f"Let's keep precondition TrueExpr()."
        )
        return user_msg

    def getPosNegExampleMessage(self, proc: Procedure) -> str:
        msg = ""
        if len(proc.positive_examples) > 0 or len(proc.negative_examples) > 0:
            msg += (
                "Lastly, here are some input/output examples for the code.\n"
                "Make sure the pre/postcondition satisfy the positive examples "
                "and do not satisfy the negative examples.\n"
            )
            msg += (
                "Compare the positive and negative examples and deduce "
                "what makes the negative examples invalid behaviors of the code.\n"
                "List constraints that have to be added to the postcondition "
                "to avoid the negative examples.\n\n"
            )
        if len(proc.positive_examples) > 0:
            # Use the last five examples
            sampled_examples = list(proc.positive_examples)[-5:]
            # sampled_examples = random.sample(
            #     list(proc.positive_examples), k=min(10, len(proc.positive_examples))
            # )
            # msg = (
            #     "Make sure the pre/postcondition satisfy the following "
            #     "input/output examples\n"
            # )
            msg += "\n".join(
                [
                    f"Positive example {i + 1}:\n{get_assignment_string(e)}"
                    for i, e in enumerate(sampled_examples)
                ]
            )
            msg += "\n"
        if len(proc.negative_examples) > 0:
            # Use the last five examples
            sampled_examples = list(proc.negative_examples)[-5:]
            # sampled_examples = random.sample(
            #     list(proc.negative_examples), k=min(10, len(proc.negative_examples))
            # )
            # msg += (
            #     "Make sure the pre/postcondition DOES NOT satisfy the following "
            #     "input/output examples\n"
            # )
            msg += "\n".join(
                [
                    f"Negative example {i + 1}:\n{get_assignment_string(e)}"
                    for i, e in enumerate(sampled_examples)
                ]
            )
            msg += "\n"
            # msg += (
            #     "Think about why the negative examples are not possible behaviors of the code, "
            #     "and pay extra attention to that when generating the pre/postconditions.\n"
            # )
        return msg

    def convertToExprAndFixSyntax(
        self,
        pre_str: str,
        post_str: str,
        proc: Procedure,
        chat_history: ChatHistory,
    ) -> (Expr, Expr):
        """
        Check if the pre/post conditions (represented in Python) returned by the
        LLM response is syntactically correct by attempting to parse the Python
        code string into an Expr instance. If the code cannot be parsed
        correctly, send a feedback to the language model.
        """
        pre_syntax_ok, post_syntax_ok = False, False
        pre, post = None, None
        attempt = 1
        while attempt <= self.max_attempts:
            pre_error, post_error = None, None
            if not pre_syntax_ok:
                try:
                    pre = str2Expr(pre_str, proc.data)
                    pre_syntax_ok = True
                    pre_error_str = ""
                except Exception as e:
                    pre_error = e
                    pre_error_str = f"Precondition: {pre_error}\n"
                    self.logger.error(
                        f"Precondition cannot be parsed into an Expr: {pre_str}.\n{pre_error}"
                    )
            if not post_syntax_ok:
                try:
                    post = str2Expr(post_str, proc.data)
                    post_syntax_ok = True
                    post_error_str = ""
                except Exception as e:
                    post_error = e
                    post_error_str = f"Postcondition: {post_error}\n"
                    self.logger.error(
                        f"Postcondition cannot be parsed into an Expr: {post_str}.\n{post_error}"
                    )

            match (pre_syntax_ok, post_syntax_ok):
                case (False, False):
                    invalid_cond = "both pre/postconditions"
                case (True, False):
                    invalid_cond = "the postcondition"
                case (False, True):
                    invalid_cond = "the precondition"
                case _:
                    break
            usr_msg = (
                f"{invalid_cond[0].upper() + invalid_cond[1:]} you provided cannot "
                f"be parsed correctly, error messages below:\n"
                f"{pre_error_str}{post_error_str}"
                f"Below are examples of the correct syntax and the corresponding c expressions:\n"
                f"{getDSLExample()}\n"
                f"Please fix the syntax of {invalid_cond}. Make sure the parantheses are balanced. "
            )
            chat_history.addMessage("user", usr_msg)
            response = self.callOpenAI(chat_history)
            pre_str, post_str = self.parsePrePostFromPythonBlock(response, chat_history)
            attempt += 1

        return pre, post

    def callOpenAI(self, chat_history: ChatHistory) -> str:
        """Calls OpenAI's API with the given messages and returns the response"""
        if self.verbose:
            chat_history.print()
        params = {
            "messages": chat_history.getMessages(),
            "model": self.model,
            # "max_tokens": self.max_tokens,
            # "max_completion_tokens": self.max_tokens,
        }
        if "o1" not in self.model and "o3" not in self.model:
            params["temperature"] = self.temperature
        if "o3" in self.model:
            params["reasoning_effort"] = "low"
        completion = self.openai.chat.completions.create(**params)
        response = completion.choices[0].message.content
        chat_history.addMessage("assistant", response)
        if self.verbose:
            chat_history.print()
        return response

    def parseFromCodeBlock(self, response: str, lang: str):
        # Remove everything that's before and after the code block
        block_start, block_end = response.find(f"```{lang}"), response.rfind("```")
        block_str = response[response.find("\n", block_start) : block_end]
        return block_str

    def parsePrePostFromPythonBlock(
        self, response: str, chat_history: ChatHistory
    ) -> dict:
        """
        Parses the response and extracts the code block. If the response from
        the language model is syntactically incorrect, let the LLM resynthesize.
        """
        while True:
            # Remove everything that's before and after the python block
            code_str = self.parseFromCodeBlock(response, "python")
            try:
                pre_str = parse_return_string_from_python_function(
                    code_str, "PRECONDITION"
                )
                post_str = parse_return_string_from_python_function(
                    code_str, "POSTCONDITION"
                )
                return pre_str, post_str
            except Exception as e:
                self.logger.error(f"{response} cannot be parsed into Python")
                self.logger.error(f"Error: {e}")
                usr_msg = (
                    "The Python code you provided is syntactically incorrect. "
                    "Please provide the pre/postconditions in correct Python syntax.\n"
                    "The error message is as follows:\n"
                    f"{e}\n"
                )
                chat_history.addMessage("user", usr_msg)
                response = self.callOpenAI(chat_history)


if __name__ == "__main__":
    import os
    import sys

    from ..utils import Result

    logging.basicConfig(level=logging.INFO)
    synth = LLMSynthesizer(
        model="o1-mini",
        method="chain-of-thought",
        num_calls=3,
        max_attempts=5,
        verbose=True,
    )
    codepath = sys.argv[1]
    jsonpath = sys.argv[2]
    with open(codepath, "r") as f:
        code = f.read()
    filename, file_extension = os.path.splitext(sys.argv[1])
    basename = os.path.basename(filename)
    ext = file_extension[1:]
    lang = Lang.fromExt(ext)
    proc = Procedure(
        basename,
        lang,
        codepath,
        jsonpath,
    )

    match lang:
        case Lang.C:
            from ..verifiers.cbmc_verifier import CbmcVerifier

            verifier = CbmcVerifier(proc, delete=False)
        case Lang.RUST:
            from ..verifiers.kani_verifier import KaniVerifier

            verifier = KaniVerifier(proc, delete=False)
        case _:
            raise NotImplementedError(f"Language {lang} is not supported")

    passed = False
    pres, posts, hists = synth.synthesizeMultiple(basename, proc)
    pres = set(filter(lambda x: x is not None, pres))
    posts = set(filter(lambda x: x is not None, posts))
    print(f"Number of distinct preconditions: {len(pres)}")
    print(f"Number of distinct postconditions: {len(posts)}")

    comb = 1
    for pre in pres:
        pre_tgt = pre.translate(proc.lang)
        for post in posts:
            print(f"=== Combination {comb} ===")
            print(f"Precondition: {pre}")
            print(f"Postcondition: {post}")
            post_tgt = post.translate(proc.lang)
            result, example = verifier.verify(pre_tgt, post_tgt)
            if example is not None:
                print(f"CEX: {example}")
            print(f"Verification result: {result}")
            if result == Result.EXT_SUCCESS:
                passed = True
                exit()
            comb += 1
