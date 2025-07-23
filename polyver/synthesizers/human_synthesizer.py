from smartinput import Fore, History, sinput

from ..dsl_parser import str2Expr
from ..procedure import Procedure
from ..synthesizer import Synthesizer


class HumanSynthesizer(Synthesizer):
    def __init__(self):
        self.prompt = "> "
        self.history = History()
        self.sys_clr = Fore.YELLOW
        self.usr_clr = Fore.CYAN

    def synthesize(self, name: str, proc: Procedure, failed_attempts: dict = None):
        print(self.sys_clr + "----------------------------")
        print("Use 'r' for function output")
        print(f"Procedure {name}:\n{proc.code}\n")
        print(
            "Positive examples:\n\t{}\n".format(
                "\n\t".join(str(e) for e in list(proc.positive_examples))
            )
        )
        print(
            "Negative examples:\n\t{}\n".format(
                "\n\t".join(str(e) for e in list(proc.negative_examples))
            )
        )
        print(self.sys_clr + f"Enter pre-condition for {name}:")
        pre = self.getExprFromInput(proc)
        print(self.sys_clr + f"Enter post-condition for {name}:")
        post = self.getExprFromInput(proc)
        print(self.sys_clr + "----------------------------\n" + Fore.RESET)
        return [pre], [post]

    def getExprFromInput(self, proc):
        success = False
        while not success:
            s = sinput(self.prompt, history=self.history, color=self.usr_clr)
            try:
                expr = str2Expr(s, proc.data)
                success = True
            except Exception as ex:
                print(f"Invalid input. An exception is raised: {ex}. Please try again.")
                continue

        return expr
