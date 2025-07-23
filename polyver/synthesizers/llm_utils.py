import ast
import importlib.util
import inspect
import os
from pathlib import Path

import astor
from colorama import Fore


class ChatHistory:
    def __init__(self, logger):
        self.logger = logger
        self.messages = []
        self.printed = []
        self.usr_msg_print_len = None  # Used to truncate output messages if too long.

    def addMessage(self, role, content):
        self.messages.append({"role": role, "content": content})
        self.printed.append(False)

    def print(self):
        for i, msg in enumerate(self.messages):
            if self.printed[i]:
                continue
            role, content = msg["role"], msg["content"]
            color = Fore.CYAN if role == "assistant" else Fore.YELLOW
            content = (
                content[: self.usr_msg_print_len] + "\n..."
                if role != "assistant"
                else content
            )
            self.logger.info(
                color + f"======== {role.upper()} ========\n{content}" + Fore.RESET
            )
            self.printed[i] = True

    def getMessages(self):
        return self.messages

    def clear(self):
        self.messages = []
        self.printed = []

    def __str__(self):
        return "\n".join([f"{msg['role']}:\n{msg['content']}" for msg in self.messages])


def getClassDocstrings(file_path):
    class_docstrings = {}

    # Get the directory path and module name from the file path
    directory, module_name = os.path.split(file_path)
    # Get package name (for relative import)
    package_name = os.path.basename(directory)
    # Remove extension
    module_name = os.path.splitext(module_name)[0]
    # Combine module name and file basename
    module_name = package_name + "." + module_name

    # Load the module
    spec = importlib.util.spec_from_file_location(module_name, file_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    # Iterate through the objects in the module
    for name, obj in inspect.getmembers(module):
        # Check if the object is a class
        if inspect.isclass(obj):
            # Get the docstring of the class
            class_docstrings[name] = inspect.getdoc(obj)

    return class_docstrings


def getDSLExample():
    examples = """Example usages:
IfThenElse( Lt(Select('x', 'y'), '3'), Add('z', '1'), Sub('z', '1') ) ==> (x.y < 3 ? z + 1 : z - 1)
And( Eq(Select('x', 'y'), '3'), Or(Eq('z', '1'), Eq('z', '2')) ) ==> (x->y == 3 && z == 1 or z == 2)
"""
    return examples


def getDSLDoc():
    file_path = Path(__file__).parent.parent / "dsl.py"
    class_docstrings = getClassDocstrings(file_path)
    ret = "\n".join(
        [
            # f"Class {class_name}:\n{docstring.split('\n')[-1]}\n"
            "\n".join(docstring.split("\n")[-2:]) + "\n"
            for class_name, docstring in class_docstrings.items()
            if class_name not in ["Expr", "Lang", "Enum"]
        ]
    )
    return ret


def get_assignment_string(ex):
    ret = ""
    inputs = ex[0]
    outputs = ex[1]
    for inp in inputs:
        ret += f"{inp[0]} = {inp[1]}\n"
    for out in outputs:
        ret += f"{out[0]} = {out[1]}\n"
    return ret


def parse_return_string_from_python_function(code, function_name):
    # Parse the code into an AST
    tree = ast.parse(code)

    # Define a visitor class to traverse the AST and find
    # the function definition and its return value
    class FunctionReturnVisitor(ast.NodeVisitor):
        def __init__(self):
            self.return_value = None

        def visit_FunctionDef(self, node):
            if node.name == function_name:
                self.generic_visit(node)

        def visit_Return(self, node):
            if hasattr(node, "value"):
                self.return_value = node.value

    # Create an instance of the visitor class
    visitor = FunctionReturnVisitor()

    # Traverse the AST
    visitor.visit(tree)

    # Convert the AST node to a Python code string
    if visitor.return_value is not None:
        return astor.to_source(visitor.return_value).strip()
    else:
        return None


if __name__ == "__main__":
    print(getDSLDoc())
