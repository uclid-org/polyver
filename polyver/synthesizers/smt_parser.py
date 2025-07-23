import re

from lark import Lark, Transformer

# Define the grammar
smt_grammar = r"""
    ?start: define_fun -> start

    ?define_fun: "(" define_fun ")"
        | "(" "define-fun" SYMBOL "(" params ")" type expr ")" -> define_fun

    ?params: (param)*
    param: "(" variable type ")"
    type: "Bool" | "Int" | "(" "_" "BitVec" NUMBER ")"

    ?expr: atom
        | "(" operator expr+ ")" -> operation
        | "(" let expr ")"
        | "(" expr ")"

    ?atom: "(" atom ")"
        | variable
        | number
        | bv
        | bitstring

    ?let: "let" "(" let_binding+ ")" -> let

    ?let_binding: "(" variable expr ")" -> let_binding

    operator: OPERATOR -> operator

    variable: SYMBOL -> variable
    number: NUMBER -> number
    bv: "(" "_" "bv" NUMBER NUMBER ")" -> bv
    bitstring: "#" SYMBOL -> bitstring

    OPERATOR: "=" | "!=" | "ite" | "and" | "or" | "not"
        | "+" | "-" | "*" | "/" | "%" | "<" | "<=" | ">" | ">="
        | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "bvult" | "bvule" | "bvugt" | "bvuge"
        | "bvneg" | "bvadd" | "bvsub" | "bvmul" | "bvdiv" | "bvmod"
    SYMBOL: /[a-zA-Z_][a-zA-Z0-9_\->\.]*/
    NUMBER: /\d+(\.\d+)?/

    %ignore /\s+/
"""

# Create the parser
defineFunParser = Lark(smt_grammar, start="start")
SMTParser = Lark(smt_grammar, start=["start", "expr"])


# Transformer to process the parsed tree into an AST
class ASTTransformer(Transformer):
    def __init__(self):
        self.symbol_table = {}
        self.symbol_counter = 0

    def new_symbol(self):
        """Return a new symbol."""
        self.symbol_counter += 1
        return f"_x{self.symbol_counter}_"

    def number(self, items):
        """Return numbers as strings."""
        # symbol = self.new_symbol()
        # self.symbol_table[symbol] = items[0]
        # return symbol
        return str(items[0])

    def bv(self, items):
        """
        Return the value of bitvector as strings.
        E.g. (_ bv13 32) -> 13
        """
        return str(items[0])

    def bitstring(self, items):
        """
        Return the value of bitvector as strings.
        E.g. #b00000010 -> 2
        """
        base_str, bits = items[0][0], items[0][1:]  # Remove the prefix
        match base_str:
            case "b":
                base = 2
            case "o":
                base = 8
            case "x":
                base = 16
            case _:
                raise ValueError(f"Unknown base: {items[0]}")
        return str(int(bits, base))

    def variable(self, items):
        """Return variable names as strings."""
        # symbol = self.new_symbol()
        # self.symbol_table[symbol] = items[0]
        # return symbol
        return self.process_variable(str(items[0]))

    def operation(self, items):
        """Return operators as strings."""
        operator = items[0]
        operands = items[1:]
        match operator:
            case "+" | "bvadd":
                res = f"Add({', '.join(operands)})"
            case "-" | "bvsub" | "bvneg":
                if len(operands) == 1:
                    operands.insert(0, "0")
                res = f"Sub({', '.join(operands)})"
            case "*" | "bvmul":
                res = f"Mul({', '.join(operands)})"
            case "/" | "bvdiv":
                res = f"Div({', '.join(operands)})"
            case "%" | "bvmod":
                res = f"Mod({', '.join(operands)})"
            case "<" | "bvslt":
                res = f"Lt({', '.join(operands)})"
            case "<=" | "bvsle":
                res = f"Le({', '.join(operands)})"
            case ">" | "bvsgt":
                res = f"Gt({', '.join(operands)})"
            case ">=" | "bvsge":
                res = f"Ge({', '.join(operands)})"
            case "=":
                res = f"Eq({', '.join(operands)})"
            case "!=":
                res = f"Ne({', '.join(operands)})"
            case "ite":
                res = f"IfThenElse({', '.join(operands)})"
            case "and":
                res = f"And({', '.join(operands)})"
            case "or":
                res = f"Or({', '.join(operands)})"
            case "not":
                res = f"Not({', '.join(operands)})"
            case _:
                raise ValueError(f"Unknown operator: {operator}")
        return res

    def operator(self, items):
        """Return operators as strings."""
        return str(items[0])

    def let(self, items):
        """Return let expressions as lists."""
        return items

    def let_binding(self, items):
        """Return let pairs as lists."""
        return items

    def expr(self, items):
        """Return expressions as lists."""
        if len(items) == 1:
            return items[0]
        # Has let expression. Replace variables with values
        # FIXME: This is a hack. Need to find a better way to handle let expressions
        # Things may break if the variable names are substrings of each other
        assert len(items) == 2
        pairs = items[0]
        expr = items[1]
        for n, v in pairs:
            expr = expr.replace(n, v)
        return expr

    def define_fun(self, items):
        """Return the final expression."""
        return items[-1]

    def start(self, items):
        """Return the start symbol."""
        return items[0]

    def process_variable(self, name):
        """
        Recursively replace '->' and '.' with Select operator.
        Find the first occurence of '->' or '.' and replace it with Select operator.
        E.g. a.b->c -> Select(Select(a, b), c)
        """
        if name == "true":
            return "TrueExpr()"
        if name == "false":
            return "FalseExpr()"
        split = re.split(r"(->|\.)", name, 1)
        if len(split) == 1:
            return name
        assert len(split) == 3
        return f"Select({split[0]}, {self.process_variable(split[2])})"


if __name__ == "__main__":
    # Input Lisp-like code
    code = (
        "(define-fun f ((x Int)) Int "
        "(let ((_let_1 (- x)) (_let_2 x)) (ite (< x _let_1) (+ _let_1 _let_2) x)))"
    )
    # code = "(< (+ 1 2) 3)"
    code = (
        "(define-fun progSummary (( p0 Int)( p1 Int)( p2 Int)( p3 Int)) Bool "
        "(< init_self->_mode.aaa->bbb init_self->_mode))"
    )
    code = (
        "(define-fun f ((x Int)) (_ BitVec 32) "
        "(let ((_let_1 (bvneg x)) (_let_2 x)) (ite (bvslt x (_ bv13 32)) (bvadd _let_1 _let_2) x)))"
    )
    code = (
        "(define-fun progSummary ((i (_ BitVec 32)) (r (_ BitVec 32))) Bool "
        "(bvslt i (ite (bvslt i #b00000000000000000000000000000111) (bvsub i r) r)))"
    )

    # Parse and transform
    parsed_tree = defineFunParser.parse(code)
    print(code)
    print(parsed_tree.pretty())

    ast = ASTTransformer().transform(parsed_tree)
    print(ast)
