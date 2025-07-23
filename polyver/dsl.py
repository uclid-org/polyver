from .utils import Lang


class Expr:
    """
    Base class for expressions.
    """

    srcType = None
    srcName = None
    destType = None
    destName = None

    def __init__(self, *args, suffix=""):
        assert len(args) == 1, f"Expr requires 1 argument, {len(args)} given"
        self.args = list(args)

    # __repr__: Unambiguous, for developers, debugging.
    def __repr__(self):

        return self.translate(Lang.API)

    # __str__: Readable, for end-users, informal.
    # Use the UCLID5 translation as the user-friendly, readable representation.
    def __str__(self):
        return f"{self.translate(Lang.UCLID5)}"

    def __lt__(self, other):
        match (isinstance(self, Expr), isinstance(other, Expr)):
            case (True, False):
                return False
            case (False, True):
                return True
            case (True, True):
                if str(other).isdigit() and not str(self).isdigit():
                    return True
                if str(self).isdigit() and not str(other).isdigit():
                    return False
                return str(self) < str(other)
            case (False, False):
                return str(self) < str(other)

    def __eq__(self, other):
        return str(self) == str(other)

    def __hash__(self):
        return hash(str(self))

    def translate(self, lang: Lang):
        match lang:
            case Lang.API | Lang.C | Lang.RUST:
                if not self.srcName:
                    return str(self.args[0])
                return str(self.srcName)

            case Lang.UCLID5:
                if not self.destName:
                    return str(self.args[0])
                return str(self.destName)


class TrueExpr(Expr):
    """
    Represents the constant true expression.
    Example: TrueExpr() represents 'true'
    # Constant true expression
    def TrueExpr(): return true
    """

    def __init__(self):
        self.args = []
        self.srcType = "bool"
        self.destType = "boolean"

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return "true"
            case Lang.API:
                return "TrueExpr()"


class FalseExpr(Expr):
    """
    Represents the constant false expression.
    Example: FalseExpr() represents 'false'
    # Constant false expression
    def FalseExpr(): return false
    """

    def __init__(self):
        self.args = []
        self.srcType = "bool"
        self.destType = "boolean"

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return "false"
            case Lang.API:
                return "FalseExpr()"


class And(Expr):
    """
    Represents a logical AND operation.
    Example: And('a', 'b', 'c') represents 'a and b and c'
    # Logical AND operation
    def And(*args): return all(*args)
    """

    def __init__(self, *args):
        self.args = sorted(
            [arg if isinstance(arg, Expr) else Expr(arg) for arg in args]
        )

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return "(" + " && ".join(a.translate(lang) for a in self.args) + ")"
            case Lang.API:
                return f"And({', '.join(a.translate(lang) for a in self.args)})"


class Or(Expr):
    """
    Represents a logical OR operation.
    Example: Or('a', 'b', 'c') represents 'a or b or c'
    # Logical OR operation
    def Or(*args): return any(*args)
    """

    def __init__(self, *args):
        self.args = sorted([a if isinstance(a, Expr) else Expr(a) for a in args])

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return "(" + " || ".join(a.translate(lang) for a in self.args) + ")"
            case Lang.API:
                return f"Or({', '.join(a.translate(lang) for a in self.args)})"


class Not(Expr):
    """
    Represents a logical NOT operation.
    Example: Not('a') represents 'not a'
    # Logical NOT operation
    def Not(a): return not a
    """

    def __init__(self, *args):
        assert len(args) == 1, f"Not requires 1 argument, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return f"(!{self.args[0].translate(lang)})"
            case Lang.API:
                return f"Not({self.args[0].translate(lang)})"


class Eq(Expr):
    """
    Represents an equality comparison.
    Example: Eq('a', 'b') represents 'a == b'
    # Equality comparison
    def Eq(a, b): return a == b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Eq requires 2 arguments, {len(args)} given"
        self.args = sorted([a if isinstance(a, Expr) else Expr(a) for a in args])

    def translate(self, lang: Lang):
        arg0 = self.args[0].translate(lang)
        arg1 = self.args[1].translate(lang)
        precision = 0.0001
        match lang:
            case Lang.C | Lang.RUST:
                if any(arg.srcType == "float" for arg in self.args):
                    return (
                        f"(({arg0}) - ({arg1}) <= {precision} && "
                        f"({arg1}) - ({arg0}) <= {precision})"
                    )
                return f"({arg0} == {arg1})"
            case Lang.UCLID5:
                if any(arg.srcType == "float" for arg in self.args):
                    return (
                        f"(({arg0}) - ({arg1}) <= {precision}single && "
                        f"({arg1}) - ({arg0}) <= {precision}single)"
                    )
                return f"({arg0} == {arg1})"
            case Lang.API:
                return f"Eq({arg0}, {arg1})"


class Ne(Expr):
    """
    Represents an inequality comparison.
    Example: Ne('a', 'b') represents 'a != b'
    # Inequality comparison
    def Ne(a, b): return a != b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Ne requires 2 arguments, {len(args)} given"
        self.args = sorted([a if isinstance(a, Expr) else Expr(a) for a in args])

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return f"({self.args[0].translate(lang)} != {self.args[1].translate(lang)})"
            case Lang.API:
                return f"Ne({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


def has_unsigned_type(typ: str) -> bool:
    return typ is not None and ("unsigned" in typ or "uint" in typ)


class Lt(Expr):
    """
    Represents a less-than comparison.
    Example: Lt('a', 'b') represents 'a < b'
    # Less-than comparison
    def Lt(a, b): return a < b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Lt requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} < {self.args[1].translate(lang)})"
                )
            case Lang.UCLID5:
                assert self.args[0].srcType == self.args[1].srcType
                op = "<_u" if has_unsigned_type(self.args[0].srcType) else "<"
                return f"({self.args[0].translate(lang)} {op} {self.args[1].translate(lang)})"
            case Lang.API:
                return f"Lt({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Gt(Expr):
    """
    Represents a greater-than comparison.
    Example: Gt('a', 'b') represents 'a > b'
    # Greater-than comparison
    def Gt(a, b): return a > b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Gt requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} > {self.args[1].translate(lang)})"
                )
            case Lang.UCLID5:
                assert self.args[0].srcType == self.args[1].srcType
                op = ">_u" if has_unsigned_type(self.args[0].srcType) else ">"
                return f"({self.args[0].translate(lang)} {op} {self.args[1].translate(lang)})"
            case Lang.API:
                return f"Gt({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Le(Expr):
    """
    Represents a less-than-or-equal comparison.
    Example: Le('a', 'b') represents 'a <= b'
    # Less-than-or-equal comparison
    def Le(a, b): return a <= b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Le requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.C | Lang.RUST:
                return f"({self.args[0].translate(lang)} <= {self.args[1].translate(lang)})"
            case Lang.UCLID5:
                assert self.args[0].srcType == self.args[1].srcType
                op = "<=_u" if has_unsigned_type(self.args[0].srcType) else "<="
                return f"({self.args[0].translate(lang)} {op} {self.args[1].translate(lang)})"
            case Lang.API:
                return f"Le({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Ge(Expr):
    """
    Represents a greater-than-or-equal comparison.
    Example: Ge('a', 'b') represents 'a >= b'
    # Greater-than-or-equal comparison
    def Ge(a, b): return a >= b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Ge requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.C | Lang.RUST:
                return f"({self.args[0].translate(lang)} >= {self.args[1].translate(lang)})"
            case Lang.UCLID5:
                assert self.args[0].srcType == self.args[1].srcType
                op = ">=_u" if has_unsigned_type(self.args[0].srcType) else ">="
                return f"({self.args[0].translate(lang)} {op} {self.args[1].translate(lang)})"
            case Lang.API:
                return f"Ge({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Add(Expr):
    """
    Represents an addition operation.
    Example: Add('a', 'b') represents 'a + b'
    # Addition operation
    def Add(a, b): return a + b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Add requires 2 arguments, {len(args)} given"
        self.args = sorted([a if isinstance(a, Expr) else Expr(a) for a in args])

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} + {self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Add({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Sub(Expr):
    """
    Represents a subtraction operation.
    Example: Sub('a', 'b') represents 'a - b'
    # Subtraction operation
    def Sub(a, b): return a - b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Sub requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} - {self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Sub({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Mul(Expr):
    """
    Represents a multiplication operation.
    Example: Mul('a', 'b') represents 'a * b'
    # Multiplication operation
    def Mul(a, b): return a * b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Mul requires 2 arguments, {len(args)} given"
        self.args = sorted([a if isinstance(a, Expr) else Expr(a) for a in args])

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} * {self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Mul({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Div(Expr):
    """
    Represents a division operation.
    Example: Div('a', 'b') represents 'a / b'
    # Division operation
    def Div(a, b): return a / b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Div requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} / {self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Div({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Mod(Expr):
    """
    Represents a modulo operation.
    Example: Mod('a', 'b') represents 'a % b'
    # Modulo operation
    def Mod(a, b): return a % b
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Mod requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.UCLID5 | Lang.C | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)} % {self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Mod({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class Select(Expr):
    """
    Represents a selection operation.
    Example: Select('a', 'b') represents 'a.b'
    # Selection operation (a.b or a->b)
    def Select(a, b): return getattr(a, b)
    """

    def __init__(self, *args):
        assert len(args) == 2, f"Select requires 2 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        match lang:
            case Lang.C:
                pointer = "*" in self.args[0].srcType
                return (
                    f"({self.args[0].translate(lang)}"
                    f"{'->' if pointer else '.'}"
                    f"{self.args[1].translate(lang)})"
                )
            case Lang.UCLID5 | Lang.RUST:
                return (
                    f"({self.args[0].translate(lang)}.{self.args[1].translate(lang)})"
                )
            case Lang.API:
                return f"Select({self.args[0].translate(lang)}, {self.args[1].translate(lang)})"


class IfThenElse(Expr):
    """
    Represents a conditional expression.
    Example: IfThenElse('a', 'b', 'c') represents 'if a then b else c'
    # Conditional expression
    def IfThenElse(a, b, c): return b if a else c
    """

    def __init__(self, *args):
        assert len(args) == 3, f"IfThenElse requires 3 arguments, {len(args)} given"
        self.args = [a if isinstance(a, Expr) else Expr(a) for a in args]

    def translate(self, lang: Lang):
        a = self.args[0].translate(lang)
        b = self.args[1].translate(lang)
        c = self.args[2].translate(lang)
        match lang:
            case Lang.UCLID5:
                return f"(if ({a}) then ({b}) else ({c}))"
            case Lang.C:
                return f"(({a}) ? ({b}) : ({c}))"
            case Lang.RUST:
                return f"if ({a}) {{ {b} }} else {{ {c} }}"
            case Lang.API:
                return f"IfThenElse({a}, {b}, {c})"


class Const(Expr):
    def __init__(self, sourceType=None, destType=None, value="0"):
        self.bits = -1
        self.srcType = sourceType
        self.destType = destType
        self.args = [Expr(value)]

    def translate(self, lang):
        match lang:
            case Lang.UCLID5:
                match self.destType:
                    case None:
                        suffix = ""
                    case x if "bv" in x or "single" in x:
                        suffix = x
                    case _:
                        suffix = ""
                return str(self.args[0].args[0]) + suffix
            case Lang.API | Lang.C | Lang.RUST:
                return str(self.args[0].args[0])


if __name__ == "__main__":
    # Example usage
    expr = IfThenElse(Select("x", "y", False), Add("z", "1"), Sub("z", "1"))
    print(expr.translate(Lang.API))  # IfThenElse(Select(x, y), Add(z, 1), Sub(z, 1))
    print(expr.translate(Lang.UCLID5))  # (x == y) && (z > 0)
    print(expr.translate(Lang.C))  # (x == y) && (z > 0)
