import ast
import json
import logging

from .dsl import *


def str2Expr(expr_str, data):
    expr = convert2Expr(expr_str)
    expr = type_expr(expr, data)
    typed, subtree = check_typed(expr)
    if not typed:
        logging.warning(f"WARNING: expression {expr_str} is not fully typed")
        logging.warning(f"Untyped subtree: {subtree}")
    return expr


# Returns True if the expression is fully typed, otherwise
# returns False and the first subtree that is fully untyped
def check_typed(expr):
    if not isinstance(expr, Expr):
        return False, expr
    if expr.srcType is not None or expr.destType is not None:
        return True, None
    has_children_untyped = False
    all_children_untyped = True
    ret_subtree = None
    for arg in expr.args:
        typed, subtree = check_typed(arg)
        if typed:
            all_children_untyped = False
        else:
            has_children_untyped = True
            ret_subtree = subtree
    if all_children_untyped:
        ret_subtree = expr
    return not has_children_untyped, ret_subtree


class BooleanExpressionParser(ast.NodeVisitor):
    def visit_Call(self, node):
        func_name = node.func.id
        args = [self.visit(arg) for arg in node.args]
        return {"func": func_name, "args": args}

    def visit_Name(self, node):
        return node.id

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant):
            return "-" + self.visit_Constant(node.operand)

    def visit_Constant(self, node):
        return str(node.n)


parser = BooleanExpressionParser()


def is_numeric(s):
    try:
        float(s)  # Try to convert the string to a float
        return True
    except ValueError:
        return False


def convert2Expr(expr_str):
    """
    Converts a string to a potentially untyped expression object.
    """
    tree = ast.parse(expr_str, mode="eval")

    # input: tree body
    tree = parser.visit(tree.body)
    # output: {'func': 'TrueExpr', 'args': []}

    def convert(node):
        """
        Responsible for converting a node into a string format?
        Node is usually a dictionary specifying the function name and arguments passed in
        """
        if isinstance(node, str):
            if is_numeric(node):
                return Const(None, None, node)
            else:
                return Expr(node)

        match node["func"]:
            case "Select":
                assert all(isinstance(arg, str) for arg in node["args"])
                return Select(*node["args"])
            case _:
                args = [convert(arg) for arg in node["args"]]
                return eval(node["func"])(*args)

    return convert(tree)


def pull_types_from_IO(var_name, config_dict):
    """
    To handle all the cases apart from Select, we use this function to
    pull the types which are stored in a combination of input and output
    """
    input_list = config_dict["inputs"] + config_dict["outputs"]
    for var_dict in input_list:
        if var_dict["tgtname"] == var_name:
            return (
                var_dict["tgtname"],
                var_dict["tgttype"],
                var_dict["uclname"],
                var_dict["ucltype"],
            )


def return_types_from_struct_name(struct_name, attr, config_dict):
    """
    Returns the type of the attribute in the struct from the config dictionary
    """
    # once we have the struct name, we can go and find the exact type of the attributes
    type_dict_list = config_dict["types"]
    type_attr_dict_list = type_dict_list[struct_name]["fields"]
    for field in type_attr_dict_list.keys():
        if field == attr:
            return (
                type_attr_dict_list[field]["tgttype"],
                type_attr_dict_list[field]["ucltype"],
            )
    return None


def pull_types(struct_name, attr, config_dict):
    """
    Pulls the types of the variables from the config file.

    Input:
        args_list : (List[str]) - This is a list of arguments that were based in.
    """

    struct_name = struct_name.split(" ")[0]
    # the second argument is the type
    # attr = args_list[1]
    return return_types_from_struct_name(struct_name, attr, config_dict)


def handleSelect(select_obj, config_dict):
    """
    Handles Select as an arg. We need to set each of Select's args as their respective types.
    Then we need Select to take on the value of the variable.
    """
    first_arg_expr_obj = select_obj.args[0]  # Expr object containing struct name
    sec_arg_expr_obj = select_obj.args[1]  # Expr object containing attr name
    assert isinstance(first_arg_expr_obj, Expr)
    assert isinstance(sec_arg_expr_obj, Expr)
    # We want to store the struct information in the first element of the struct.
    # This will tell us whether or not we have a pointer.
    (
        first_arg_expr_obj.srcName,
        first_arg_expr_obj.srcType,
        first_arg_expr_obj.destName,
        first_arg_expr_obj.destType,
    ) = pull_types_from_IO(first_arg_expr_obj.args[0], config_dict)
    # We want to store the actual type of the Select object
    # which is stored here in the second argument
    sec_arg_expr_obj.srcType, sec_arg_expr_obj.destType = pull_types(
        first_arg_expr_obj.srcType, sec_arg_expr_obj.args[0], config_dict
    )
    sec_arg_expr_obj.srcName, sec_arg_expr_obj.destName = (
        sec_arg_expr_obj.args[0],
        sec_arg_expr_obj.args[0],
    )
    # select object takes on the value of the attribute that we pull from the struct
    select_obj.srcType, select_obj.destType = (
        sec_arg_expr_obj.srcType,
        sec_arg_expr_obj.destType,
    )
    return select_obj


def checkConfig(select_obj, config_dict):
    """
    Earlier this used to just be for select but since any operator
    can pull from the config file, this is generalized
    """
    assert isinstance(
        select_obj, Expr
    ), "This function should only be called on Expr objects"
    first_arg_val = select_obj.args[0]  # Expr object containing struct name

    pulled_types = pull_types_from_IO(first_arg_val, config_dict)

    if pulled_types is not None:
        (
            select_obj.srcName,
            select_obj.srcType,
            select_obj.destName,
            select_obj.destType,
        ) = pulled_types
        return select_obj
    # else:
    #     return None
    return select_obj


def is_boolean_operator(expr_obj):
    """
    Returns if the operator is a boolean operator.
    """
    return type(expr_obj) in [And, Or, Not]


def is_arithmetic_operator(expr_obj):
    """
    Returns if the operator is an arithmetic operator.
    """
    return type(expr_obj) in [Add, Sub, Mod, Mul, Div]


def is_comparison_operator(expr_obj):
    """
    Returns if the operator is a comparison operator.
    """
    return type(expr_obj) in [Eq, Gt, Ne, Lt, Le, Ge]


def is_const(expr_obj):
    """
    Returns if the operator is a constant.
    """
    return type(expr_obj) in [Const, TrueExpr, FalseExpr]


def is_select(expr_obj):
    """
    Returns if the operator is a Select.
    """
    return isinstance(expr_obj, Select)


def is_expr(expr_obj):
    """
    Returns if the operator is an Expr.
    """
    return isinstance(expr_obj, Expr)


def is_ite(expr_obj):
    """
    Returns if the operator is an ITE.
    """
    return isinstance(expr_obj, IfThenElse)


# Return the original expression object but typed
def type_expr(expr_obj, config_dict):
    new_args = []
    if is_select(expr_obj):
        typed_arg = handleSelect(expr_obj, config_dict)
        return typed_arg
    elif is_boolean_operator(expr_obj):
        for arg in expr_obj.args:
            typed_arg = type_expr(arg, config_dict)
            new_args.append(typed_arg)
        expr_obj.args = new_args
        # srcType and destType will be set to bool if the subtree is typed
        if all(arg.srcType == "bool" and arg.destType == "boolean" for arg in new_args):
            expr_obj.srcType = "bool"
            expr_obj.destType = "boolean"
        # else:
        #     logging.warning("WARNING: subtree not fully typed")
        return expr_obj
    elif is_comparison_operator(expr_obj) or is_arithmetic_operator(expr_obj):
        # srcType and destType will be set to the type of the subtrees
        # if the subtrees are *fully* typed
        srcType, destType, new_args = find_type_and_assign_to_neighbors(
            expr_obj.args, config_dict
        )
        # Assign corresponding types to the expression object if all subtrees are typed
        if (
            srcType is not None
            and destType is not None
            and all(
                arg.srcType == srcType and arg.destType == destType for arg in new_args
            )
        ):
            # match type(expr_obj):
            if is_comparison_operator(expr_obj):
                expr_obj.srcType = "bool"
                expr_obj.destType = "boolean"
            elif is_arithmetic_operator(expr_obj):
                expr_obj.srcType = srcType
                expr_obj.destType = destType
            else:
                raise RuntimeError(f"Unknown type: {type(expr_obj)}")
        # else:
        #     logging.warning("WARNING: subtree not fully typed")
        return expr_obj
    elif is_ite(expr_obj):
        cond_expr = type_expr(expr_obj.args[0], config_dict)
        # srcType and destType will be set to the type of
        # then and else branches if they are *fully* typed
        srcType, destType, new_args = find_type_and_assign_to_neighbors(
            expr_obj.args[1:], config_dict
        )
        expr_obj.args = [cond_expr] + new_args
        # Assign corresponding types to the expression object if both branches are typed
        if (
            cond_expr.srcType == "bool"
            and cond_expr.destType == "boolean"
            and all(
                arg.srcType == srcType and arg.destType == destType for arg in new_args
            )
        ):
            expr_obj.srcType = srcType
            expr_obj.destType = destType
        # else:
        #     logging.warning("WARNING: subtree not fully typed")
        return expr_obj
    elif is_const(expr_obj):
        return expr_obj
    elif is_expr(expr_obj):
        typed_arg = checkConfig(expr_obj, config_dict)
        if typed_arg is None:
            raise RuntimeError("WARNING: ERROR IN CONFIG")
        return typed_arg
    else:
        raise RuntimeError(f"Unknown type: {type(expr_obj)}")


# Given a list of expression objects, check if each of them can be typed
# If one of them can, assign the type to the rest of the expression objects and their subtrees.
# Return the type if any of the expression objects can be typed, otherwise None.
# Also return the updated typed expression objects.
def find_type_and_assign_to_neighbors(args, config_dict):
    # First check if we can find the type of any child
    srcType = None
    destType = None
    intermediate_args = []
    new_args = []
    for arg in args:
        typed_arg = type_expr(arg, config_dict)
        intermediate_args.append(typed_arg)
        if srcType is None and destType is None:
            srcType = typed_arg.srcType
            destType = typed_arg.destType
        # Check if the types are compatible
        if typed_arg.srcType is not None and typed_arg.destType is not None:
            assert typed_arg.srcType == srcType and typed_arg.destType == destType, (
                f"Type mismatch: {typed_arg.translate(Lang.API)} has type "
                f"({typed_arg.srcType}, {typed_arg.destType}). Should be ({srcType}, {destType})"
            )
    # If there is an operand that is typed, propagate that type
    # to the rest of the operands and their subtrees
    if srcType is not None and destType is not None:
        # Propagate the types to its neighbors
        for arg in intermediate_args:
            if arg.srcType is None and arg.destType is None:
                typed_arg = assign_type_to_subtree(
                    arg, srcType, destType, config_dict
                )  # CHECK THIS
                new_args.append(typed_arg)
            else:
                assert arg.srcType == srcType and arg.destType == destType, (
                    f"Type mismatch: {arg.translate(Lang.API)} has type "
                    f"({arg.srcType}, {arg.destType}). Should be ({srcType}, {destType})"
                )
                new_args.append(arg)
    else:
        assert srcType is None and destType is None, "Types should be None"
        new_args = intermediate_args
    return srcType, destType, new_args


def assign_type_to_subtree(expr_obj, srcType, destType, config_dict):
    # If the expression object is already typed and has the same type, return it
    if expr_obj.srcType is not None and expr_obj.destType is not None:
        assert (
            expr_obj.srcType == srcType and expr_obj.destType == destType
        ), "Types should match"
        return expr_obj

    if is_const(expr_obj):
        expr_obj.srcType = srcType
        expr_obj.destType = destType
        if expr_obj.srcType == "bool" and expr_obj.destType == "boolean":
            assert expr_obj in [
                TrueExpr(),
                FalseExpr(),
            ], f"{expr_obj.translate(Lang.API)} should be a Boolean"
        return expr_obj
    elif is_arithmetic_operator(expr_obj):
        new_args = []
        for arg in expr_obj.args:
            typed_arg = assign_type_to_subtree(arg, srcType, destType, config_dict)
            new_args.append(typed_arg)
        if all(arg.srcType == srcType and arg.destType == destType for arg in new_args):
            expr_obj.srcType = srcType
            expr_obj.destType = destType
        # else:
        #     logging.warning("WARNING: subtree not fully typed")
        expr_obj.args = new_args
        return expr_obj
    elif is_ite(expr_obj):
        cond_expr = type_expr(expr_obj.args[0], config_dict)
        then_expr = assign_type_to_subtree(
            expr_obj.args[1], srcType, destType, config_dict
        )
        else_expr = assign_type_to_subtree(
            expr_obj.args[2], srcType, destType, config_dict
        )
        expr_obj.args = [cond_expr, then_expr, else_expr]
        # If the condition is typed and all branches are typed
        # and have the same type, assign the type to the ITE
        if (
            cond_expr.srcType == "bool"
            and cond_expr.destType == "boolean"
            and then_expr.srcType == srcType
            and then_expr.destType == destType
            and else_expr.srcType == srcType
            and else_expr.destType == destType
        ):
            expr_obj.srcType = srcType
            expr_obj.destType = destType
        # else:
        #     logging.warning("WARNING: subtree not fully typed")
        return expr_obj
    elif is_boolean_operator(expr_obj) or is_comparison_operator(expr_obj):
        assert False, "Should not happen"
    elif is_select(expr_obj):
        assert False, "Should not happen since types should have been set"
    elif is_expr(expr_obj):
        logging.warning(
            f"WARNING: {expr_obj} not typed, assigning {srcType} and {destType}"
        )
        expr_obj.srcType = srcType
        expr_obj.destType = destType
        return expr_obj
    else:
        raise RuntimeError(f"Unknown type: {type(expr_obj)}")


def pretty_print_json(expr):
    """Pretty print the Expr object as JSON."""
    if isinstance(expr, Const):
        return {
            "op": "Const",
            "srcType": expr.srcType,
            "dstType": expr.destType,
            "value": expr.args[0].args[
                0
            ],  # Const.args = [Expr(value)] -> Const.args[0].args = [value]
        }
    if isinstance(expr, str):
        return expr
    final_dict = {
        "op": expr.__class__.__name__,
        "srcName": expr.srcName,
        "srcType": expr.srcType,
        "dstName": expr.destName,
        "dstType": expr.destType,
        "args": [pretty_print_json(a) for a in expr.args],
    }
    return final_dict


if __name__ == "__main__":
    ped_expr = "And(Le(Select('pedestrian', 'is_present'), 1), Ge(Select('pedestrian', 'is_present'), 0),Ge(Select(init_self, _mode), 0), Ge(Select('init_self', 'count'), 0),Le(Select('init_self', '_mode'), 3),Le(Select('init_self', 'count'), 60))"
    simple_ped_expr = """Eq(Select(pedestrian,is_present), Add(2,1))"""
    step_expr = """And(IfThenElse(Eq(Select('src', 'm'),Select('dst', 'id')), Eq( Select('ret', 'win'), 1), Eq( Select('ret', 'win'), Select('dst', 'win'))), IfThenElse( Gt( Select('src', 'm'), Select('dst', 'id')), Eq( Select('ret', 'm'), Select('src', 'm')), Eq( Select('ret', 'm'), Select('dst', 'm'))), Eq( Select('ret', 'id'), Select('dst', 'id')))"""
    ite_expr = """IfThenElse(Eq(Select('src', 'm'),Select('dst', 'id')), Select('ret', 'win'), Select('dst', 'win'))"""
    arith_expr = """Eq(Add(Add(1,2), Add(3,4)), Select(ret,win))"""
    only_const_expr = """Eq(Add(1,2), Add(3,4))"""

    from pathlib import Path

    examples_dir = Path(__file__).parent.parent / "examples"
    traffic_light = examples_dir / "traffic_light" / "traffic_light_reaction_2.json"
    step = examples_dir / "leader_election" / "step.json"

    config = {
        "ped": [ped_expr, traffic_light],
        "simple_ped": [simple_ped_expr, traffic_light],
        "step": [step_expr, step],
        "ite": [ite_expr, step],
        "arith": [arith_expr, step],
        "only_const": [only_const_expr, step],
    }

    for i, (name, val) in enumerate(config.items()):
        ORIGINAL_EXPR = val[0]
        filename = val[1]

        with open(filename) as cf:
            data = json.load(cf)
        print(f"-------------- TEST {i} --------------")
        print(f"Testing: {name}")
        print("original expression: ", ORIGINAL_EXPR)
        expr_obj = convert2Expr(ORIGINAL_EXPR)
        pretty = pretty_print_json(expr_obj)
        orig_file = "original_expr.json"
        # with open(orig_file, "w") as f:
        #     f.write(json.dumps(pretty, indent=4))
        try:
            propogated_types = type_expr(expr_obj, data)
        except RuntimeError as e:
            print("ERROR: ", e)
            continue
        pretty = pretty_print_json(propogated_types)
        file = "pretty_print_final.json"
        # with open(file, "w") as f:
        #     f.write(json.dumps(pretty, indent=4))
        print("C: ")
        print(propogated_types.translate(Lang.C))
        print("UCLID5: ")
        print(propogated_types.translate(Lang.UCLID5))
        print("API: ")
        print(propogated_types.translate(Lang.API))
        typed, subtree = check_typed(propogated_types)
        if not typed:
            print(f"WARNING: expression {propogated_types} not fully typed")
            print(f"Untyped subtree: {subtree}")

        print("-------------------------------------")
