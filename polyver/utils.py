import concurrent.futures
import re
from enum import Enum


class Lang(Enum):
    """Enum for supported languages"""

    API = 0
    UCLID5 = 1
    C = 2
    RUST = 3

    def fromExt(ext):
        if ext == "ucl":
            return Lang.UCLID5
        elif ext == "c":
            return Lang.C
        elif ext == "rs":
            return Lang.RUST
        else:
            raise ValueError(f"Unsupported language: {ext}")


class Result(Enum):
    """Enum class for verification results"""

    PASSED = 0
    VIOLATED = 1
    ERROR = 2
    UNKNOWN = 3
    EXT_SUCCESS = 4
    EXT_FAILURE = 5
    EXT_ERROR = 6
    EXT_UNKNOWN = 7
    VERIF_TIMEOUT = 8
    SYNTH_FAILURE = 9


class Theory(Enum):
    """Enum class for theories"""

    BV = 1
    INT = 2


theory = Theory.BV


# Takes a target (C or Rust) type and returns the corresponding SMT type
def getSMTType(typ):
    match typ:
        case "bool":
            return "Bool"
        # FIXME: Only supports 32-bit integers for now
        case "int":
            if theory == Theory.BV:
                return "(_ BitVec 32)"
            elif theory == Theory.INT:
                return "Int"
        case "i32":
            if theory == Theory.BV:
                return "(_ BitVec 32)"
            elif theory == Theory.INT:
                return "Int"
        case _:
            raise ValueError(f"Unknown type {typ}")


def getSMTName(name):
    return f"|{name}|"


# Returns the default value for a given target (C or Rust) type
def getDefaultValue(t):
    if t == "int":
        return "0"
    elif t == "bool":
        return "false"
    elif t == "i32":
        return "0"
    else:
        raise ValueError(f"Unsupported type: {t}")


class TypeConverter:

    # Converts a ucl value to an integer
    # Currently interprets bitvectors as signed integers
    # TODO: hanlde unsigned bitvectors
    @staticmethod
    def ucl2tgt(value, fr, to):
        # Regular expression to capture bv value and width.
        # E.g., in (_ bv304099331 32), this pattern matches 304099331 and 32.
        pattern = r"\(\_ bv(\d+) (\d+)\)"

        # Find matches
        match = re.match(pattern, value)
        if match:
            bv_value = match.group(1)
            bit_width = match.group(2)
            return str(
                TypeConverter.interpret_signed_bitvector(int(bv_value), int(bit_width))
            )
        elif "int" in fr and "int" in to:
            return value if value.isnumeric() else None
        elif "bv" in fr and "int" in to:
            if value.endswith(fr):
                # This handles the case where uclid prints bitvectors as '5bv32'
                # This happens when print_cex_json is used and the trace is output to a json file.
                # value is of form '<value>bv<width>'
                val, width = value.split("bv")
                return str(
                    TypeConverter.interpret_signed_bitvector(int(val), int(width))
                )
            elif value.isnumeric():
                # This handles the case where uclid prints integers as '5' instead of '5bv32'
                # This happens when print_cex is used and the trace is parsed from stdout.
                return value
            else:
                return None
        elif "int" in fr and "i32" in to:
            return value if value.isnumeric() else None
        elif "bv" in fr and "i32" in to:
            if value.endswith(fr):
                val, width = value.split("bv")
                return str(
                    TypeConverter.interpret_signed_bitvector(int(val), int(width))
                )
            else:
                return None
        elif fr == "boolean" and to == "bool":
            return value if value in ["true", "false"] else None
        return None

    # Converts a tgt value to smtlib format. E.g., 5 -> 5, 5 -> (_ bv5 32)
    # - Assumes value is an integer i.e. (-)?[0-9]+
    # - `to` is an smtlib type
    @staticmethod
    def tgt2smtlib(value, fr):
        # assert "int" in fr
        isNeg = value.startswith("-")
        num = value if not isNeg else value[1:]
        to = getSMTType(fr)  # Convert to SMT type
        if to == "Int":
            return f"(- {num})" if isNeg else num
        elif "BitVec" in to:
            # NOTE: MAY OVERFLOW IF VALUE IS TOO LARGE
            pattern = r"\(\_ BitVec (\d+)\)"
            match = re.match(pattern, to)
            if match:
                width = int(match.group(1))
                if isNeg:
                    return f"(bvneg (_ bv{num} {width}))"
                else:
                    print(f"Printing here (_ bv{num} {width})")
                    return f"(_ bv{num} {width})"
        elif fr == "bool" and to == "Bool":
            print(value)
            assert value.lower() in ["true", "false"]
            return value.lower()
        return None

    @staticmethod
    def interpret_signed_bitvector(x, n):
        # Define a bitmask with the sign bit set
        sign_bitmask = 1 << (n - 1)

        # Perform a bitwise AND operation with the bitmask
        result = x & ((1 << n) - 1)

        # Check if the sign bit is set
        if result & sign_bitmask:
            # If sign bit is set, interpret as negative
            # Convert the result to negative by subtracting 2^n
            result -= 1 << n

        return result


def invoke_parallel(f, args_list, n=None):
    """
    Runs the function `f` on each list of arguments in `args_list` in parallel.

    Parameters:
    - f: The function to run.
    - args_list: A list of lists of arguments to pass to `f`.

    Returns:
    - A list of results from applying `f` to each argument list, in the same order as `args_list`.
    """
    results = []

    def safe_call(args):
        """Wrapper to call `f` safely and handle exceptions."""
        try:
            result = f(*args)
        except Exception as e:
            print(f"Exception occurred: {e}")
            results.append(e)
        else:
            results.append(result)

    with concurrent.futures.ThreadPoolExecutor(max_workers=n) as executor:
        # Use list comprehension with executor.submit for parallel execution
        futures = [executor.submit(safe_call, args) for args in args_list]
        # Wait for all futures to complete
        concurrent.futures.wait(futures)

        for future in concurrent.futures.as_completed(futures):
            try:
                future.result()
            except Exception as e:
                print(f"Exception occurred: {e}")

    return results


def print_trace(trace: dict, logger):
    length = trace["length"]
    content = trace["trace"]
    logger.info(f"Trace length: {length}")
    for i in range(length):
        logger.info(f"========== STEP {i} ==========")
        if isinstance(content[i], str):
            logger.info(content[i])  # Account for UCLID5's parsing error.
        else:
            for var, val in content[i].items():
                logger.info(f"{var}: {val[0]}")
        logger.info("============================")


def parse_uclid_output(file_path):
    with open(file_path, "r") as file:
        lines = file.readlines()

    # Ensure the first line contains the required message
    if not lines or "Successfully instantiated 1 module(s)." not in lines[0]:
        print("Error: Log file does not indicate successful instantiation.")
        return {}

    results = {}
    property_counter = {}  # Track occurrences of each property name
    current_cex = None
    key_value_store = None  # Store key-value pairs for the current step

    for i, line in enumerate(lines):
        # Detect CEX entry
        if line.startswith("CEX for"):
            # Save previous CEX entry if it exists
            if current_cex and key_value_store is not None:
                results[current_cex]["trace"].append(key_value_store)
                key_value_store = None

            # Extract the property name
            match = re.search(r"property (\S+)", line)
            precondition_match = re.search(r"(precondition_\S+)", line)

            if precondition_match:
                base_name = precondition_match.group(1)
            elif match:
                base_name = "property_" + match.group(1)
            else:
                continue  # If no valid property name is found, skip

            # Track occurrences and rename consistently (starting at _0)
            count = property_counter.get(base_name, 0)
            property_counter[base_name] = count + 1
            current_cex = f"{base_name}__{count}"

            # Initialize list in results if new property
            if current_cex not in results:
                results[current_cex] = {"length": 0, "trace": []}

        # Detect step start
        elif line.startswith("Step #") and current_cex:
            # Save previous step data if it exists
            if key_value_store is not None:
                results[current_cex]["trace"].append(key_value_store)

            key_value_store = {}  # Start new dictionary for next step

        # Detect key-value pairs
        elif ":" in line and key_value_store is not None:
            parts = line.split(":", 1)
            key = parts[0].strip()
            value = parts[1].strip()
            key_value_store[key] = [value]

    # Save the last step if it exists
    if current_cex and key_value_store is not None:
        results[current_cex]["trace"].append(key_value_store)

    # Update trace length for each property
    for prop in results:
        results[prop]["length"] = len(results[prop]["trace"])

    return results


if __name__ == "__main__":
    # Test type conversion
    val = TypeConverter.ucl2tgt("2147483649bv32", "bv32", "int")
    print(val)
    val = TypeConverter.ucl2tgt("(_ bv304099331 32)", "bv32", "int")
    print(val)

    # Test parallel invocation
    def test_func(a, b):
        return a + b

    results = invoke_parallel(test_func, [[1, "3"]] * 5)
    print(results)

    # Test uclid output parsing
    import json
    import sys

    log_file = sys.argv[1] if len(sys.argv) > 1 else "example.log"
    output_json = sys.argv[2] if len(sys.argv) > 2 else "output.json"

    parsed_data = parse_uclid_output(log_file)

    # Save results to a JSON file
    with open(output_json, "w") as json_file:
        json.dump(parsed_data, json_file, indent=2)

    print(f"Results saved to {output_json}")
