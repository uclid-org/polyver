# PolyVer: A Compositional Approach for Polyglot System Modeling and Verification

PolyVer is a framework for modeling and verifying polyglot systems, which are systems that consist of components written in different programming languages.
It supports both automated verification and synthesis of contracts for procedures in these systems.
This is the artifact for the paper ^ in FMCAD 2025.

## Features
- Modeling: supports modeling of polyglot systems using the modeling and verification tool UCLID5.
- Verification: supports C and Rust procedures with cbmc and Kani as language-verifiers.
- Synthesis: supports LLM-based, user-input, and SyGuS/SyMO synthesizers for pre/post-condition contract synthesis.

## Installation
Clone the repo and install locally:
```
git clone https://github.com/uclid-org/polyver.git
cd polyver
pip install -e .
```

## Dependencies
To run this project, you'll need the following dependencies. Please refer to each project for installation instructions.
- [UCLID5](https://github.com/uclid-org/uclid)
- [UCLID5 Python API](https://github.com/uclid-org/uclid-api)
- [cbmc](https://github.com/diffblue/cbmc/releases/tag/cbmc-6.3.1) (tested with version 6.3.1)
- [Kani](https://model-checking.github.io/kani/install-guide.html) (tested with version 0.56.0)
- [delphi](https://github.com/polgreen/delphi/tree/0.1) (for SyMO synthesizer)

## Directory Structure
- `polyver/`: Contains the main codebase for PolyVer.
- `polyver/synthesizers/`: Contains the synthesizer (LLM, user-input, and SyGuS/SyMO).
- `polyver/verifiers/`: Contains the verifiers (cbmc and kani).
- `examples/`: Contains example modules and procedures.

## Usage
[examples/example/example.py](examples/example/example.py) provides a simple example of how to define and verify a custom module using PolyVer.
To run the example, execute the following command:

```bash
python3 examples/example/example.py --verbose
```

### Module Definition
To define and verify a custom module using PolyVer, extend the `Module` class and register procedures in `self.procs`.
Here we define a module named `ExampleModule` that contains a C procedure `foo`, where its source code and JSON metadata are stored in the same directory as the module.

```python
from uclid.builder import *
from uclid.builder_sugar import *

from polyver.module import Module
from polyver.procedure import Procedure
from polyver.utils import Lang

from pathlib import Path

class ExampleModule(Module):
    def __init__(self, delete=True, verbose=False):
        super().__init__("example", delete, verbose)
        foo = Procedure(
            name="foo",
            lang=Lang.C,
            filepath=Path(__file__).parent / "foo.c",
            jsonpath=Path(__file__).parent / "foo.json",
        )
		# Required to store procedures in a dictionary named `self.procs`
        self.procs = {foo.name: foo}
```

Next, we define the `buildUclidModule` method to construct the UCLID5 module.
The C function `foo` is specified as a __noinline__ UCLID5 procedure, meaning only the contract will be used for verification. The procecdure's contract is verified separately using cbmc.
`getLatestUclid...String` methods are used to retrieve the latest UCLID5 strings for the procedure's pre/post-conditions, which are then used to build the UCLID5 module.

```python
    def buildUclidModule(self) -> UclidModule:
        # ...
        requires = UclidRaw(self.procs["foo"].getLatestUclidRequiresString())
        ensures = UclidRaw(self.procs["foo"].getLatestUclidEnsuresString())
        proc_sig = UclidProcedureSig(
            inputs=[(i, valType)],
            modifies=None,
            returns=[(r, valType)],
            requires=requires,
            ensures=ensures,
            noinline=True,
        )
        foo = m.mkProcedure(
            "foo",
            proc_sig,
            UclidBlockStmt([]),
        )
        # ...
        # Return a Uclid module here
        pass
```


### Verification
To verify the module, use the `ModelChecker` class provided by PolyVer.
`getModelChecker` allows you to configure the model checker via command line.

```python
from polyver.main import getModelChecker

# Create an instance of the module
m = ExampleModule()
# Create a model checker instance
mc = getModelChecker(m)
# Run the model checker
mc.check()
# Write a report as a json file
mc.report("./result.json")
```

This writes a report to `result.json` containing the verification results of the module, including contracts if verified successfully otherwise a counterexample trace.
This report can be passed via `--init_solution` argument to verify correctness.

For more details regarding model checker configuration, try `python3 examples/example/example.py --help`.
