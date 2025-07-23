# Uclid5 with External Procedures

## Dependencies
This project uses [Uclid5](https://github.com/uclid-org/uclid), [Uclid5 Python API](https://github.com/uclid-org/uclid-api), and [cbmc](https://github.com/diffblue/cbmc). Please refer to the repos for installation instructions.

## Usage
`src/example_module.py` shows how to build a Uclid module with external procedures.
Run `python3 -m polyver.main -h` for available options.

To install the python package, in the root directory run
```
pip install .
```

Currently supports external C and Rust procedures and involves human in the loop.
