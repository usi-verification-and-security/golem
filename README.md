# Golem

[![Join the chat at https://gitter.im/usi-verification-and-security/golem](https://badges.gitter.im/usi-verification-and-security/golem.svg)](https://gitter.im/usi-verification-and-security/golem?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

Golem is a solver for Constrained Horn Clauses (CHCs).
It accepts the input in the format of (extended) SMT-LIB 2.6, as defined by [CHC-COMP](https://chc-comp.github.io/format.html).

## Installation
The easiest way is to download the executables from our release page. This way, all dependencies are already bundled in the executable.

### Building from source
Golem can be compiled on Linux and MacOS.
It uses `CMake` for build configuration.
Golem depends on [OpenSMT](https://github.com/usi-verification-and-security/opensmt/) for SMT solving and interpolation.
If you already have OpenSMT installed, you can pass the path using `-DOPENSMT_HOME` option to `cmake` command.
Note that Golem requires a specific version of OpenSMT, currently v2.4.0.
Otherwise, `cmake` will download the latest compatible version of OpenSMT and build it as a subproject.

## Usage
You can view the usage in the help message after running 
```
$ golem -h
```

At the moment, you must specified the SMT theory used in the CHC encoding with `-l` option. The supported theories are `QF_LRA` and `QF_LIA`, i.e., the linear arithmetic over reals or integers.
We plan to remove this requirement and automatically detect the theory in the future.

### Backend engines
Golem currently supports 5 different backend algorithms for solving CHCs.
- spacer [default]
- bmc
- lawi
- tpa
- split-tpa

Spacer engine is the default one.
It represents are own implementation of the algorithm from [this paper](https://link.springer.com/article/10.1007/s10703-016-0249-4). You might be familiar with the original implementation of Spacer inside [Z3](https://github.com/z3Prover/z3/).

BMC engine implements the simple bounded model checking algorithm which checks for existence of increasingly longer counterexample paths in a given transition system.
It uses incremental capibilities of the underlying SMT solver to speed up the process.

LAWI stands for Lazy Abstraction With Interpolants. The algorithm is described in [this paper](https://link.springer.com/chapter/10.1007/11817963_14).
It is also known as `Impact`, which was the first tool where the algorithm was implemented.
LAWI engine supports only linear systems of Horn clauses.

TPA stands for Transition Power Abstraction. It is an algorithm we have developed recently with the goal to detect long counterexample quickly. The description of the algorithm can be found in [this paper](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_29).
TPA supports only a limited subset of linear CHC systems that represent chains of transition systems.

split-TPA is a different instantiation of the TPA paradigm and is typically more powerful than TPA on satisfiable (safe) CHC systems.

### Witness validation and printing
Golem supports internal validation of witnesses for its answer using `--validate` option.
Witness for `sat` is a model, an interpretation of the predicates.
Witness for `unsat` is a proof.
This option is still experimental. For example, `spacer` engine does not computes `unsat` witnesses yet. Also `tpa/split-tpa` does not always produce the witness yet.
 
To obtain the produced model or proof of unsatisfiability, use `--print-witness` option.
