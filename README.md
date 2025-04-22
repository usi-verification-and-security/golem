# Golem

[![CircleCI](https://dl.circleci.com/status-badge/img/gh/usi-verification-and-security/golem/tree/master.svg?style=shield)](https://dl.circleci.com/status-badge/redirect/gh/usi-verification-and-security/golem/tree/master)


Golem is a solver for Constrained Horn Clauses (CHCs).
It accepts the input in the format of (extended) SMT-LIB 2.6, as defined by [CHC-COMP](https://chc-comp.github.io/format.html).

## Installation
The easiest way is to download the executables from our release page. This way, all dependencies are already bundled in the executable.

### Building from source
Golem can be compiled on Linux and MacOS.
It uses `CMake` for build configuration.
Golem depends on [OpenSMT](https://github.com/usi-verification-and-security/opensmt/) for SMT solving and interpolation.
If you already have OpenSMT installed, you can pass the path using `-DOPENSMT_HOME` option to `cmake` command.
Note that Golem requires a specific version of OpenSMT, currently v2.9.1.
Otherwise, `cmake` will download the latest compatible version of OpenSMT and build it as a subproject.

## Usage
You can view the usage in the help message after running 
```
$ golem -h
```

At the moment, you should specified the SMT theory used in the CHC encoding with `-l` option. The supported theories are `QF_LRA` and `QF_LIA`, i.e., the linear arithmetic over reals or integers.
Golem now has limited support to automatically detect the theory from the script, so the option is no longer mandatory, but still recommended.

## Backend engines
Golem supports several different backend algorithms for solving CHCs.

### Spacer (default)
Spacer engine represents our own implementation of the Spacer algorithm from [this paper](https://link.springer.com/article/10.1007/s10703-016-0249-4). You might be familiar with the original implementation of Spacer inside [Z3](https://github.com/z3Prover/z3/).


### Bounded model checking

BMC engine implements the simple bounded model checking algorithm which checks for existence of increasingly longer counterexample paths.
It uses incremental capibilities of the underlying SMT solver to speed up the process.
Works only for linear systems of Horn clauses.

### Dual Approximated Reachability

DAR engine implements the algorithm Dual Approximated Reachability described in [this paper](https://link.springer.com/chapter/10.1007/978-3-642-36742-7_22).
It works only for linear systems of Horn clauses. 

### k-induction

KIND engine implements very basic k-induction algorithm from [this paper](https://link.springer.com/chapter/10.1007/3-540-40922-X_8).
It only supports transition systems.

### Lazy Abstraction With Interpolants (Impact)

The implementation of LAWI follows the description of the algorithm in [this paper](https://link.springer.com/chapter/10.1007/11817963_14).
The algorithm is also known as `Impact`, which was the first tool where the algorithm was implemented.
Works only for linear systems of Horn clauses.

### McMillan's Interpolation-based model checking

IMC engine implements the original McMillan's interpolation-based model-checking algorithm from [this paper](https://link.springer.com/chapter/10.1007/978-3-540-45069-6_1).
It works on transition system, but it can handle linear systems of Horn clauses by first transforming them into a simple transition system.

### Predicate Abstraction and CEGAR

The PA engine is a simple prototype of a [predicate abstraction](https://link.springer.com/chapter/10.1007/3-540-63166-6_10) with [CEGAR](https://link.springer.com/chapter/10.1007/10722167_15).
The implementation is still rather naive, but the algorithm can handle all (even nonlinear) CHC systems.


### Property-directed k-induction

The implementation of PDKIND follows the description of the algorithm in [this paper](https://ieeexplore.ieee.org/document/7886665).
It works on transition system, but it can handle linear systems of Horn clauses by first transforming them into a simple transition system.

### Transition Power Abstraction

TPA is an algorithm we have developed recently with the goal to detect long counterexample quickly. The description of the algorithm can be found in [this paper](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_29).
TPA directly supports a subset of linear CHC systems which can be mapped to DAGs of transition systems.
Transitions that do not fall into this category are handled by transformation into a simple transition system.

[split-TPA](https://ieeexplore.ieee.org/document/10026590) is a different instantiation of the TPA paradigm and is typically more powerful than basic TPA on satisfiable (safe) CHC systems.


#### Running multiple engines in parallel

Golem also supports multiprocess run of several engines simultaneously.
You can pass comma-separated list of engines to `--engine` options.
For example, the following invocation will run split-TPA, Spacer and LAWI in parallel

```sh
golem --engine split-tpa,spacer,lawi --input <file>
```

### Witness validation and printing
Golem supports internal validation of witnesses for its answer using `--validate` option.
Witness for `sat` is a model, an interpretation of the predicates.
Witness for `unsat` is a proof.
 
To obtain the produced model or proof of unsatisfiability, use `--print-witness`.
