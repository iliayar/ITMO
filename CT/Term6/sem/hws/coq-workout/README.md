This is a supplementary repository for a one-term course on formal semantics.

## Project files description

- `Id.v` – definition of identifiers (partially inherited from Benjamin Pierce's Software Foundations);
- `State.v` – definition of states and some operations for states;
- `Expr.v` – pure strict expressions with big-step evaluation definition and equivalences;
- `Stmt.v` – L, a While-like language, with a big-step semantics and its properties;
- `Euclid.v` – an Euclid's algorithm in L and a statement of its termination in the big-step semantis;
- `SmallStep.v` – a small-step semantics for L and its equivalences to the big-step semantics;
- `Hoare.v` – an axiomatics semantics for L with examples;
- `CPS.v` – a CPS semantics for L and its equivalences to the big-step semantics;
- `Lambda.v` – a simple lambda calculus workout.

## Installation

The use of [opam](https://opam.ocaml.org) is highly advised. The current version works
with `ocaml>=4.11.1` and `coq>=8.13.0`. From the command line:
```bash
opam remote add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq coq-hahn
```
This will install `coq` and `hahn` library. You can then
```bash
make
```
the project to check that everything is in sync.
