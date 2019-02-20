Chip
====

Change impact analysis in Coq and OCaml.

Requirements
------------

Definitions and proofs:

- [Coq 8.8 or 8.9](http://coq.inria.fr)
- [MathComp 1.7.0](https://math-comp.github.io/math-comp/) (`ssreflect` and `fingroup` suffice)

Executable tool:

- [OCaml 4.05.0 or later](https://ocaml.org)
- [Ocamlbuild](https://github.com/ocaml/ocamlbuild)
- [yojson](https://github.com/ocaml-community/yojson)
- [extlib](https://github.com/ygrek/ocaml-extlib)

Checking the definitions and proofs
-----------------------------------

We recommend installing the requirements via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-mathcomp-fingroup
```

Then run:
```
make
```
This will build the whole project and check all the proofs.

Building the tool
-----------------

First install the Coq requirements as above, then install the OCaml requirements:
```
opam install ocamlbuild yojson extlib
```

Then, to build the regular tool, run
```
make impacted
```
To try plain change impact analysis, go to `extraction/impacted` and run:
```
./filtering.native test/new.json test/old.json
```
To try hierarchical change impact analysis, run:
```
./hierarchical.native test/new-hierarchical.json test/old-hierarchical.json
```
To try topological sorting, run:
```
./topfiltering.native test/new-topsort.json test/old-topsort.json
```

To build the tool with red-black trees, run:
```
make impacted-rbt
```
and look in `extraction/impacted-rbt`.

Coq files
---------

Adapted and extended from work by [Cohen and Thery](https://github.com/CohenCyril/tarjan):

- `core/extra.v`: auxiliary sequence lemmas
- `core/connect.v`: auxiliary connect and topological sort definitions and lemmas
- `core/kosaraju.v`: implementation and correctness proof of Kosaraju's strongly connected components algorithm
- `core/tarjan.v`: implementation and correctness proof of Tarjan's strongly connected components algorithm

Adapted from work by [Nanevski et al.](https://github.com/imdea-software/fcsl-pcm):

- `core/ordtype.v`: ordered type definition for the Mathematical Components library

Core definitions and lemmas:

- `core/closure.v`: basic definition of transitive closures of sets
- `core/check.v`: set-based definitions of dependency graphs, impactedness, and freshness
- `core/change.v`: correctness argument for basic change impact analysis definitions
- `core/hierarchical.v`: overapproximation strategy for change impact analysis in hierarchical systems
- `core/hierarchical_correct.v`: correctness proofs for overapproximation strategy
- `core/hierarchical_sub.v`: compositional strategy for change impact analysis in hierarchical systems
- `core/hierarchical_sub_correct.v`: correctness proofs for compositional strategy
- `core/acyclic.v`: definition of and basic lemmas for acyclicity, parameterized acyclicity checker
- `core/kosaraju_acyclic.v`: acyclicity checking based on Kosaraju's algorithm
- `core/tarjan_acyclic.v`: acyclicity checking based on Tarjan's algorithm
- `core/topos.v`: definitions and lemmas on topological sorting of acyclic graphs

Implementation-related definitions and lemmas:

- `core/close_dfs.v`: refined sequence-based transitive closure computation
- `core/dfs_set.v`: refined transitive closure computation using MSet functor (to enable red-black trees)
- `core/check_seq.v`: sequence-based change impact analysis definitions, optimized topological sorting using impact analysis
- `core/check_seq_hierarchical.v`: sequence-based hierarchical change impact analysis definitions
- `core/finn.v`: regular instantiation of sequence-based definitions for the ordinal finite type
- `core/finn_set.v`: red-black tree instantiation of sequence-based definitions for the ordinal finite type
