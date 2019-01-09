Change Impact Analysis in Coq and OCaml
=======================================

A basic requirement is to install [OPAM](http://opam.ocaml.org/doc/Install.html).

Then create an OPAM switch for OCaml 4.06.1:
```
opam update
opam switch 4.06.1
eval `opam config env`
```

Building the Coq development
----------------------------

First install the requirements:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.8.1
opam pin add coq-mathcomp-ssreflect 1.7.0
opam install coq-mathcomp-fingroup
```

Then run:
```
make
```
This will build the whole project and check all the proofs.

Building the Chip tool
----------------------

First install the Coq requirements as above. Then install the OCaml requirements:
```
opam install ocamlbuild yojson extlib
```

To build regular Chip, run
```
make impacted
```
To then try the tool, go to `extraction/impacted` and run:
```
./filtering.native test/new.json test/old.json
```

To build Chip with red-black trees, run:
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
- `core/run.v`: set-based definitions of dependency graphs, impactedness, and freshness
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
- `core/run_seq.v`: sequence-based change impact analysis definitions, optimized topological sorting using impact analysis
- `core/finn.v`: regular instantiation of sequence-based definitions for the ordinal finite type
- `core/finn_set.v`: red-black tree instantiation of sequence-based definitions for the ordinal finite type
