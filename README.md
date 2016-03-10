Contents
========

This artifact consists of Coq proof scripts defining and proving type
soundness for the languages described in the paper

Casper Bach Poulsen, Pierre Neron, Andrew Tolmach, and Eelco Visser,
"Scopes Decribe Frames: A Uniform Model for Memory Layout in Dynamic Semantics."

"Running" these scripts, i.e. passing them successfully through the
Coq type-checker, serves to verify that these proofs are correct.

Reading the scripts may give insight into the structure of the proofs,
and in particular about how the scopes-as-frames framework is
defined in a generic way independent of the specific languages.

Building
========

To pass all scripts through Coq, run `make`. All proofs are
known to compile with [Coq 8.5](https://coq.inria.fr/download).

It is also possible to step through the proofs interactively using an
IDE such as [CoqIDE](https://coq.inria.fr/download) or
[ProofGeneral](http://proofgeneral.inf.ed.ac.uk).


Pretty-Printed Scripts
======================

To (re-)generate pretty-printed versions of the proof scripts that may be easier
to read, run `make html`.  This runs the CoqDoc utility to generate formatted
html files in the `html` folder.  `html/toc.html` contains a table of contents, and
`html/index.html` an index over the various definitions and lemmas.


Roadmap
=======

The files of this Coq development are structured as follows:

- `html/` contains pretty-printed versions of the scripts.

- `framework/` contains the generic, language-independent framework
  for scopes-as-frames:

    - `maps.v`: a formalization of finite maps, using lists.

    - `prop_fold.v`: a generic propositional fold predicate, used for
      sequential n-ary let-bindings in L2 (see "Differences from the
      paper" below).

    - `scopes.v`: the formalization of resolved scope graphs,
      parameterized by an object language notion of types.

    - `frames.v`: the formalization of frames, heaps, and the
      `good_frame` and `good_heap` properties that capture the essence
      of type soundness using scopes-as-frames. Definitions and lemmas
      are parameterized by an object language notion of values, types,
      and default values.

    - `GC.v`: additional definitions and lemmas for sound garbage collection.

    - `sub.v`: a straightforward adaptation of the key lemmas from
      `frames.v` and the `good_frame` and `good_heap` properties to
      support subtyping.

- `langs/` contains folders for each language in the paper:

    - `L1/syntax.v`: the abstract syntax definition for `L1`.

    - `L1/well_boundness.v`: well-boundness rules for `L1`.

    - `L1/well_typedness.v`: well-typedness rules for `L1`.

    - `L1/semantics.v`: the dynamic semantics for `L1`.

    - `L1/type_soundness.v`: the type soundness proof for L1.

- The files in `langs/L3` are structured similarly to `L1`.

- The files in `langs/L2` are also structured similarly, but contains
  two additional files:

    - `L2/GCsemantics.v`: the dynamic semantics for `L2` with the
      generic garbage collection rule.

    - `L2/GCtype_soundness.v`: the type soundness proof for `L2` with
       sound garbage collection.


Differences from the paper
==========================

The languages described in our paper are simplified versions of the
languages that we used to experiment with proving type soundness.
There are numerous small differences of naming and terminology.
In additon, the languages in this artifact differ from the paper
in the following ways:

- L1 follows the semantics in the paper.

- L2 and L3 differ from the paper as follows:

    - Functions and function types are n-ary, and argument values are
      stored in call-frames immediately after they are computed (as
      opposed to in the big-step derivation tree).

    - The language provides three variants of n-ary let-binding:
      sequential lets, parallel lets, and recursive lets (following
      the static semantics given for these in [1]). Recursive lets are
      restricted to bind values of function type only.

    - The language has boolean expressions and simple if-then-else
      branching.


References
==========

[1] Pierre Neron, Andrew P. Tolmach, Eelco Visser, Guido Wachsmuth: A
    Theory of Name Resolution. ESOP 2015: 205-231
    doi: http://dx.doi.org/10.1007/978-3-662-46669-8_9