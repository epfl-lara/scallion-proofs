# Scallion Proofs [![Build Status][larabot-img]][larabot-ref]

### Overview

This project proves the correctness of the parsing with derivatives
algorithm used in Scallion.

### Roadmap

* `Structures.v` contains the definition of the `Syntax` type.
* `Matches.v` describes when does a syntax associate a value with a token sequence.
* `FocusedSyntax.v` contains the definition of focused syntaxes, and the `unfocus` function that returns a standard `Syntax`.
* The `FocusedSyntax*.v` files contain the definitions of functions on
  focused syntaxes and their associated lemmas.
* `Description.v` contains the definition of *descriptions*, which allow to
* The `*Descr.v` files contains the descriptions for the functions on syntaxes: nullable, productive, first, should-not-follow, has-conflict.
  specify functions on syntaxes using inductive rules.
* `DescriptionInd.v` contains the inductive semantics of *descriptions*
* `PropagatorNetwork.v` contains a formalisation of propagator networks with
  termination guarantees.
* `DescriptionToFunction.v` builds propagator networks to create functions
  based on descriptions.
* The `DescriptionToFunctionSoundness.v` and `DescriptionToFunctionCompleteness.v` files contain the proofs of soundness
  and completeness of this construction.
* `FocusedSyntaxParse.v` contains the proof of correctness (soundness and
  completeness) for the parsing algorithm based on derivatives of focused syntaxes.
* `dependencies.pdf` contains a graph of the dependencies between the files.


### Installing the dependencies

These proofs require Coq 8.10.2 and Coq Equations 1.2+8.10. If you have `opam`
version 2 installed, these can be installed using the following commands (tested
on Linux). Replace "new-switch-name" by a name you like for the fresh switch.

The opam binaries are available on https://github.com/ocaml/opam/releases.

```
opam switch create new-switch-name 4.09.0
eval $(opam env)
opam install coq.8.10.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2+8.10
```

With older versions of opam, replace the first two commands with:

```
opam switch new-switch-name --alias-of 4.09.0
eval `opam config env`
```


If you have trouble installing, please refer to the official webpages:
* https://coq.inria.fr/download
* https://github.com/mattam82/Coq-Equations


### Compiling the proofs

The proofs can be compiled using:

```
./configure
make -j4      # takes around 13 minutes to complete
```

The compilation returns spurious warnings because some obligations from the
`Equations` package cannot be solved automatically. The obligations are all
solved manually right after in the proof code.

[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/scallion-proofs/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/scallion-proofs/builds
