# Scallion Proofs [![Build Status][larabot-img]][larabot-ref]

### Overview

This project proves the correctness of the parsing with derivatives
algorithm used in [Scallion](https://github.com/epfl-lara/scallion), which
is presented in this [PLDI paper](https://arxiv.org/pdf/1911.12737.pdf).

### Roadmap

* [Structures.v](Structures.v) contains the definition of the `Syntax` type.
* [Matches.v](Matches.v) describes when does a syntax associate a value with a token sequence.
* [FocusedSyntax.v](FocusedSyntax.v) contains the definition of focused syntaxes, and the `unfocus` function that returns a standard `Syntax`.
* The [FocusedSyntax*.v](FocusedSyntax*.v) files contain the definitions of functions on
  focused syntaxes and their associated lemmas.
* [Description.v](Description.v) contains the definition of *descriptions*, which allow to
* The `*Descr.v` files contains the descriptions for the functions on syntaxes: nullable, productive, first, should-not-follow, has-conflict.
  specify functions on syntaxes using inductive rules.
* [DescriptionInd.v](DescriptionInd.v) contains the inductive semantics of *descriptions*
* [PropagatorNetwork.v](PropagatorNetwork.v) contains a formalisation of propagator networks with
  termination guarantees.
* [DescriptionToFunction.v](DescriptionToFunction.v) builds propagator networks to create functions
  based on descriptions.
* The [DescriptionToFunctionSoundness.v](DescriptionToFunctionSoundness.v) and [DescriptionToFunctionCompleteness.v](DescriptionToFunctionCompleteness.v) files contain the proofs of soundness
  and completeness of this construction.
* [FocusedSyntaxParse.v](FocusedSyntaxParse.v) contains the proof of correctness (soundness and
  completeness) for the parsing algorithm based on derivatives of focused syntaxes.
* [dependencies.pdf](dependencies.pdf) contains a graph of the dependencies between the files.


### Installing the dependencies

These proofs require Coq 8.11.0 and Coq Equations 1.2.1+8.11. If you have `opam`
version 2 installed, these can be installed using the following commands (tested
on Linux). Replace "new-switch-name" by a name you like for the fresh switch.

The opam binaries are available on https://github.com/ocaml/opam/releases.

```
opam init # if you've never used opam before
opam switch create new-switch-name 4.09.0
eval $(opam env)
opam install coq.8.11.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-equations.1.2.1+8.11
```

With older versions of opam, replace the first two commands with:

```
opam init # if you've never used opam before
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
make -j4      # takes 15/20 minutes to complete
```

### Cross-references with the [PLDI paper](https://arxiv.org/pdf/1911.12737.pdf)


* Theorem 1: Follows from the types assigned to the `matches` predicate in [Matches.v](Matches.v)
* Theorem 2: `productive_ind_correct` in [ProductiveInd.v](ProductiveInd.v)
* Theorem 3: `nullable_ind_correct` in [NullableInd.v](NullableInd.v)
* Theorem 4: `first_ind_correct` in [FirstInd.v](FirstInd.v)
* Theorem 5: `should_not_follow_ind_sound` in [ShouldNotFollowInd.v](ShouldNotFollowInd.v)
* Theorem 7: `non_ambiguous_ll1` in [FocusedSyntaxParse.v](FocusedSyntaxParse.v)
* Theorem 8: `should_not_follow_ind_correct` in [ShouldNotFollowComplete.v](ShouldNotFollowComplete.v)
* Theorems of Section 5 are not in Coq, as we directly considered focused
  syntaxes.
* Theorem 14: `plug_correct` in [FocusedSyntaxPlug.v](FocusedSyntaxPlug.v)
* Theorem 15: `locate_not_none2` in [FocusedSyntaxLocateMatches.v](FocusedSyntaxLocateMatches.v)
* Theorem 16: `locate_first_ind` in [FocusedSyntaxLocate.v](FocusedSyntaxLocate.v)
* Theorem 17: `locate_correct` in [FocusedSyntaxLocateMatches.v](FocusedSyntaxLocateMatches.v)
* Theorem 18: `pierce_correct` in [FocusedSyntaxPierceMatches.v](FocusedSyntaxPierceMatches.v)
* Theorem 19: `derive_preserves_ll1` in [FocusedSyntaxDerive.v](FocusedSyntaxDerive.v)
* Theorem 20: `derive_none` in [FocusedSyntaxDerive.v](FocusedSyntaxDerive.v)
* Theorem 21: `derive_sound` in [FocusedSyntaxDerive.v](FocusedSyntaxDerive.v)
* Theorem 22: `result_correct` in [FocusedSyntaxNullable.v](FocusedSyntaxNullable.v)
* Theorem 23: `parse_correct` in [FocusedSyntaxParse.v](FocusedSyntaxParse.v)

### Acknowledgements

We thank the anonymous reviewers of the artifact evaluation for their
suggestions on improving the presentation of the proofs.

[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/scallion-proofs/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/scallion-proofs/builds
