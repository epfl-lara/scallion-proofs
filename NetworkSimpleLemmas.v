Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.NetworkConstruction.

Opaque set_cell.
Opaque io_types.

Lemma same_inputs_make_network':
  forall A G (s: Syntax A) (descr: Description G) k N,
    forall k', k' < k -> inputs (make_network' s descr k N) k' = inputs N k'.
Proof.
  induction s;
    repeat light || destruct_match || invert_constructor_equalities ||
           match goal with
           | H: context[make_network' ?s _ _ _] |- context[make_network' ?s ?descr ?k ?N] =>
               unshelve epose proof (H descr k N ); clear H
           | H: forall k, _ -> inputs _ _ = inputs _ _ |- _ => rewrite H in * by lia
           end;
    try lia.
Qed.

Lemma same_inputs_make_network2':
  forall A G (s: Syntax A) (descr: Description G) k N,
    forall k', k' >= k + syntax_size s -> inputs (make_network' s descr k N) k' = inputs N k'.
Proof.
  induction s;
    repeat light || destruct_match || invert_constructor_equalities ||
           match goal with
           | H: context[make_network' ?s _ _ _] |- context[make_network' ?s ?descr ?k ?N] =>
               unshelve epose proof (H descr k N ); clear H
           | H: forall k, _ -> inputs _ _ = inputs _ _ |- _ => rewrite H in * by lia
           end;
    try lia.
Qed.

Lemma cell_make_network':
  forall A (s: Syntax A) G (descr: Description G) k N,
    cells (make_network' s descr k N) k = make_cell_with_state s descr None.
Proof.
  destruct s;
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Lemma cell_make_network:
  forall A (s : Syntax A) G (descr : Description G),
    cells (make_network s descr) (sum_sizes vars) = make_cell_with_state s descr None.
Proof.
  unfold make_network;
    repeat light || rewrite cell_make_network'.
Qed.

Lemma same_cells_make_network':
  forall A (s: Syntax A) G (descr: Description G) k N,
    forall k', k' < k -> cells (make_network' s descr k N) k' = cells N k'.
Proof.
  induction s;
    repeat light || destruct_match || invert_constructor_equalities ||
           match goal with
           | H: context[make_network' ?s _ _ _] |- context[make_network' ?s ?descr ?k ?N] =>
               unshelve epose proof (H _ descr k N); clear H
           | H: forall k, _ -> cells _ _ = cells _ _ |- _ => rewrite H in * by lia
           end;
    try lia.
Qed.

Lemma same_cells_make_network2':
  forall A (s: Syntax A) G (descr: Description G) k N,
    forall k', k' >= k + syntax_size s -> cells (make_network' s descr k N) k' = cells N k'.
Proof.
  induction s;
    repeat light || destruct_match || invert_constructor_equalities ||
           match goal with
           | H: context[make_network' ?s _ _ _] |- context[make_network' ?s ?descr ?k ?N] =>
               unshelve epose proof (H _ descr k N); clear H
           | H: forall k, _ -> cells _ _ = cells _ _ |- _ => rewrite H in * by lia
           end;
    try lia.
Qed.
