Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.AmbiguityConflict.

Lemma matches_inv_disj_l:
  forall A (s1 s2 : Syntax A) t ts v,
    matches (Disjunction s1 s2) (t :: ts) v ->
    In (class t) (first_fun s1) ->
    (has_conflict_ind (Disjunction s1 s2) -> False) ->
    matches s1 (t :: ts) v.
Proof.
  repeat light || invert_matches || apply_anywhere first_fun_sound;
    eauto with has_conflict_ind exfalso.
Qed.

Lemma matches_inv_disj_r:
  forall A (s1 s2 : Syntax A) t ts v,
    matches (Disjunction s1 s2) (t :: ts) v ->
    In (class t) (first_fun s2) ->
    (has_conflict_ind (Disjunction s1 s2) -> False) ->
    matches s2 (t :: ts) v.
Proof.
  repeat light || invert_matches || apply_anywhere first_fun_sound;
    eauto with has_conflict_ind exfalso.
Qed.

Lemma matches_inv_seq:
  forall A1 A2 (s1: Syntax A1) (s2 : Syntax A2) t ts v a,
    matches (Sequence s1 s2) (t :: ts) v ->
    ~In (class t) (first_fun s1) ->
    matches s1 [] a ->
    (has_conflict_ind (Sequence s1 s2) -> False) ->
    matches (Sequence (Epsilon a) s2) (t :: ts) v.
Proof.
  repeat light || invert_matches || apply_anywhere first_fun_sound || app_cons_destruct ||
         invert_constructor_equalities || matches_nil_unicity2;
    eauto with has_conflict_ind exfalso;
    eauto with matches;
    eauto using first_fun_complete with exfalso.
Qed.
