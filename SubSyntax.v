Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.Tactics.
Require Export Parser.Matches.

Definition accepts { A } (s: Syntax A) (ts: list token): Prop :=
  exists v, matches s ts v.

Lemma matches_accept:
  forall A (s: Syntax A) ts v,
    matches s ts v ->
    accepts s ts.
Proof.
  unfold accepts; eauto.
Qed.

Hint Resolve matches_accept: matches.

Definition subsyntax { A1 A2 } (s1: Syntax A1) (s2: Syntax A2): Prop :=
  forall ts, accepts s1 ts -> accepts s2 ts.

Lemma subsyntax_refl:
  forall A (s: Syntax A),
    subsyntax s s.
Proof.
  unfold subsyntax; lights.
Qed.

Lemma subsyntax_trans:
  forall (A1 A2 A3: Type) (s1: Syntax A1) (s2: Syntax A2) (s3: Syntax A3),
    subsyntax s1 s2 ->
    subsyntax s2 s3 ->
    subsyntax s1 s3.
Proof.
  unfold subsyntax; lights.
Qed.

Lemma subsyntax_disj_l:
  forall A (s1 s2: Syntax A),
    subsyntax s1 (Disjunction s1 s2).
Proof.
  unfold subsyntax, accepts; lights; eauto with matches.
Qed.

Lemma subsyntax_disj_r:
  forall A (s1 s2: Syntax A),
    subsyntax s2 (Disjunction s1 s2).
Proof.
  unfold subsyntax, accepts; lights; eauto with matches.
Qed.

Lemma subsyntax_disj_empty_l:
  forall A (s1 s2: Syntax A),
    (forall ts v, ~matches s2 ts v) ->
    subsyntax (Disjunction s1 s2) s1.
Proof.
  unfold subsyntax, accepts; repeat light || invert_matches; eauto with exfalso.
Qed.

Lemma subsyntax_disj_empty_r:
  forall A (s1 s2: Syntax A),
    (forall ts v, ~matches s1 ts v) ->
    subsyntax (Disjunction s1 s2) s2.
Proof.
  unfold subsyntax, accepts; repeat light || invert_matches; eauto with exfalso.
Qed.

Lemma subsyntax_seq_l:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) v,
    matches s2 [] v ->
    subsyntax s1 (Sequence s1 s2).
Proof.
  unfold subsyntax, accepts; lights; eauto with matches.
Qed.

Lemma subsyntax_seq_r:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) v,
    matches s1 [] v ->
    subsyntax s2 (Sequence s1 s2).
Proof.
  unfold subsyntax, accepts; lights; eauto with matches.
Qed.

Lemma subsyntax_map_s:
  forall A B (f: A -> B) g s,
    subsyntax (Map f g s) s.
Proof.
  unfold subsyntax, accepts; repeat light || invert_matches; eauto.
Qed.

Lemma subsyntax_s_map:
  forall A B (f: A -> B) g s,
    subsyntax s (Map f g s).
Proof.
  unfold subsyntax, accepts; repeat light; eauto with matches.
Qed.

Lemma subsyntax_var_e:
  forall x, subsyntax (Var x) (e x).
Proof.
  unfold subsyntax, accepts; repeat light || invert_matches; eauto.
Qed.

Lemma subsyntax_e_var:
  forall x, subsyntax (e x) (Var x).
Proof.
  unfold subsyntax, accepts; repeat light; eauto with matches.
Qed.

Hint Immediate subsyntax_refl: subsyntax0.
Hint Immediate subsyntax_disj_l: subsyntax0.
Hint Immediate subsyntax_disj_r: subsyntax0.
Hint Immediate subsyntax_disj_empty_l: subsyntax0.
Hint Immediate subsyntax_disj_empty_r: subsyntax0.
Hint Immediate subsyntax_seq_l: subsyntax0.
Hint Immediate subsyntax_seq_r: subsyntax0.
Hint Immediate subsyntax_map_s: subsyntax0.
Hint Immediate subsyntax_s_map: subsyntax0.
Hint Immediate subsyntax_var_e: subsyntax0.
Hint Immediate subsyntax_e_var: subsyntax0.

Ltac subsyntax_trans :=
  match goal with
  | H: subsyntax ?s ?e |- subsyntax ?s' ?e =>
      unshelve epose proof (subsyntax_trans _ _ _ s' s e _ _);
        eauto with subsyntax0
  | H: subsyntax ?e ?s |- subsyntax ?e ?s' =>
      unshelve epose proof (subsyntax_trans _ _ _ e s s' _ _);
        eauto with subsyntax0
  end.

Hint Extern 1 => eauto with subsyntax0: subsyntax.
Hint Extern 1000 => solve [ subsyntax_trans ]: subsyntax.
