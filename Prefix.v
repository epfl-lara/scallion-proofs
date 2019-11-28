Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.Tactics.
Require Export Parser.Matches.

Definition prefix { A B } (s1: Syntax A) (s2: Syntax B): Prop :=
  forall ts v, matches s1 ts v ->
  exists ts' v', matches s2 (ts ++ ts') v'.

Ltac prefix :=
  match goal with
  | H1: matches_without _ ?s1 ?ts ?v, H2: prefix ?s1 ?s2 |- _ =>
    poseNew (Mark (ts,s2) "prefix");
    unshelve epose proof (H2 ts v _)
  end.

Lemma prefix_disj_l:
  forall A B (s1 s2: Syntax A) (s: Syntax B),
    prefix (Disjunction s1 s2) s ->
    prefix s1 s.
Proof.
  unfold prefix; repeat light; eauto with matches.
Qed.

Lemma prefix_disj_r:
  forall A B (s1 s2: Syntax A) (s: Syntax B),
    prefix (Disjunction s1 s2) s ->
    prefix s2 s.
Proof.
  unfold prefix; repeat light; eauto with matches.
Qed.

Lemma prefix_seq_l:
  forall A1 A2 B (s1: Syntax A1) (s2: Syntax A2) (s: Syntax B) ts v,
    prefix (Sequence s1 s2) s ->
    matches s2 ts v ->
    prefix s1 s.
Proof.
  unfold prefix; repeat light;
    eauto with matches.
  unshelve epose proof (H (ts0 ++ ts) (v0, v) _);
    repeat light || rewrite <- app_assoc in *;
    eauto with matches.
Qed.

Lemma prefix_seq_r:
  forall A1 A2 B (s1: Syntax A1) (s2: Syntax A2) (s: Syntax B) v,
    prefix (Sequence s1 s2) s ->
    matches s1 [] v ->
    prefix s2 s.
Proof.
  unfold prefix; repeat light;
    eauto with matches.
Qed.

Lemma prefix_map:
  forall A B C (f: A -> B) g (s: Syntax A) (s': Syntax C),
    prefix (Map f g s) s' ->
    prefix s s'.
Proof.
  unfold prefix; repeat light;
    eauto with matches.
Qed.

Lemma prefix_var:
  forall A x (s: Syntax A),
    prefix (Var x) s ->
    prefix (e x) s.
Proof.
  unfold prefix; repeat light;
    eauto with matches.
Qed.

Hint Resolve prefix_disj_l: prefix.
Hint Resolve prefix_disj_r: prefix.
Hint Resolve prefix_seq_l: prefix.
Hint Resolve prefix_seq_r: prefix.
Hint Resolve prefix_map: prefix.
Hint Resolve prefix_var: prefix.

Ltac prefix_sub :=
  match goal with
  | H: prefix (Disjunction ?s _) _ |- _ =>
    poseNew (Mark H "prefix_sub");
    pose proof (prefix_disj_l _ _ _ _ _ H);
    pose proof (prefix_disj_r _ _ _ _ _ H)
  | H1: prefix (Sequence ?s1 ?s2) _,
    H2: matches ?s2 _ _
    |- _ =>
    poseNew (Mark (H1, H2) "prefix_sub");
    pose proof (prefix_seq_l _ _ _ _ _ _ _ _ H1 H2)
  | H1: prefix (Sequence ?s1 ?s2) _,
    H2: matches ?s1 [] _
    |- _ =>
    poseNew (Mark (H1, H2) "prefix_sub");
    pose proof (prefix_seq_r _ _ _ _ _ _ _ H1 H2)
  | H: prefix (Map _ _ _) _ |- _ =>
    poseNew (Mark H "prefix_sub");
    pose proof (prefix_map _ _ _ _ _ _ _ H)
(*  | H: prefix (Var _) _ |- _ =>
    poseNew (Mark H "prefix_sub");
    pose proof (prefix_var _ _ _ H) *) (* loop *)
  end.
