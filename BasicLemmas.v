Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import PeanoNat.
Require Import Psatz. (* lia tactic for linear integer arithmetic *)

Require Export Parser.Structures.
Require Export Parser.Tactics.

Fixpoint remove_id (xs : names) (i : id) : names := match xs with
  | nil => nil
  | cons y ys =>
    if id_eq_dec i y
    then remove_id ys i
    else cons y (remove_id ys i)
  end.

Lemma remove_id_smaller : forall xs i,
  length (remove_id xs i) <= length xs.
Proof.
  induction xs; repeat light || destruct_match; firstorder with lia.
Qed.

Ltac t_remove_id_smaller :=
  match goal with
  | |- context[remove_id ?xs ?i] =>
    poseNew (Mark (xs, i) "remove_id_smaller");
    pose proof (remove_id_smaller xs i)
  end.

Lemma remove_id_strictly_smaller : forall xs i,
  In i xs ->
  length (remove_id xs i) < length xs.
Proof.
  induction xs; repeat light || destruct_match || instantiate_any || t_remove_id_smaller; lia.
Qed.

Ltac t_remove_id_strictly_smaller :=
  match goal with
  | H: In ?i ?xs |- context[length (remove_id ?xs ?i)] =>
    poseNew (Mark (i,xs) "remove_id_strictly_smaller");
    pose proof (remove_id_strictly_smaller xs i)
  end.

Lemma remove_id_preserve_others : forall xs i j,
  (i <> j) ->
  In j xs ->
  In j (remove_id xs i).
Proof.
  induction xs; repeat light || destruct_match.
Qed.

Ltac t_remove_id_preserve_others :=
  match goal with
  | H1: ?i = ?j -> False, H2: In ?j ?xs |- _ =>
    is_var xs;
    poseNew (Mark (i,j,xs) "remove_id_preserve_others");
    pose proof (remove_id_preserve_others _ _ _ H1 H2)
  | H1: ?j = ?i -> False, H2: In ?j ?xs |- _ =>
    is_var xs;
    poseNew (Mark (i,j,xs) "remove_id_preserve_others");
    unshelve epose proof (remove_id_preserve_others _ _ _ _ H2)
  end.

Lemma remove_id_no_new : forall xs i j,
  In j (remove_id xs i) ->
  In j xs.
Proof.
  induction xs; repeat light || destruct_match; eauto.
Qed.

Lemma remove_id_not_in : forall xs i,
  ~In i xs ->
  remove_id xs i = xs.
Proof.
  induction xs; repeat light || destruct_match || f_equal; eauto.
Qed.

Lemma remove_id_sub_names_1 : forall n x,
  incl (remove_id n x) n.
Proof.
  unfold incl; intros; eauto using remove_id_no_new.
Qed.

Lemma remove_id_sub_names_2 : forall n0 n x,
  incl n n0 ->
  incl (remove_id n x) n0.
Proof.
  unfold incl; intros; eauto using remove_id_no_new.
Qed.

Lemma remove_id_commute: forall n i j,
  remove_id (remove_id n i) j = remove_id (remove_id n j) i.
Proof.
  induction n; repeat light || destruct_match.
Qed.

Lemma in_remove_self: forall n i,
  In i (remove_id n i) -> False.
Proof.
  induction n; repeat light || destruct_match; eauto.
Qed.

Ltac t_in_remove_self :=
  match goal with
  | H: In ?i (remove_id ?n ?i) |- _ =>
    apply (False_ind _ (in_remove_self _ _ H))
  end.

Lemma remove_id_twice: forall n i,
  remove_id (remove_id n i) i = remove_id n i.
Proof.
  induction n; repeat light || destruct_match.
Qed.

Ltac decide_id_equalities :=
  match goal with
  | i1: id, i2: id |- _ =>
    poseNew (Mark (i1, i2) "Nat.eq_dec");
    poseNew (Mark (i2, i1) "Nat.eq_dec");
    pose proof (id_eq_dec i1 i2)
  end.

Lemma remove_id_sub_names_both : forall n1 n2 x,
  incl n2 n1 ->
  incl (remove_id n2 x) (remove_id n1 x).
Proof.
  unfold incl; repeat light || decide_id_equalities || t_in_remove_self || apply remove_id_preserve_others || apply_any;
    eauto using remove_id_no_new.
Qed.
