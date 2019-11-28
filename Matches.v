Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Program.Equality.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz. (* lia tactic for linear integer arithmetic *)

Require Import Parser.Structures.
Require Import Parser.Tactics.
Require Import Parser.List.
Require Import Parser.BasicLemmas.

(*** Matching ***)

Inductive matches_without (forbidden: list id): forall A: Type, Syntax A -> list token -> A -> Prop :=
  | MEps: forall A v, matches_without forbidden A (Epsilon v) nil v
  | MElem: forall (t: token),
      matches_without forbidden token (Elem (class t)) (cons t nil) t
  | MDisL: forall A (s1 s2 : Syntax A) (xs : list token) (a: A),
      matches_without forbidden A s1 xs a ->
      matches_without forbidden A (Disjunction s1 s2) xs a
  | MDisR: forall A (s1 s2 : Syntax A) (xs : list token) (a: A),
      matches_without forbidden A s2 xs a ->
      matches_without forbidden A (Disjunction s1 s2) xs a
  | MSeq: forall A B (s1: Syntax A) (s2 : Syntax B) (xs1 xs2 : list token) (a: A) (b: B),
      matches_without forbidden A s1 xs1 a ->
      matches_without forbidden B s2 xs2 b ->
      matches_without forbidden (A * B) (Sequence s1 s2) (xs1 ++ xs2) (a, b)
  | MMap: forall A B (s : Syntax A) (xs : list token) v f g,
      matches_without forbidden A s xs v ->
      matches_without forbidden B (Map f g s) xs (f v)
  | MVar: forall (x : id) (xs : list token) a,
      ~ In x forbidden ->
      matches_without forbidden (get_type x) (e x) xs a ->
      matches_without forbidden (get_type x) (Var x) xs a.

Hint Constructors matches_without: matches.

Notation matches := (matches_without nil).

Arguments matches_without forbidden { A }.

(*** Inversions on Matches ***)

Lemma matches_without_inversion:
  forall forbidden A (s: Syntax A) xs v,
    matches_without forbidden s xs v ->
    match s as x in Syntax X return X -> Prop with
    | Failure B => fun _ => False
    | @Epsilon B v' =>
      fun v =>
        xs = nil /\
        v = v'
    | @Elem tc =>
      fun v =>
        xs = [ v ] /\
        class v = tc
    | @Disjunction B s1 s2 =>
      fun v =>
        matches_without forbidden s1 xs v \/
        matches_without forbidden s2 xs v
    | @Sequence B1 B2 s1 s2 =>
      fun v =>
        let v': (B1 * B2) := v in
        exists v1 v2 xs1 xs2,
          xs = xs1 ++ xs2 /\
          v' = (v1, v2) /\
          matches_without forbidden s1 xs1 v1 /\
          matches_without forbidden s2 xs2 v2
    | @Map B1 B2 f g s1 =>
      fun v =>
        exists (v': B1),
          matches_without forbidden s1 xs v' /\
          f v' = v
    | @Var x =>
      fun v =>
        ~ In x forbidden /\
        matches_without forbidden (e x) xs v
    end v.
Proof.
  induction 1; lights;
    eauto 8.
Qed.

Lemma matches_failure:
  forall forbidden A xs v,
    matches_without forbidden (Failure A) xs v ->
    False.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Lemma matches_epsilon:
  forall forbidden A xs (v1 v2: A),
    matches_without forbidden (Epsilon v1) xs v2 ->
      xs = nil /\ v1 = v2.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Lemma matches_elem:
  forall forbidden tc xs v,
    matches_without forbidden (Elem tc) xs v ->
      xs = cons v nil /\ class v = tc.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Lemma matches_sequence:
  forall forbidden B1 B2 s1 s2 xs v,
    matches_without forbidden (Sequence s1 s2) xs v ->
    exists (v1: B1) (v2: B2) xs1 xs2,
      v = (v1, v2) /\
      xs = xs1 ++ xs2 /\
      matches_without forbidden s1 xs1 v1 /\
      matches_without forbidden s2 xs2 v2.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); repeat light || destruct v;
    eauto 8.
Qed.

Lemma matches_disjunction:
  forall forbidden A s1 s2 xs (v: A),
    matches_without forbidden (Disjunction s1 s2) xs v ->
      matches_without forbidden s1 xs v  \/
      matches_without forbidden s2 xs v.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Lemma matches_map:
  forall forbidden A B s f g xs v,
    matches_without forbidden (@Map A B f g s) xs v ->
    exists v',
      matches_without forbidden s xs v' /\
      f v' = v.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Lemma matches_var:
  forall forbidden x xs v,
    matches_without forbidden (Var x) xs v ->
      matches_without forbidden (e x) xs v /\
      ~In x forbidden.
Proof.
  intros.
  pose proof (matches_without_inversion _ _ _ _ _ H); lights.
Qed.

Ltac invert_matches :=
  match goal with
  | H: matches_without _ (Failure _) _ _ |- _ => apply matches_failure in H
  | H: matches_without _ (Epsilon _) _ _ |- _ => apply matches_epsilon in H
  | H: matches_without _ (Elem _) _ _ |- _ => apply matches_elem in H
  | H: matches_without _ (Sequence _ _) _ _ |- _ => apply matches_sequence in H
  | H: matches_without _ (Disjunction _ _) _ _ |- _ => apply matches_disjunction in H
  | H: matches_without _ (Map _ _ _) _ _ |- _ => apply matches_map in H
  | H: matches_without _ (Var _) _ _ |- _ => apply matches_var in H
  end.

(*** Theorems about Matching. ***)

Lemma matches_either : forall forbidden A (s: Syntax A) xs x v,
  matches_without forbidden s xs v ->
  (matches_without (x :: forbidden) s xs v   \/
    (exists xs' v', sublist xs' xs /\ matches_without (x :: forbidden) (e x) xs' v')).
Proof.
  induction 1; repeat light || decide_id_equalities;
    eauto using remove_id_preserve_others with matches sublist lights.
Qed.

Ltac matches_either :=
  match goal with
  | x: id, H: matches_without ?forbidden ?s ?xs ?v |- _ =>
    is_var forbidden;
    poseNew (Mark H "matches_either");
    pose proof (matches_either _ _ _ _ x _ H)
  end.

Theorem matches_forget_x :
  forall forbidden x xs v,
    matches_without forbidden (e x) xs v ->
    exists xs' v',
      sublist xs' xs /\
      matches_without (x :: forbidden) (e x) xs' v'.
Proof.
  repeat light || matches_either; eauto with sublist.
Qed.

Ltac matches_forget_x :=
  match goal with
  | H: matches (e ?x) ?xs ?v |- _ =>
    poseNew (Mark H "matches_forget_x");
    pose proof (matches_forget_x _ _ _ _ H)
  end.

Theorem matches_incl :
  forall A forbidden forbidden' (s: Syntax A) xs v,
    incl forbidden' forbidden ->
    matches_without forbidden s xs v ->
    matches_without forbidden' s xs v.
Proof.
  induction 2; eauto with matches.
Qed.

Ltac matches_sub_names :=
  match goal with
  | H1: incl ?f' ?f, H2: matches ?f ?s ?xs ?v |- _ =>
    poseNew (Mark (H1, H2) "matches_sub_names");
    pose proof (matches_incl _ _ _ _ _ _ H1 H2)
  end.

Lemma matches_same:
  forall A (s: Syntax A) xs ys v,
    matches s xs v ->
    xs = ys ->
    matches s ys v.
Proof.
  lights.
Qed.

Lemma matches_xs_seq:
  forall A B (s1: Syntax A) (s2: Syntax B) xs v1 v2,
    matches s1 nil v1 ->
    matches s2 xs v2 ->
    matches (Sequence s1 s2) xs (v1, v2).
Proof.
  intros; eauto using matches_same with matches lights.
Qed.

Hint Resolve matches_xs_seq: matches.

Lemma matches_xs_nil:
  forall A B (s1: Syntax A) (s2: Syntax B) xs v1 v2,
    matches s1 xs v1 ->
    matches s2 nil v2 ->
    matches (Sequence s1 s2) xs (v1, v2).
Proof.
  intros; eauto using matches_same with matches lists.
Qed.

Hint Resolve matches_xs_nil: matches.

Lemma matches_t_xs_seq:
  forall (A B : Type) (s1 : Syntax A) (s2 : Syntax B) t xs1 xs2 v1 v2,
    matches s1 (t :: xs1) v1 ->
    matches s2 xs2 v2 ->
    matches (Sequence s1 s2) (t :: xs1 ++ xs2) (v1, v2).
Proof.
  eauto using matches_same with matches.
Qed.

Hint Resolve matches_t_xs_seq: matches.

Lemma matches_prepend_seq:
  forall (A B : Type) (s1 : Syntax A) (s2 : Syntax B) xs1 xs2 xs2' v1 v2,
    matches s1 xs1 v1 ->
    matches s2 (xs2 ++ xs2') v2 ->
    matches (Sequence s1 s2) ((xs1 ++ xs2) ++ xs2') (v1, v2).
Proof.
  repeat light || rewrite <- app_assoc; eauto with matches.
Qed.

Hint Resolve matches_prepend_seq: matches.

Lemma matches_append_seq:
  forall (A B : Type) (s1 : Syntax A) (s2 : Syntax B) xs1 xs2 xs2' v1 v2,
    matches s1 (xs1 ++ xs2) v1 ->
    matches s2 xs2' v2 ->
    matches (Sequence s1 s2) (xs1 ++ xs2 ++ xs2') (v1, v2).
Proof.
  repeat light || rewrite app_assoc; eauto with matches.
Qed.

Hint Resolve matches_append_seq: matches.

Lemma matches_append_nil:
  forall A (s : Syntax A) xs v,
    matches s xs v ->
    matches s (xs ++ []) v.
Proof.
  repeat light || lists.
Qed.

Hint Resolve matches_append_nil: matches.

Lemma matches_elem_witness:
  forall tc,
    matches (Elem tc) (proj1_sig (token_witness tc) :: nil) (proj1_sig (token_witness tc)).
Proof.
  intros.
  destruct (token_witness tc); lights; eauto with matches.
Qed.

Hint Resolve matches_elem_witness: matches.

Lemma matches_without_matches:
  forall A (s: Syntax A) forbidden ts v,
    matches_without forbidden s ts v ->
    matches s ts v.
Proof.
  eauto using matches_incl, incl_nil.
Qed.

Hint Immediate matches_without_matches: matches.
