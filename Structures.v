Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.

Require Export Parser.List.

(*** Tokens and Identifiers ***)

Parameter token: Type.
Parameter id: Type.
Parameter token_class: Type.

Parameter class_eq_dec: forall n m: token_class, { n = m } + { ~ (n = m) }.
Parameter id_eq_dec: forall n m: id, { n = m } + { ~ (n = m) }.

(* we assume a fixed number of token_classes *)
Parameter token_classes: list token_class.
Axiom all_token_classes: forall k, In k token_classes.

Definition names: Type := list id.

(* we assume a fixed number of variable identifiers *)
Parameter vars: names.
Axiom all_vars: forall x, In x vars.
Axiom NoDup_vars: NoDup vars.

Program Fixpoint get_index' l x (pre: In x l): nat :=
  match l with
  | [] => _
  | y :: ys =>
    if (id_eq_dec x y)
    then 0
    else S (get_index' ys x _)
  end.

Solve Obligations with repeat light.

Fail Next Obligation. (* no more obligations for get_index' *)

Definition get_index x := get_index' vars x (all_vars x).

Lemma get_index'_lt:
  forall l x pre, get_index' l x pre < length l.
Proof.
  induction l; repeat light || destruct_match;
    eauto using Lt.lt_n_S;
    lia.
Qed.

Lemma get_index_lt:
  forall x, get_index x < length vars.
Proof.
  unfold get_index; eauto using get_index'_lt.
Qed.

Ltac get_index_lt :=
  match goal with
  | x: id |- _ =>
    poseNew (Mark x "get_index_lt");
    pose proof (get_index_lt x)
  end.

(*** Global Types for Variables ***)

Parameter get_type: id -> Type.

(*** Syntaxes ***)

Inductive Syntax: Type -> Type :=
  | Epsilon A : A -> Syntax A
  | Failure A : Syntax A
  | Elem : token_class -> Syntax token
  | Disjunction A : Syntax A -> Syntax A -> Syntax A
  | Sequence A B : Syntax A -> Syntax B -> Syntax (A * B)
  | Map A B (f: A -> B) (g: B -> list A): Syntax A -> Syntax B
  | Var (x: id): Syntax (get_type x).

Arguments Epsilon { A }.
Arguments Disjunction { A }.
Arguments Sequence { A } { B }.
Arguments Map { A } { B }.

Fixpoint syntax_size { A } (s: Syntax A): nat :=
  match s with
  | Epsilon _ => 1
  | Failure _ => 1
  | Elem _ => 1
  | Disjunction s1 s2 => 1 + syntax_size s1 + syntax_size s2
  | Sequence s1 s2 => 1 + syntax_size s1 + syntax_size s2
  | Map _ _ s => 1 + syntax_size s
  | Var _ => 1
  end.

Fixpoint var_in { A } (x: id) (s: Syntax A): Prop :=
  match s with
  | Epsilon _ => False
  | Failure _ => False
  | Elem _ => False
  | Disjunction s1 s2 => var_in x s1 \/ var_in x s2
  | Sequence s1 s2 => var_in x s1 \/ var_in x s2
  | Map _ _ s => var_in x s
  | Var y => x = y
  end.

(*** Global Environment ***)

Definition env := forall (x: id), Syntax (get_type x).
Parameter e: env.
Parameter class: token -> token_class.
Parameter token_witness: forall (tc: token_class), { t: token | class t = tc }.

Lemma class_token_witness:
  forall tc, class (proj1_sig (token_witness tc)) = tc.
Proof.
  intros.
  destruct (token_witness tc); auto.
Qed.

Hint Resolve class_token_witness: matches.


Fixpoint sum_sizes (l: list id): nat :=
  match l with
  | [] => 0
  | x :: xs => syntax_size (e x) + sum_sizes xs
  end.

Program Fixpoint sum_sizes_until' (l: list id) (x: id) (pre: In x l): nat :=
  match l with
  | [] => _
  | y :: ys => if id_eq_dec x y then 0 else syntax_size (e y) + sum_sizes_until' ys x _
  end.

Solve Obligations with lights.

Fail Next Obligation. (* no more obligations for `sum_sizes_until` *)

Definition sum_sizes_until x := sum_sizes_until' vars x (all_vars x).

Lemma sum_sizes_until_prefix':
  forall l1 x l2 pre,
    ~ In x l1 ->
    sum_sizes_until' (l1 ++ x :: l2) x pre = sum_sizes l1.
Proof.
  induction l1;
    repeat light || destruct_match || destruct_or || instantiate_any; eauto with lia.
Qed.

Lemma vars_not_in_prefix:
  forall l1 l2 x,
    vars = l1 ++ x :: l2 ->
    In x l1 ->
    False.
Proof.
  intros; apply not_in_prefix with _ l1 l2 x; auto.
  - rewrite <- H; exact NoDup_vars.
Qed.

Lemma sum_sizes_until_prefix:
  forall l1 x l2,
    vars = l1 ++ x :: l2 ->
    sum_sizes_until x = sum_sizes l1.
Proof.
  unfold sum_sizes_until; repeat light.
  generalize (all_vars x).
  rewrite H; lights.
  eapply sum_sizes_until_prefix';
    eauto using vars_not_in_prefix.
Qed.

Lemma sum_sizes_append:
  forall l1 l2,
    sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof.
  induction l1; repeat light || instantiate_forall; eauto with lia.
Qed.

Lemma sum_sizes_snoc:
  forall l b,
    sum_sizes (l ++ [b]) = sum_sizes l + syntax_size (e b).
Proof.
  repeat light || rewrite sum_sizes_append in *.
Qed.

Lemma syntax_size_gt_0:
  forall A (s: Syntax A), syntax_size s > 0.
Proof.
  induction s; cbn; lia.
Qed.

Ltac syntax_size_gt_0 :=
  match goal with
  | s: Syntax _ |- _ =>
    poseNew (Mark s "syntax_size_gt_0");
    pose proof (syntax_size_gt_0 _ s)
  end.

Definition is_var { A } (s: Syntax A): Prop :=
  match s with
  | Var _ => True
  | _ => False
  end.

Lemma sum_sizes_until'_sum_sizes:
  forall l x pre,
    sum_sizes_until' l x pre < sum_sizes l.
Proof.
  induction l;
    repeat light || destruct_match || destruct_or || instantiate_forall;
      pose proof (syntax_size_gt_0 _ (e a));
      try lia.
Qed.

Lemma sum_sizes_until_sum_sizes:
  forall x,
    sum_sizes_until x < sum_sizes vars.
Proof.
  intros;
    apply sum_sizes_until'_sum_sizes.
Qed.

Lemma sum_sizes_until_prefix2:
  forall l l' l'' x pre pre',
    l'' = l ++ l' ->
    sum_sizes_until' l x pre = sum_sizes_until' l'' x pre'.
Proof.
  induction l;
    repeat light || destruct_match || destruct_or || instantiate_forall.
Qed.

Lemma sum_sizes_until_prefix3:
  forall l l' x,
    vars = l ++ l' ->
    In x l ->
    sum_sizes_until x < sum_sizes l.
Proof.
  unfold sum_sizes_until;
    repeat light.

  unshelve erewrite <- (sum_sizes_until_prefix2 l l' vars);
    eauto using sum_sizes_until'_sum_sizes.
Qed.

Lemma sum_sizes_until_sum_sizes2:
  forall x n, sum_sizes_until x < sum_sizes vars + n.
Proof.
  intros.
  pose proof (sum_sizes_until_sum_sizes x); eauto with lia.
Qed.
