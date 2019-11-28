Require Import Coq.Program.Tactics.

Require Export Parser.Tactics.

Definition or_else { A } (opt1 opt2: option A): option A :=
  match opt1 with
  | None => opt2
  | Some _ => opt1
  end.

Definition option_flat_map { A B } (f: A -> option B) (opt: option A): option B :=
  match opt with
  | None => None
  | Some a => f a
  end.

Definition is_some { A } (opt: option A): Prop :=
  match opt with
  | None => False
  | Some _ => True
  end.

Definition is_some_b { A } (opt: option A): bool :=
  match opt with
  | None => false
  | Some _ => true
  end.

Lemma is_some_dec { A } (opt: option A): { is_some opt } + { ~ is_some opt }.
Proof.
  destruct opt; lights.
Qed.

Ltac clear_some_dec :=
  match goal with
  | H: is_some_dec _ = _ |- _ => clear H
  end.

Lemma is_some_some { A }:
  forall (opt: option A) (a: A),
    opt = Some a ->
    is_some opt.
Proof.
  destruct opt; lights.
Qed.

Definition opt_forall { A } (opt: option A) (p: A -> Prop): Prop :=
  match opt with
  | None => True
  | Some a => p a
  end.

Program Definition get_option { A } (opt: option A) (pre: is_some opt): A :=
  match opt with
  | None => _
  | Some v => v
  end.

Fail Next Obligation. (* no more obligations for get_option *)

Ltac options :=
  unfold or_else in * ||
  unfold option_map in * ||
  unfold is_some_b in * ||
  unfold is_some in * ||
  unfold opt_forall in * ||
  unfold get_option in * ||
  unfold option_flat_map in *.

Lemma get_option_some:
  forall T (opt: option T) (v: T) pre,
    opt = Some v ->
    get_option opt pre = v.
Proof.
  destruct opt; lights.
Qed.
