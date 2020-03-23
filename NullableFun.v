Require Import Coq.Strings.String.

Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.
Require Export Parser.DescriptionInd.
Require Export Parser.Matches.
Require Export Parser.NullableDescr.
Require Export Parser.NullableInd.
Require Export Parser.MonotonicRules.

Definition nullable_fun { A }: Syntax A -> option A := build_fun nullable_descr.

Lemma nullable_fun_some:
  forall A (s: Syntax A) v,
    nullable_fun s = Some v ->
    matches s nil v.
Proof.
  unfold nullable_fun; intros.
  pose proof (fun_soundness _ nullable_descr _ s v);
    repeat light || destruct_match.
  apply nullable_ind_sound in H1; auto.
Qed.

Lemma monotonic_nullable: monotonic_descr nullable_descr.
Proof.
  unfold monotonic_descr, nullable_descr;
    repeat light;
    eauto using monotonic_rule_1_map;
    eauto using monotonic_rule_2_disj;
    eauto using monotonic_rule_2_combine;
    eauto using monotonic_rule_1_id.
Qed.

Lemma nullable_fun_none:
  forall A (s: Syntax A) v,
    nullable_fun s = None ->
    matches s nil v ->
    False.
Proof.
  unfold nullable_fun; intros.
  apply nullable_ind_complete in H0; unfold nullable_ind in *; lights.
  pose proof (fun_completeness _ nullable_descr _ s v H0  monotonic_nullable);
    repeat light || destruct_match || options.
Qed.

Lemma nullable_fun_none2:
  forall A (s: Syntax A),
    nullable_fun s = None ->
    (forall v, ~ matches s nil v).
Proof.
  eauto using nullable_fun_none.
Qed.

Ltac nullable_fun_spec :=
  match goal with
  | H: nullable_fun ?s = Some _ |- _ => apply nullable_fun_some in H
  | H1: nullable_fun ?s = None,
    H2: matches ?s nil ?v |- _ =>
    apply (False_ind _ (nullable_fun_none _ _ _ H1 H2))
  | H: nullable_fun ?s = None |- _ =>
    poseNew (Mark H "nullable_fun_none");
    pose proof (nullable_fun_none2 _ _ H)
  end.

Lemma matches_nil_is_some_nullable:
  forall A (s: Syntax A) v,
    matches s [] v ->
    is_some (nullable_fun s).
Proof.
  repeat light || options || destruct_match || nullable_fun_spec; eauto.
Qed.

Ltac decide_nullable_one s :=
  poseNew (Mark s "decide_nullable");
  let N := fresh "N" in
  destruct (nullable_fun s) eqn:N.

Ltac decide_nullable_any :=
  match goal with
  | s: Syntax _ |- _ => decide_nullable_one s
  end.

Ltac destruct_not_nullable :=
  match goal with
  | H1: nullable_fun _ = None, H2: matches _ ?ts _ |- _ =>
    let TS := fresh "TS" in
    tryif is_cons ts then fail else destruct ts eqn:TS
  end.
