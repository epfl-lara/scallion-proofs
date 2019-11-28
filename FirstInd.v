Require Import Coq.Lists.List.
Import ListNotations.

Require Import Parser.Structures.
Require Import Parser.Option.
Require Import Parser.List.
Require Import Parser.Description.
Require Import Parser.DescriptionInd.
Require Import Parser.CommonRules.
Require Import Parser.NullableFun.
Require Import Parser.ProductiveFun.
Require Import Parser.Matches.
Require Import Parser.Tactics.
Require Import Parser.HList.

Require Export Parser.FirstDescr.

Definition first_ind { A } (s: Syntax A) (k: token_class): Prop :=
  descr_ind (first_descr k) s tt.

Lemma first_ind_sound:
  forall A (s: Syntax A) k,
    first_ind s k ->
    exists x xs v, matches s (x :: xs) v /\ class x = k.
Proof.
  induction 1;
    repeat light || lists || instantiate_any || destruct_match || rules ||
           nullable_fun_spec || productive_fun_spec;
    eauto 10 with matches.
Qed.

Lemma first_ind_complete:
  forall A (s: Syntax A) t ts v,
    matches s (t :: ts) v ->
    first_ind s (class t).
Proof.
  unfold first_ind; intros.
  remember (t :: ts) as xs.
  revert dependent t.
  revert dependent ts.
  induction H;
    repeat light || lists || app_cons_destruct; eauto 3 with descr_ind lights.

  - eapply ElemInd; repeat light || lists || destruct_match.
  - apply SeqInd2 with right_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec; eauto.
  - apply SeqInd1 with left_rule tt;
      repeat light || lists || destruct_match || nullable_fun_spec || productive_fun_spec || invert_constructor_equalities; eauto.
Qed.
