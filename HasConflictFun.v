Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Matches.
Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.
Require Export Parser.MonotonicRules.
Require Export Parser.HasConflictInd.

Definition has_conflict_fun' { A } (s: Syntax A): option unit :=
  build_fun has_conflict_descr s.

Definition has_conflict_fun { A } (s: Syntax A): bool :=
  is_some_b (has_conflict_fun' s).

Definition ll1_fun { A } (s: Syntax A): bool:= negb (has_conflict_fun s).

Lemma monotonic_has_conflict: monotonic_descr has_conflict_descr.
Proof.
  unfold monotonic_descr;
    repeat light || lists || destruct_match;
    eauto using monotonic_rule_1_map;
    eauto using monotonic_rule_2_disj;
    eauto using monotonic_rule_2_combine;
    eauto using monotonic_rule_2_left;
    eauto using monotonic_rule_2_right;
    eauto using monotonic_rule_2_some;
    eauto using monotonic_rule_1_id.
Qed.

Lemma ll1_fun_false:
  forall A (s: Syntax A),
    ll1_fun s = false ->
    has_conflict_ind s.
Proof.
  unfold ll1_fun, has_conflict_fun, has_conflict_fun';
    repeat light || bools || options || destruct_match.

  pose proof (fun_soundness _ _ _ _ _ matched); repeat light || destruct_unit.
Qed.

Lemma ll1_fun_true:
  forall A (s: Syntax A),
    ll1_fun s = true ->
    ~has_conflict_ind s.
Proof.
  unfold ll1_fun, has_conflict_fun, has_conflict_fun';
    repeat light || bools || options || destruct_match.

  unfold has_conflict_ind in *.
  unshelve epose proof (fun_completeness _ _ _ _ _ H0 monotonic_has_conflict);
    repeat light || destruct_unit || options || destruct_match.
Qed.
