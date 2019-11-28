Require Export Parser.Monotonicity.
Require Export Parser.CommonRules.

Lemma monotonic_rule_1_map:
  forall A B (f: A -> B),
    monotonic_rule_1 (map_rule f).
Proof.
  unfold monotonic_rule_1, are_some_are_some_1, is_some_is_some, map_rule;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_2_disj:
  forall A, monotonic_rule_2 (@disj_rule A).
Proof.
  unfold monotonic_rule_2, are_some_are_some_2, is_some_is_some, disj_rule;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_2_combine:
  forall A1 A2 A (f: A1 -> A2 -> A), monotonic_rule_2 (combine_rule f).
Proof.
  unfold monotonic_rule_2, are_some_are_some_2, is_some_is_some, combine_rule;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_1_id:
  forall A, monotonic_rule_1 (@id_rule A).
Proof.
  unfold monotonic_rule_1, are_some_are_some_1, is_some_is_some, combine_rule;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_2_left:
  forall A1 A2, monotonic_rule_2 (@left_rule A1 A2).
Proof.
  unfold monotonic_rule_2, are_some_are_some_2, is_some_is_some;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_2_right:
  forall A1 A2, monotonic_rule_2 (@right_rule A1 A2).
Proof.
  unfold monotonic_rule_2, are_some_are_some_2, is_some_is_some;
    repeat light || options || destruct_match.
Qed.

Lemma monotonic_rule_2_some:
  forall A1 A2 A (a: A), monotonic_rule_2 (@some_rule (A1 :: A2 :: nil) A a).
Proof.
  unfold monotonic_rule_2, are_some_are_some_2, is_some_is_some;
    repeat light || options || destruct_match.
Qed.
