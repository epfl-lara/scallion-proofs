Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.
Require Export Parser.Matches.
Require Export Parser.MonotonicRules.
Require Export Parser.FirstInd.

Definition first_fun' { A } (k: token_class): Syntax A -> option unit :=
  build_fun (first_descr k).

Definition first_fun { A } (s: Syntax A): list token_class :=
  filter (fun k => is_some_b (first_fun' k s)) token_classes.

Lemma monotonic_first: forall k, monotonic_descr (first_descr k).
Proof.
  unfold monotonic_descr, first_descr;
    repeat light || lists || destruct_match;
    eauto using monotonic_rule_1_map;
    eauto using monotonic_rule_2_disj;
    eauto using monotonic_rule_2_combine;
    eauto using monotonic_rule_2_left;
    eauto using monotonic_rule_2_right;
    eauto using monotonic_rule_1_id.
Qed.

Lemma first_fun_correct:
  forall A (s: Syntax A) k,
    In k (first_fun s) <->
    first_ind s k.
Proof.
  unfold first_fun, first_fun', first_ind;
    repeat rewrite filter_In in * || light || options || destruct_match || destruct_unit;
    auto using all_token_classes.
  - pose proof (fun_soundness _ (first_descr k) _ s tt); lights.
  - unshelve epose proof (fun_completeness _ (first_descr k) _ s tt _ (monotonic_first k)); repeat light || options || destruct_match.
Qed.

Lemma first_fun_sound:
  forall A (s: Syntax A) k,
    In k (first_fun s) ->
    exists x xs v, get_kind x = k /\ matches s (x :: xs) v.
Proof.
  intros; rewrite first_fun_correct in *;
    eauto using first_ind_sound.
Qed.

Lemma first_fun_complete:
  forall A (s: Syntax A) x xs v,
    matches s (x :: xs) v ->
    In (get_kind x) (first_fun s).
Proof.
  intros; rewrite first_fun_correct;
    eauto using first_ind_complete.
Qed.

Lemma first_fun_spec:
  forall A (s: Syntax A) k,
    In k (first_fun s) <->
    exists t ts v,
      get_kind t = k /\
      matches s (t :: ts) v.
Proof.
  repeat light || apply_anywhere first_fun_sound;
    eauto using first_fun_complete.
Qed.

Lemma first_fun_epsilon:
  forall A (a: A) k,
    In k (first_fun (Epsilon a)) ->
    False.
Proof.
  repeat light || apply_anywhere first_fun_sound || invert_matches.
Qed.

Lemma first_fun_disj:
  forall A (s1 s2: Syntax A) k,
    In k (first_fun (Disjunction s1 s2)) ->
      In k (first_fun s1) \/ In k (first_fun s2).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches;
    eauto 6 with lights.
Qed.

Lemma first_fun_disj_l:
  forall A (s1 s2: Syntax A) k,
    In k (first_fun s1) ->
    In k (first_fun (Disjunction s1 s2)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_disj_r:
  forall A (s1 s2: Syntax A) k,
    In k (first_fun s2) ->
    In k (first_fun (Disjunction s1 s2)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_seq_l:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k ts v,
    In k (first_fun s1) ->
    matches s2 ts v ->
    In k (first_fun (Sequence s1 s2)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_seq_r:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k v,
    In k (first_fun s2) ->
    matches s1 [] v ->
    In k (first_fun (Sequence s1 s2)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_seq:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k,
    In k (first_fun (Sequence s1 s2)) ->
      (In k (first_fun s1) /\ (exists ts v, matches s2 ts v)) \/
      (In k (first_fun s2) /\ (exists v, matches s1 [] v)).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches ||
         app_cons_destruct || invert_constructor_equalities;
    eauto 9 with lights.
Qed.

Lemma first_fun_eps_seq:
  forall A1 A2 (a: A1) (s2: Syntax A2) k,
    In k (first_fun s2) ->
    In k (first_fun (Sequence (Epsilon a) s2)).
Proof.
  eauto using first_fun_seq_r with matches.
Qed.

Lemma first_fun_eps_seq2:
  forall A1 A2 (a: A1) (s2: Syntax A2) k,
    In k (first_fun (Sequence (Epsilon a) s2)) ->
    In k (first_fun s2).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches || invert_constructor_equalities;
    eauto with matches.
Qed.

Lemma first_fun_map:
  forall A B (f: A -> B) g (s: Syntax A) k,
    In k (first_fun s) ->
    In k (first_fun (Map f g s)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_map2:
  forall A B (f: A -> B) g (s: Syntax A) k,
    In k (first_fun (Map f g s)) ->
    In k (first_fun s).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches;
    eauto.
Qed.

Lemma first_fun_var:
  forall x k,
    In k (first_fun (e x)) ->
    In k (first_fun (Var x)).
Proof.
  repeat light || rewrite first_fun_spec in *;
    eauto 6 with matches lights.
Qed.

Lemma first_fun_var2:
  forall x k,
    In k (first_fun (Var x)) ->
    In k (first_fun (e x)).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches;
    eauto.
Qed.

Lemma first_fun_seq_monotone_l:
  forall A B (s1 s2: Syntax A) (s: Syntax B) k,
    (forall v, matches s1 [] v -> exists v', matches s2 [] v') ->
    (forall k, In k (first_fun s1) -> In k (first_fun s2)) ->
    In k (first_fun (Sequence s1 s)) ->
    In k (first_fun (Sequence s2 s)).
Proof.
  repeat light || rewrite first_fun_spec in * || invert_matches || app_cons_destruct ||
         invert_constructor_equalities || instantiate_any;
    eauto 7 with matches.

  unshelve epose proof (H0 (get_kind t0) _);
    repeat light || rewrite first_fun_spec in *;
    eauto 7 with matches.
Qed.

Hint Resolve first_fun_disj_l: first_fun.
Hint Resolve first_fun_disj_r: first_fun.
Hint Resolve first_fun_seq_l: first_fun.
Hint Resolve first_fun_seq_r: first_fun.
Hint Resolve first_fun_map: first_fun.
Hint Resolve first_fun_var: first_fun.
Hint Resolve first_fun_eps_seq: first_fun.

Hint Immediate first_fun_eps_seq2: first_fun.
Hint Immediate first_fun_map2: first_fun.
Hint Immediate first_fun_var2: first_fun.
Hint Immediate first_fun_epsilon: first_fun.
