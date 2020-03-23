Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.NetworkSimpleLemmas.

Open Scope nat_scope.

Opaque PeanoNat.Nat.eq_dec.

Lemma unchanged_cells_smaller:
  forall A (s: Syntax A) G (descr: Description G) k N k',
    k' < k -> cells (make_network' s descr k N) k' = cells N k'.
Proof.
  induction s;
    repeat light || destruct_match;
    eauto using eq_trans with lia.
Qed.

Lemma unchanged_cells_larger:
  forall A (s: Syntax A) G (descr: Description G) k N k',
    k' >= k + syntax_size s -> cells (make_network' s descr k N) k' = cells N k'.
Proof.
  induction s;
    repeat light || destruct_match;
    eauto using eq_trans with lia.
Qed.

Lemma unchanged_inputs_smaller:
  forall A (s: Syntax A) G (descr: Description G) k N k',
    k' < k -> inputs (make_network' s descr k N) k' = inputs N k'.
Proof.
  induction s;
    repeat light || destruct_match;
    eauto using eq_trans with lia.
Qed.

Lemma unchanged_inputs_larger:
  forall A (s: Syntax A) G (descr: Description G) k N k',
    k' >= k + syntax_size s -> inputs (make_network' s descr k N) k' = inputs N k'.
Proof.
  induction s;
    repeat light || destruct_match;
    eauto using eq_trans with lia.
Qed.

Definition good_inputs
             { A } (s: Syntax A) { G } (descr: Description G) (N: Network) k (b1 b2: nat): Prop :=
  match s with
  | Epsilon _ => inputs N k = []
  | Failure _ => inputs N k = []
  | Elem _ => inputs N k = []
  | Disjunction s1 s2 =>
      b1 < S k /\
      S (k + syntax_size s1) < b2 /\
      inputs N k = [ S k; S (k + syntax_size s1) ] /\
      map (cells N) (inputs N k) = [
        make_cell_with_state s1 descr None; make_cell_with_state s2 descr None
      ]
  | Sequence s1 s2 =>
      b1 <= S k /\
      S (k + syntax_size s1) < b2 /\
      inputs N k = [ S k; S (k + syntax_size s1) ] /\
      map (cells N) (inputs N k) = [
        make_cell_with_state s1 descr None; make_cell_with_state s2 descr None
      ]
  | Map f g s' =>
      b1 <= S k /\ S k < b2 /\
      inputs N k = [ S k ] /\
      map (cells N) (inputs N k) = [
        make_cell_with_state s' descr None
      ]
  | Var x =>
      inputs N k = [ sum_sizes_until x ]
  end.

Definition good_cell { G } (descr: Description G) (N: Network) (k: nat) (b1 b2: nat): Prop :=
  exists A (s: Syntax A),
    cells N k = make_cell_with_state s descr None /\
    good_inputs s descr N k b1 b2.

Definition good_cells { G } (descr: Description G) (N: Network) (num_cells: nat) (b1 b2: nat): Prop :=
  forall k, k < num_cells -> good_cell descr N k b1 b2.

Opaque make_cell_with_state.

Lemma good_cell_make_cell:
  forall G (descr: Description G) N k b1 b2,
    good_cell descr N k b1 b2 ->
    exists A (s: Syntax A), cells N k = make_cell_with_state s descr None.
Proof.
  unfold good_cell; lights; eauto.
Qed.

Ltac good_cell_make_cell_with_state :=
  match goal with
  | H: good_cell ?descr ?N ?k ?b  |- _ =>
    poseNew (Mark H "good_cell_make_cell");
    pose proof (good_cell_make_cell _ _ _ _ H)
  end.

Definition good_cells_make_network'_prop { A } (s: Syntax A): Prop :=
  forall G (descr: Description G) k N,
    forall k',
      k <= k' ->
      k' < k + syntax_size s ->
      good_cell descr (make_network' s descr k N) k' k (k + syntax_size s).

Ltac choose_syntax :=
  match goal with
  | |- exists _ _, make_cell_with_state ?s' _ _ = make_cell_with_state _ _ _ /\ _ =>
    eexists; exists s'
  | H: ?c = make_cell_with_state ?s _ _ |-
     exists _ _, ?c = _ /\ _ =>
       eexists; exists s
  end.

Lemma good_cell_epsilon:
  forall A (a : A) G (descr : Description G) N k,
    good_cell descr (set_cell_with_inputs N k (make_cell_with_state (Epsilon a) descr None) []) k k (k + 1).
Proof.
  unfold good_cell;
    repeat light || destruct_match || choose_syntax.
Qed.

Lemma good_cells_make_network'_epsilon:
  forall A (a : A), good_cells_make_network'_prop (Epsilon a).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || destruct_match || smaller_greater;
    eauto using good_cell_epsilon;
    try lia.
Qed.

Lemma good_cell_failure:
  forall A G (descr : Description G) N k,
    good_cell descr (set_cell_with_inputs N k (make_cell_with_state (Failure A) descr None) []) k k (k + 1).
Proof.
  unfold good_cell;
    repeat light || destruct_match || choose_syntax.
Qed.

Lemma good_cells_make_network'_failure:
  forall A, good_cells_make_network'_prop (Failure A).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || destruct_match || smaller_greater;
    eauto using good_cell_failure;
    try lia.
Qed.

Lemma good_cell_elem:
  forall G (descr : Description G) N k tc,
    good_cell descr (set_cell_with_inputs N k (make_cell_with_state (Elem tc) descr None) []) k k (k + 1).
Proof.
  unfold good_cell;
    repeat light || destruct_match || choose_syntax.
Qed.

Lemma good_cells_make_network'_elem:
  forall tc, good_cells_make_network'_prop (Elem tc).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || destruct_match || smaller_greater;
    eauto using good_cell_elem;
    try lia.
Qed.

Ltac use_ineq :=
  match goal with
  | H: ?k < S ?k -> _ |- _ =>
      unshelve epose proof (H _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H ]
  | H: ?k < S (?k + _) -> _ |- _ =>
      unshelve epose proof (H _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H ]
  | H: S ?k < S (?k + _) -> _ |- _ =>
      unshelve epose proof (H _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H ]
  | H: ?k <= ?k -> _ |- _ =>
      unshelve epose proof (H _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H ]
  | H1: ?k' < ?k + S ?n,
    H2: ?k' < S (?k + ?n) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' <= ?k,
    H2: S ?k' <= S ?k -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' < ?k,
    H2: ?k' < S (?k + _) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' >= ?k + S (?n1 + ?n2),
    H2: ?k' >= S (?k + ?n1 + ?n2) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' >= ?k + S (?n1 + ?n2),
    H2: ?k' >= S (?k + ?n1) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' < ?k + S (?n1 + ?n2),
    H2: ?k' < S (?k + ?n1 + ?n2) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' < ?k + S ?n -> False,
    H2: ?k' >= S (?k + ?n) -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' < ?k + S ?n -> False,
    H2: S (?k + ?n) <= ?k' -> _ |- _ =>
      unshelve epose proof (H2 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H2 ]
  | H1: ?k' <= ?k,
    H2: ?k' = ?k -> False,
    H3: S ?k' <= ?k -> _ |- _ =>
      unshelve epose proof (H3 _); [ solve [ repeat syntax_size_gt_0; lia ] | clear H3 ]
  end.

Ltac decide_smaller :=
  match goal with
  | H: ?k' < ?k + S (syntax_size ?s1 + _) |- _ =>
      poseNew (Mark (k', k, s1) "first_size");
      pose proof (Compare_dec.lt_dec k' (k + S (syntax_size s1)))
  end.

Ltac good_cells_IH :=
  match goal with
  | H: context[make_network' ?s _ _ _] |-
    context[make_network' ?s ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' =>
         poseNew (Mark (s, k') "IH");
         pose proof (H _ descr k N k')
      end
  | H: context[make_network' ?s _ _ _] |-
    context[cells (make_network' ?s ?descr ?k ?N) ?k'] =>
      poseNew (Mark (s, k') "IH");
      pose proof (H _ descr k N k')
  | H: context[make_network' ?s _ _ _] |-
    context[inputs (make_network' ?s ?descr ?k ?N) ?k'] =>
      poseNew (Mark (s, k') "IH");
      pose proof (H _ descr k N k')
  end.

Ltac decide_equality :=
  match goal with
  | H1: ?k <= ?k',
    H2: S ?k <= ?k' -> _ |- _ =>
      poseNew (Mark (k,k') "decide_equality");
      destruct (PeanoNat.Nat.eq_dec k k')
  end.

Ltac unchanged_rewrites :=
  match goal with
  | H: context[make_network' ?s] |- _ =>
    (rewrite (unchanged_cells_smaller _ s) in * by (repeat light || syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_cells_larger _ s) in * by (repeat light ||  syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_inputs_smaller _ s) in * by (repeat light ||  syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_inputs_larger _ s) in * by (repeat light ||  syntax_size_gt_0; lia))
  | |- context[make_network' ?s] =>
    (rewrite (unchanged_cells_smaller _ s) in * by (repeat light || syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_cells_larger _ s) in * by (repeat light ||  syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_inputs_smaller _ s) in * by (repeat light ||  syntax_size_gt_0; lia)) ||
    (rewrite (unchanged_inputs_larger _ s) in * by (repeat light ||  syntax_size_gt_0; lia))
  end.

Lemma good_inputs_top:
  forall A (s: Syntax A) G (descr: Description G) N k,
    good_inputs s descr (make_network' s descr k N) k k (k + syntax_size s).
Proof.
  unfold good_inputs;
    repeat light || destruct_match || unchanged_rewrites || rewrite cell_make_network' ||
           f_equal || syntax_size_gt_0;
    eauto with lia.
Qed.

Lemma good_cell_top:
  forall A (s: Syntax A) G (descr: Description G) N k,
    good_cell descr (make_network' s descr k N) k k (k + syntax_size s).
Proof.
  unfold good_cell;
    repeat light || rewrite cell_make_network' || choose_syntax;
    eauto using good_inputs_top.
Qed.

Lemma good_cell_same_bounds:
  forall G (descr: Description G) N k b1 b2 b1' b2',
    good_cells descr N k b1 b2 ->
    b1 = b1' ->
    b2 = b2' ->
    good_cells descr N k b1' b2'.
Proof.
  lights.
Qed.

Lemma still_good_inputs:
  forall A (s: Syntax A) B (s': Syntax B) G (descr : Description G) N b b' (k k': nat),
    good_inputs s' descr N k' 0 b ->
    k' < k ->
    b <= k ->
    b <= b' ->
    good_inputs s' descr (make_network' s descr k N) k' 0 b'.
Proof.
  unfold good_inputs;
    repeat light || destruct_match || unchanged_rewrites || rewrite_known_inputs ||
           invert_constructor_equalities || f_equal_constructors;
    try lia.
Qed.

Lemma still_good_cell:
  forall A (s: Syntax A) G (descr : Description G) N b b' (k k': nat),
    good_cell descr N k' 0 b ->
    k' < k ->
    b <= k ->
    b <= b' ->
    good_cell descr (make_network' s descr k N) k' 0 b'.
Proof.
  unfold good_cell; repeat light.
  unchanged_rewrites.
  rewrite_known_cells.
  choose_syntax; lights;
    eauto using still_good_inputs.
Qed.

Lemma good_inputs_set_cell_with_inputs:
  forall A (s: Syntax A) G (descr: Description G) N k k' c ks b1 b2,
    good_inputs s descr N k b1 b2 ->
    k' < b1 ->
    k <> k' ->
    good_inputs s descr (set_cell_with_inputs N k' c ks) k b1 b2.
Proof.
  unfold good_inputs;
    repeat light || destruct_match || rewrite_known_inputs || f_equal_constructors ||
           invert_constructor_equalities
    ;
    eauto with lia.
Qed.

Lemma good_cell_set_cell_with_inputs:
  forall G (descr: Description G) N k k' c ks b1 b2,
    good_cell descr N k b1 b2 ->
    k' < b1 ->
    k <> k' ->
    good_cell descr (set_cell_with_inputs N k' c ks) k b1 b2.
Proof.
  unfold good_cell;
    repeat light || destruct_match;
    eauto using good_inputs_set_cell_with_inputs.
Qed.

Ltac good_cell_set_cell_with_inputs :=
  match goal with
  | H: good_cell _ _ _ _ _ |- good_cell _ (set_cell_with_inputs ?N ?k' ?c ?ks) _ _ _ =>
    poseNew (Mark H "good_cell_set_cell_with_inputs");
    unshelve epose proof (good_cell_set_cell_with_inputs _ _ _ _ k' c ks _ _ H _ _)
  end.

Lemma good_cell_widen:
  forall G (descr: Description G) N k b1 b2 b1' b2',
    good_cell descr N k b1 b2 ->
    b1' <= b1 ->
    b2' >= b2 ->
    good_cell descr N k b1' b2'.
Proof.
  unfold good_cell, good_inputs;
    repeat light || destruct_match || rewrite_known_cells || choose_syntax;
    try lia.
Qed.

Lemma good_inputs_same:
  forall A (s: Syntax A) G (descr: Description G) N N' k b1 b2,
    good_inputs s descr N k b1 b2 ->
    inputs N' k = inputs N k ->
    (forall k', b1 <= k' -> k' < b2 -> cells N' k' = cells N k') ->
    good_inputs s descr N' k b1 b2.
Proof.
  unfold good_inputs;
    repeat light || destruct_match || map_ext_in || rewrite_any;
    eauto with lia.
Qed.

Lemma good_cell_same:
  forall G (descr: Description G) N N' k b1 b2,
    good_cell descr N k b1 b2 ->
    cells N' k = cells N k ->
    inputs N' k = inputs N k ->
    (forall k', b1 <= k' -> k' < b2 -> cells N' k' = cells N k') ->
    good_cell descr N' k b1 b2.
Proof.
  unfold good_cell;
    repeat light || destruct_match || choose_syntax || rewrite_known_cells;
    eauto using good_inputs_same.
Qed.

Lemma good_cell_disj_left:
  forall A (s1 s2 : Syntax A) G (descr : Description G) N k k',
    k < k' ->
    k' < k + S (syntax_size s1) ->
    good_cell descr (make_network' s1 descr (S k) N) k'
              (S k)
              (S k + syntax_size s1) ->
    good_cell descr (make_network' (Disjunction s1 s2) descr k N) k'
              k
              (k + S (syntax_size s1 + syntax_size s2)).
Proof.
  repeat light || destruct_match || choose_syntax || rewrite cell_make_network' ||
         map_ext_in || unchanged_rewrites ||
         rewrite_known_inputs || syntax_size_gt_0.

  apply good_cell_widen with (S k) (S (k + syntax_size s1)); eauto with lia.
  eapply good_cell_same; eauto; repeat light || destruct_match || unchanged_rewrites;
    eauto with lia.
Qed.

Lemma good_cell_disj_right:
  forall A (s1 s2 : Syntax A) G (descr : Description G) N k k',
    k + S (syntax_size s1) <= k' ->
    k' < k + S (syntax_size s1 + syntax_size s2)  ->
    good_cell descr (make_network' s2 descr (S (k + syntax_size s1))
                                   ((make_network' s1 descr (S k) N))) k'
              (S (k + syntax_size s1))
              (S (k + syntax_size s1 + syntax_size s2)) ->
    good_cell descr (make_network' (Disjunction s1 s2) descr k N) k'
              k
              (k + S (syntax_size s1 + syntax_size s2)).
Proof.
  repeat light || destruct_match || choose_syntax || rewrite cell_make_network' ||
         map_ext_in || unchanged_rewrites ||
         rewrite_known_inputs || syntax_size_gt_0.

  apply good_cell_widen with (S (k + syntax_size s1)) (S (k + syntax_size s1 + syntax_size s2));
    eauto with lia.
  eapply good_cell_same; eauto; repeat light || destruct_match || unchanged_rewrites;
    eauto with lia.
Qed.

Lemma good_cell_seq_left:
  forall A1 A2 (s1: Syntax A1) (s2 : Syntax A2) G (descr : Description G) N k k',
    k < k' ->
    k' < k + S (syntax_size s1) ->
    good_cell descr (make_network' s1 descr (S k) N) k'
              (S k)
              (S k + syntax_size s1) ->
    good_cell descr (make_network' (Sequence s1 s2) descr k N) k'
              k
              (k + S (syntax_size s1 + syntax_size s2)).
Proof.
  repeat light || destruct_match || choose_syntax || rewrite cell_make_network' ||
         map_ext_in || unchanged_rewrites ||
         rewrite_known_inputs || syntax_size_gt_0.

  apply good_cell_widen with (S k) (S (k + syntax_size s1)); eauto with lia.
  eapply good_cell_same; eauto; repeat light || destruct_match || unchanged_rewrites;
    eauto with lia.
Qed.

Lemma good_cell_seq_right:
  forall A1 A2 (s1: Syntax A1) (s2 : Syntax A2) G (descr : Description G) N k k',
    k + S (syntax_size s1) <= k' ->
    k' < k + S (syntax_size s1 + syntax_size s2)  ->
    good_cell descr (make_network' s2 descr (S (k + syntax_size s1))
                                   ((make_network' s1 descr (S k) N))) k'
              (S (k + syntax_size s1))
              (S (k + syntax_size s1 + syntax_size s2)) ->
    good_cell descr (make_network' (Sequence s1 s2) descr k N) k'
              k
              (k + S (syntax_size s1 + syntax_size s2)).
Proof.
  repeat light || destruct_match || choose_syntax || rewrite cell_make_network' ||
         map_ext_in || unchanged_rewrites ||
         rewrite_known_inputs || syntax_size_gt_0.

  apply good_cell_widen with (S (k + syntax_size s1)) (S (k + syntax_size s1 + syntax_size s2));
    eauto with lia.
  eapply good_cell_same; eauto; repeat light || destruct_match || unchanged_rewrites;
    eauto with lia.
Qed.

Lemma good_cell_map:
  forall A B (f: A -> B) g (s: Syntax A) G (descr : Description G) N k k',
    k < k' ->
    k' < k + S (syntax_size s) ->
    good_cell descr (make_network' s descr (S k) N) k'
              (S k)
              (S (k + syntax_size s)) ->
    good_cell descr (make_network' (Map f g s) descr k N) k'
              k
              (k + (S (syntax_size s))).
Proof.
  repeat light || destruct_match || choose_syntax || rewrite cell_make_network' ||
         map_ext_in || unchanged_rewrites ||
         rewrite_known_inputs || syntax_size_gt_0.

  apply good_cell_widen with (S k) (S (k + syntax_size s)); eauto with lia.
  eapply good_cell_same; eauto; repeat light || destruct_match || unchanged_rewrites;
    eauto with lia.
Qed.

Lemma good_cell_var:
  forall G (descr : Description G) N k x,
    good_cell descr (set_cell_with_inputs N k (make_cell_with_state (Var x) descr None) [ sum_sizes_until x])
              k k (k + 1).
Proof.
  unfold good_cell;
    repeat light || destruct_match || choose_syntax.
Qed.

Lemma good_cells_make_network'_var:
  forall x, good_cells_make_network'_prop (Var x).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || destruct_match || smaller_greater;
    eauto using good_cell_var;
    eauto with lia.
Qed.

Opaque make_network'.
Opaque make_cell_with_state.

Ltac disj_IH :=
  match goal with
  | H: context[make_network' ?s1 _ _ _] |-
    context[make_network' (Disjunction ?s1 ?s2) ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' _ _ =>
         poseNew (Mark (s1, k') "IH");
         pose proof (H _ descr (S k) N k')
      end
  | H: context[make_network' ?s2 _ _ _] |-
    context[make_network' (Disjunction ?s1 ?s2) ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' _ _ =>
         poseNew (Mark (s2, k') "IH");
         pose proof (H _ descr (S (k + syntax_size s1)) (make_network' s1 descr (S k) N) k')
      end
  end.

Lemma good_cells_make_network'_disj:
  forall A (s1 s2: Syntax A),
    good_cells_make_network'_prop s1 ->
    good_cells_make_network'_prop s2 ->
    good_cells_make_network'_prop (Disjunction s1 s2).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || disj_IH || use_ineq || decide_smaller || decide_equality || destruct_match ||
           apply good_cell_top;
    eauto with lia;
    try solve [ apply good_cell_disj_left; lights; eauto with lia ];
    try solve [ apply good_cell_disj_right; lights; eauto with lia ].
Qed.

Ltac seq_IH :=
  match goal with
  | H: context[make_network' ?s1 _ _ _] |-
    context[make_network' (Sequence ?s1 ?s2) ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' _ _ =>
         poseNew (Mark (s1, k') "IH");
         pose proof (H _ descr (S k) N k')
      end
  | H: context[make_network' ?s2 _ _ _] |-
    context[make_network' (Sequence ?s1 ?s2) ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' _ _ =>
         poseNew (Mark (s2, k') "IH");
         pose proof (H _ descr (S (k + syntax_size s1)) (make_network' s1 descr (S k) N) k')
      end
  end.

Lemma good_cells_make_network'_seq:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2),
    good_cells_make_network'_prop s1 ->
    good_cells_make_network'_prop s2 ->
    good_cells_make_network'_prop (Sequence s1 s2).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || seq_IH || use_ineq || decide_smaller || decide_equality || destruct_match ||
           apply good_cell_top;
    eauto with lia;
    try solve [ apply good_cell_seq_left; lights; eauto with lia ];
    try solve [ apply good_cell_seq_right; lights; eauto with lia ].
Qed.

Ltac map_IH :=
  match goal with
  | H: context[make_network' ?s _ _ _] |-
    context[make_network' (Map ?f ?g ?s) ?descr ?k ?N] =>
      match goal with
      | |- good_cell _ _ ?k' _ _ =>
         poseNew (Mark (s, k') "IH");
         pose proof (H _ descr (S k) N k')
      end
  end.

Lemma good_cells_make_network'_map:
  forall A B (f: A -> B) g (s: Syntax A),
    good_cells_make_network'_prop s ->
    good_cells_make_network'_prop (Map f g s).
Proof.
  unfold good_cells_make_network'_prop;
    repeat light || map_IH || use_ineq || decide_smaller || decide_equality || destruct_match ||
           apply good_cell_top;
    eauto with lia.
    try solve [ apply good_cell_map; lights; eauto with lia ].
Qed.

Lemma good_cells_make_network': forall A (s: Syntax A), good_cells_make_network'_prop s.
Proof.
  induction s;
    eauto using good_cells_make_network'_epsilon;
    eauto using good_cells_make_network'_failure;
    eauto using good_cells_make_network'_elem;
    eauto using good_cells_make_network'_disj;
    eauto using good_cells_make_network'_seq;
    eauto using good_cells_make_network'_map;
    eauto using good_cells_make_network'_var.
Qed.

Lemma good_cells_make_network'_2:
  forall A (s: Syntax A) G (descr: Description G) k N k',
    k <= k' ->
    k' < k + syntax_size s ->
    good_cell descr (make_network' s descr k N) k' k (k + syntax_size s).
Proof.
  repeat light || apply good_cells_make_network'.
Qed.

Lemma still_good_cell2:
  forall A (s: Syntax A) G (descr : Description G) N (k k': nat),
    (forall k', k' < k -> good_cell descr N k' 0 k) ->
    k' < k + syntax_size s ->
    good_cell descr (make_network' s descr k N) k' 0 (k + syntax_size s).
Proof.
  repeat light.

  destruct (Compare_dec.lt_dec k' k);
    repeat light || instantiate_any.

  - eapply still_good_cell; lights; eauto with lia.
  - unshelve epose proof (good_cells_make_network'_2 _ s _ descr k N k' _ _);
      lights;
      eauto using good_cell_widen with lia.
Qed.

Transparent make_network'.

Lemma good_cells_init_env_network:
  forall G (descr: Description G) k,
    k < sum_sizes vars ->
    good_cell descr (init_env_network descr) k 0 (sum_sizes vars).
Proof.
  unfold init_env_network; lights.
  match goal with
  | |- context[fold_left ?f ?l ?a] =>
    unshelve epose proof
      fold_left_invariant
        (fun N xs => forall k,
           k < sum_sizes xs ->
           good_cell descr N k 0 (sum_sizes xs))
        f l a
        _ _
  end;
    repeat light || rewrite sum_sizes_snoc in * ||
           (erewrite sum_sizes_until_prefix in * by eauto);
      try lia;
      eauto using still_good_cell2.
Qed.

Lemma good_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k < sum_sizes vars + syntax_size s ->
    good_cell descr (make_network s descr) k 0 (sum_sizes vars + syntax_size s).
Proof.
  unfold make_network;
    repeat light;
    eauto using still_good_cell2, good_cells_init_env_network.
Qed.

Transparent make_cell_with_state.

Lemma good_cell_io_type:
  forall G (descr: Description G) k N b,
    good_cell descr N k 0 b ->
    (forall x, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr None) ->
    map (fun k' => cell_type (cells N k')) (inputs N k) = input_types (cells N k).
Proof.
  unfold good_cell, good_inputs;
    repeat light || destruct_match || rewrite_known_inputs || rewrite_known_cells ||
           invert_constructor_equalities || f_equal_constructors;
    eauto using cell_type_node_type.

  instantiate_forall;
    repeat light || destruct_match || rewrite_known_cells;
    eauto using cell_type_node_type.
Qed.
