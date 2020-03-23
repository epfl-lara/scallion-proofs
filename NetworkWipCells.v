Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.

Require Export Parser.DescriptionInd.
Require Export Parser.NetworkGoodCells.
Require Export Parser.NetworkProperties.

Opaque Nat.eq_dec.

Definition wip_inputs
             { A } (s: Syntax A) { G } (descr: Description G) (N: Network) k (b1 b2: nat): Prop :=
  match s with
  | Epsilon _ => inputs N k = []
  | Failure _ => inputs N k = []
  | Elem _ => inputs N k = []
  | Disjunction s1 s2 => exists opt1 opt2,
      b1 < S k /\
      S (k + syntax_size s1) < b2 /\
      inputs N k = [ S k; S (k + syntax_size s1) ] /\
      map (cells N) (inputs N k) = [
        make_cell_with_state s1 descr opt1; make_cell_with_state s2 descr opt2
      ]
  | Sequence s1 s2 => exists opt1 opt2,
      b1 <= S k /\
      S (k + syntax_size s1) < b2 /\
      inputs N k = [ S k; S (k + syntax_size s1) ] /\
      map (cells N) (inputs N k) = [
        make_cell_with_state s1 descr opt1; make_cell_with_state s2 descr opt2
      ]
  | Map f g s' => exists opt',
      b1 <= S k /\ S k < b2 /\
      inputs N k = [ S k ] /\
      map (cells N) (inputs N k) = [ make_cell_with_state s' descr opt' ]
  | Var x => exists opt',
      inputs N k = [ sum_sizes_until x ] /\
      map (cells N) (inputs N k) = [ make_cell_with_state (e x) descr opt' ]
  end.

Definition wip_cell { G } (descr: Description G) (N: Network) (k: nat) (b1 b2: nat): Prop :=
  exists A (s: Syntax A) (opt: option (G A)),
    cells N k = make_cell_with_state s descr opt /\
    opt_forall opt (descr_ind descr s) /\
    wip_inputs s descr N k b1 b2.

(** The "work-in-progress" property states that the state of every cell can
    be derived from the states of its inputs according to the description `descr`.
    We prove later that this is an invariant of the network (during computation),
    which ensures the soundness statement `fun_soundness_statement` *)
Definition wip_cells { G } (descr: Description G) (N: Network) (b1 b2: nat): Prop :=
  forall k, b1 <= k -> k < b2 -> wip_cell descr N k b1 b2.

Ltac instantiate_wip_cells k :=
  match goal with
  | H: wip_cells _ _ _ _ |- _ =>
    poseNew (Mark k "instantiate_wip_cells");
    let W := fresh "W" in
    unshelve epose proof (H k _ _) as W; eauto with lia; unfold wip_cell in W
  end.

Lemma good_inputs_wip_inputs:
  forall A (s: Syntax A) G (descr: Description G) N k b1 b2,
    good_inputs s descr N k b1 b2 ->
    (forall x, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr None) ->
    wip_inputs s descr N k b1 b2.
Proof.
  destruct s; repeat light; eauto 6.
  exists None; repeat light || rewrite_known_inputs.
Qed.

Lemma good_cell_wip_cell:
  forall G (descr: Description G) N k b1 b2,
    good_cell descr N k b1 b2 ->
    (forall x, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr None) ->
    wip_cell descr N k b1 b2.
Proof.
  unfold good_cell, wip_cell;
    repeat light.
  exists A, s, None; repeat light;
    eauto using good_inputs_wip_inputs.
Qed.

(** Initially, the network satisfies the `wip_cells` invariant *)
Lemma wip_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k < sum_sizes vars + syntax_size s ->
    wip_cell descr (make_network s descr) k 0 (sum_sizes vars + syntax_size s).
Proof.
  intros; apply good_cell_wip_cell;
    eauto using good_cells_make_network;
    eauto using var_cells_make_network.
Qed.


Lemma still_wip_inputs:
  forall A (s: Syntax A) G (descr: Description G) N b1 b2 k opt (opt': option (G A)) H,
    wip_inputs s descr N k b1 b2 ->
    cells N k = make_cell_with_state s descr opt ->
    (forall x, exists optx, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr optx) ->
    wip_inputs s descr (
      set_cell N k {|
       main_type := main_type (cells N k);
       cell_type := cell_type (cells N k);
       input_types := input_types (cells N k);
       update := update (cells N k);
       measure := measure (cells N k);
       state := cast H (s, opt')
      |})
      k b1 b2.
Proof.
  destruct s; repeat light.
  - eexists; eexists; repeat light || map_ext_in || destruct_match || rewrite_known_inputs;
      eauto; try lia.
  - eexists; eexists; repeat light || map_ext_in || destruct_match || rewrite_known_inputs;
      eauto; try lia.
  - eexists; repeat light || map_ext_in || destruct_match || rewrite_known_inputs;
      eauto; try lia.
  - pose proof (Nat.eq_dec k (sum_sizes_until x)); lights;
      try solve [ eexists; repeat light || destruct_match || rewrite_known_inputs; eauto ].
    specialize H2 with x; lights.
    pose proof (eq_trans (eq_sym H1) H0) as HE.
    pose proof (f_equal_dep _ state HE);
      repeat eq_dep || cbn in * || rewrite state_make_cell in * || invert_constructor_equalities.
    exists opt'; repeat light || rewrite_known_inputs || destruct_match || invert_constructor_equalities.
    f_equal.
    generalize H.
    rewrite H3; repeat cbn in * || eq_dep.
    repeat rewrite <- H6 || light || eq_dep.
Qed.

Lemma still_wip_inputs2:
  forall A (s: Syntax A) G (descr: Description G) N b1 b2 k k' hl,
    wip_inputs s descr N k b1 b2 ->
    k <> k' ->
    wip_inputs s descr (
      set_cell N k' {|
       main_type := main_type (cells N k');
       cell_type := cell_type (cells N k');
       input_types := input_types (cells N k');
       update := update (cells N k');
       measure := measure (cells N k');
       state := update (cells N k') hl
      |})
      k b1 b2.
Proof.
  destruct s; repeat light || rewrite_known_inputs || invert_constructor_equalities.
  - destruct (Nat.eq_dec k' (S k)); destruct (Nat.eq_dec k' (S (k + syntax_size s1)));
      repeat light;
      try solve [ repeat syntax_size_gt_0; eauto with lia ].

    + unshelve eexists (@snd (Syntax A) (option (G A)) (cast _ (update (cells N (S k)) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ].
      exists opt2; repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt1;
      unshelve eexists (@snd (Syntax A) (option (G A)) (cast _ (update (cells N (S (k + syntax_size s1))) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ];
        repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt1, opt2; repeat light || f_equal.

  - destruct (Nat.eq_dec k' (S k)); destruct (Nat.eq_dec k' (S (k + syntax_size s1)));
      repeat light;
      try solve [ repeat syntax_size_gt_0; eauto with lia ].

    + unshelve eexists (@snd (Syntax A) (option (G A)) (cast _ (update (cells N (S k)) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ].
      exists opt2; repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt1;
      unshelve eexists (@snd (Syntax B) (option (G B)) (cast _ (update (cells N (S (k + syntax_size s1))) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ];
        repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt1, opt2; repeat light || f_equal.

  - destruct (Nat.eq_dec k' (S k));
      repeat light.

    + unshelve eexists (@snd (Syntax A) (option (G A)) (cast _ (update (cells N (S k)) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ];
        repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt';
        repeat light || f_equal;
        eauto using update_make_cell2.

  - destruct (Nat.eq_dec k' (sum_sizes_until x));
      repeat light.

    + unshelve eexists (@snd (Syntax (get_type x)) (option (G (get_type x))) (cast _ (update (cells N (sum_sizes_until x)) hl)));
        try solve [ rewrite_any; eapply cell_type_node_type ];
        repeat light || f_equal;
        eauto using update_make_cell2.

    + exists opt';
        repeat light || f_equal;
        eauto using update_make_cell2.
Qed.

Ltac equate_states :=
  match goal with
  | H1: state (cells ?N ?k) = ?q1,
    H2: state (cells ?N ?k) = ?q2 |- _ =>
    poseNew (Mark (H1, H2) "equate_states");
    pose proof (eq_trans (eq_sym H1) H2)
  end.

Lemma update_obligation:
  forall A (s: Syntax A) G (descr : Description G) (N : Network) (k : nat) (opt: option (G A)),
    cells N k = make_cell_with_state s descr opt ->
    (Syntax A * option (G A))%type = cell_type (cells N k).
Proof.
  repeat light || f_equal_dep.
  rewrite_known_cells.
  rewrite cell_type_node_type.
  reflexivity.
Qed.

Lemma update_is_cast:
  forall A (s: Syntax A) G (descr : Description G) (N : Network) (k : nat) (opt: option (G A)) hl
    (H: cells N k = make_cell_with_state s descr opt),
    exists opt': option (G A),
      update (cells N k) hl = cast (update_obligation A s G descr N k opt H) (s, opt').
Proof.
  repeat light || f_equal_dep.
  destruct s;
    repeat light || rewrite_known_updates || eq_dep;
    try solve [
      repeat generalize_proofs; generalize hl;
      rewrite_known_cell_types;
      rewrite H5; repeat light || eq_dep;
      unfold rules_to_update; eauto
    ].
Qed.

(** The "work-in-progress" invariant is maintained after running the network one step *)
Lemma wip_cells_compute_cell:
  forall G (descr: Description G) N N' b1 b2 k pre,
    wip_cells descr N b1 b2 ->
    b1 <= k ->
    k < b2 ->
    (forall x, b1 <= sum_sizes_until x /\ sum_sizes_until x < b2) ->
    (forall x, exists optx, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr optx) ->
    compute_cell N k pre = Some N' ->
    wip_cells descr N' b1 b2.
Proof.
  unfold compute_cell, wip_cells, wip_cell;
    repeat light || destruct_match || invert_constructor_equalities || clear l matched ||
           instantiate_any ||
           lazymatch goal with
           | H: cells ?N ?k = make_cell_with_state ?s _ _ |- exists _ _ _, {| cell_type := cell_type (cells ?N ?k); state := ?q |} = _ /\ _ =>
             eexists _; exists s; unshelve eexists (snd (@cast _ (node_type _ G) _ q))
           end;
      try solve [ rewrite_known_cells; eauto using cell_type_node_type ];
      eauto using update_make_cell;
      eauto using still_wip_inputs;
      try solve [ repeat eexists; eauto using still_wip_inputs2 ].

  - repeat f_equal_dep.
    repeat eq_dep.

    unfold make_cell_with_state in H13, H15, H17.
    destruct s0; rewrite H15; repeat light || eq_dep;
    try solve [
      repeat generalize_proofs;
      rewrite_known_inputs; cbn;
      match goal with
      | H: input_types (cells _ _) = _ |- _ => rewrite H
      end; cbn;
      match goal with
      | H: cell_type (cells _ _) = _ |- _ => rewrite H
      end; cbn;
      unfold opt_forall; repeat light || eq_dep || destruct_match;
      apply_anywhere fold_left_or_else; repeat light; eauto with descr_ind
    ].

    + (* disjunction *)
      repeat generalize_proofs.
      rewrite_known_inputs; repeat cbn in * || invert_constructor_equalities.
      unshelve epose proof (H (S k0) _ _); try lia; repeat destruct_exists || destruct_and.
      unshelve epose proof (H (S (k0 + syntax_size s0_1)) _ _); try lia;
        repeat destruct_exists || destruct_and.
      match goal with
      | H: input_types (cells _ _) = _ |- _ => rewrite H
      end; cbn.

      repeat rewrite_known_cell_types.
      repeat f_equal_dep2.
      rewrite cell_type_node_type in *.
      rewrite state_make_cell in *.
      repeat cbn in * || eq_dep.
      repeat rewrite_known_states; repeat cbn in * || eq_dep.
      repeat generalize_proofs.

      repeat rewrite_known_cell_types; repeat light || eq_dep.
      unfold opt_forall; repeat light || eq_dep || destruct_match.
      apply_anywhere fold_left_or_else; repeat light.
      eapply in_disj_descr; eauto;
        unfold node_type; repeat light || eq_dep.
      * repeat same_cell_same_type; repeat light || eq_dep.
        repeat equate_states.
        repeat equate_states; repeat apply_anywhere eq_rect_reverse;
          repeat light || invert_constructor_equalities.
      * repeat same_cell_same_type; repeat light || eq_dep.
        repeat equate_states; repeat apply_anywhere eq_rect_reverse;
          repeat light || invert_constructor_equalities.

    + (* sequence *)
      repeat generalize_proofs.
      rewrite_known_inputs; repeat cbn in * || invert_constructor_equalities.
      unshelve epose proof (H (S k0) _ _); try lia; repeat destruct_exists || destruct_and.
      unshelve epose proof (H (S (k0 + syntax_size s0_1)) _ _); try lia;
        repeat destruct_exists || destruct_and.
      match goal with
      | H: input_types (cells _ _) = _ |- _ => rewrite H
      end; cbn.

      repeat rewrite_known_cell_types.
      repeat f_equal_dep2.
      rewrite cell_type_node_type in *.
      rewrite state_make_cell in *.
      repeat cbn in * || eq_dep.
      repeat rewrite_known_states; repeat cbn in * || eq_dep.
      repeat generalize_proofs.

      repeat rewrite_known_cell_types; repeat light || eq_dep.
      unfold opt_forall; repeat light || eq_dep || destruct_match.
      apply_anywhere fold_left_or_else; repeat light.
      eapply in_seq_descr; eauto;
        unfold node_type; repeat light || eq_dep.
      * repeat same_cell_same_type; repeat light || eq_dep.
        repeat equate_states; repeat apply_anywhere eq_rect_reverse;
          repeat light || invert_constructor_equalities.
      * repeat same_cell_same_type; repeat light || eq_dep.
        repeat equate_states; repeat apply_anywhere eq_rect_reverse;
          repeat light || invert_constructor_equalities.

    + (* map *)
      repeat generalize_proofs.
      rewrite_known_inputs; repeat cbn in * || invert_constructor_equalities.
      unshelve epose proof (H (S k0) _ _); try lia; repeat destruct_exists || destruct_and.
      match goal with
      | H: input_types (cells _ _) = _ |- _ => rewrite H
      end; cbn.

      repeat rewrite_known_cell_types.
      repeat f_equal_dep2.
      rewrite cell_type_node_type in *.
      rewrite state_make_cell in *.
      repeat cbn in * || eq_dep.
      repeat rewrite_known_states; repeat cbn in * || eq_dep.
      repeat generalize_proofs.

      repeat rewrite_known_cell_types; repeat light || eq_dep.
      unfold opt_forall; repeat light || eq_dep || destruct_match.
      apply_anywhere fold_left_or_else; repeat light.
      eapply in_map_descr; eauto;
        unfold node_type; repeat light || eq_dep.
      repeat same_cell_same_type; repeat light || eq_dep.
      repeat equate_states; repeat apply_anywhere eq_rect_reverse;
        repeat light || invert_constructor_equalities.

    + (* var *)
      repeat generalize_proofs.
      rewrite_known_inputs; repeat cbn in * || invert_constructor_equalities.
      unshelve epose proof (H (sum_sizes_until x) _ _);
        try lia; repeat destruct_exists || destruct_and || apply_any.
      match goal with
      | H: input_types (cells _ _) = _ |- _ => rewrite H
      end; cbn.

      repeat rewrite_known_cell_types.
      repeat f_equal_dep2.
      rewrite cell_type_node_type in *.
      rewrite state_make_cell in *.
      repeat cbn in * || eq_dep.
      repeat rewrite_known_states; repeat cbn in * || eq_dep.
      repeat generalize_proofs.

      repeat rewrite_known_cell_types; repeat light || eq_dep.
      unfold opt_forall; repeat light || eq_dep || destruct_match.
      apply_anywhere fold_left_or_else; repeat light.
      eapply in_var_descr; eauto;
        unfold node_type; repeat light || eq_dep.
      repeat same_cell_same_type; repeat light || eq_dep.
      repeat equate_states; repeat apply_anywhere eq_rect_reverse;
        repeat light || invert_constructor_equalities.

  - match goal with
    | |- context[update ?c ?hl] =>
      unshelve epose proof (update_is_cast _ _ _ _ _ _ _ hl H10)
    end; lights.
    rewrite H11; eauto using still_wip_inputs.
Qed.

Opaque make_cell_with_state.
Opaque compute_cells.

Lemma wip_cells_compute_cells':
  forall m G (descr: Description G) N num_cells ks pre,
    (sum_measures num_cells N, length ks) = m ->
    wip_cells descr N 0 num_cells ->
    (forall k, In k ks -> k < num_cells) ->
    (forall x, sum_sizes_until x < num_cells) ->
    (forall x, exists optx, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr optx) ->
    wip_cells descr (compute_cells num_cells N ks pre) 0 num_cells.
Proof.
  induction m using measure_induction; destruct ks;
    repeat light || compute_cells_def || destruct_match || options.

  - clear matched.
    revert i.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_3 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_2 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match || options.

    eapply H;
      repeat light;
      try solve [ apply left_lex; eauto using compute_cell_size ].

    + eapply (wip_cells_compute_cell _ _ N _ _ _ n);
        eauto; repeat light || apply_any; try lia.
    + specialize H4 with x; lights; eauto using compute_cell_still_make_cell.

  - clear matched.
    revert n0.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_5 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match;
      eauto 2 with lights.

    eapply H;
      repeat light || apply right_lex;
      eauto using cell_type_compute_cell.
Qed.

(** The "work-in-progress" invariant is maintained after running the network *)
Lemma wip_cells_compute_cells:
  forall G (descr: Description G) N num_cells ks pre,
    wip_cells descr N 0 num_cells ->
    (forall k, In k ks -> k < num_cells) ->
    (forall x, sum_sizes_until x < num_cells) ->
    (forall x, exists optx, cells N (sum_sizes_until x) = make_cell_with_state (e x) descr optx) ->
    wip_cells descr (compute_cells num_cells N ks pre) 0 num_cells.
Proof.
  eauto using wip_cells_compute_cells'.
Qed.

Lemma wip_cells_compute_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) pre,
    wip_cells descr (
      compute_cells
        (sum_sizes vars + syntax_size s)
        (make_network s descr)
        (range 0 (sum_sizes vars + syntax_size s))
        pre
    ) 0 (sum_sizes vars + syntax_size s).
Proof.
  intros.
  apply wip_cells_compute_cells;
    repeat light || unfold wip_cells;
    try solve [ pose proof (sum_sizes_until_sum_sizes x); eauto with lia ];
    eauto using wip_cells_make_network;
    eauto using var_cells_make_network.
Qed.
