Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.NetworkGoodCells.

Open Scope nat_scope.

Opaque PeanoNat.Nat.eq_dec.

Lemma var_cells_init_env_network:
  forall A (s: Syntax A) G (descr: Description G) x,
    cells (init_env_network descr) (sum_sizes_until x) = make_cell_with_state (e x) descr None.
Proof.
  unfold init_env_network;
    repeat light.
  match goal with
  | |- context[fold_left ?f ?l ?a] =>
    unshelve epose proof
      fold_left_invariant
        (fun N xs => forall x,
           In x xs ->
           cells N (sum_sizes_until x) = make_cell_with_state (e x) descr None
        )
        f l a
        _ _
  end;
    repeat light || rewrite in_app_iff in * || instantiate_any ||
           (rewrite unchanged_cells_smaller by eauto using sum_sizes_until_prefix3) ||
           (erewrite sum_sizes_until_prefix in * by eauto);
    eauto using cell_make_network';
    eauto using all_vars.
Qed.

Lemma var_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) x,
    cells (make_network s descr) (sum_sizes_until x) = make_cell_with_state (e x) descr None.
Proof.
  unfold make_network;
    repeat light.

  rewrite unchanged_cells_smaller; eauto using sum_sizes_until_sum_sizes;
    eauto using var_cells_init_env_network.
Qed.

Lemma empty_cells_init_env_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k >= sum_sizes vars + syntax_size s ->
    cells (init_env_network descr) k = empty_cell.
Proof.
  unfold init_env_network;
    repeat light.
  match goal with
  | |- context[fold_left ?f ?l ?a] =>
    unshelve epose proof
      fold_left_invariant
        (fun N xs =>
           cells N k = empty_cell
        )
        f l a
        _ _
  end;
    repeat light || (erewrite sum_sizes_until_prefix in * by eauto).

  rewrite unchanged_cells_larger;
    repeat light || rewrite_any || rewrite sum_sizes_append in *; try lia.
Qed.

Lemma empty_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k >= sum_sizes vars + syntax_size s ->
    cells (make_network s descr) k = empty_cell.
Proof.
  unfold make_network;
    repeat light.

  rewrite unchanged_cells_larger; lights;
    eauto using empty_cells_init_env_network.
Qed.

Lemma empty_inputs_init_env_network:
  forall G (descr: Description G) k,
    k >= sum_sizes vars ->
    inputs (init_env_network descr) k = [].
Proof.
  unfold init_env_network;
    repeat light.
  match goal with
  | |- context[fold_left ?f ?l ?a] =>
    unshelve epose proof
      fold_left_invariant
        (fun N xs =>
           inputs N k = []
        )
        f l a
        _ _
  end;
    repeat light || (erewrite sum_sizes_until_prefix in * by eauto).

  rewrite unchanged_inputs_larger;
    repeat light || rewrite_any || rewrite sum_sizes_append in *; try lia.
Qed.

Lemma empty_inputs_make_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k >= sum_sizes vars + syntax_size s ->
    inputs (make_network s descr) k = [].
Proof.
  unfold make_network;
    repeat light.

  rewrite unchanged_inputs_larger; repeat light || syntax_size_gt_0;
    eauto using empty_inputs_init_env_network with lia.
Qed.

Lemma io_types_make_network:
  forall A (s: Syntax A) G (descr: Description G),
    io_types (make_network s descr).
Proof.
  unfold io_types;
    repeat light.

  destruct (Compare_dec.lt_dec k (sum_sizes vars + syntax_size s)); lights.

  - eapply good_cell_io_type;
      eauto using good_cells_make_network;
      lights;
      eauto using var_cells_make_network.

  - rewrite empty_inputs_make_network by lia.
    rewrite empty_cells_make_network by lia.
    lights.
Qed.

Definition registered_inputs (N: Network): Prop:=
  forall k k', In k (registered N k') <-> In k' (inputs N k).

Lemma registered_inputs_empty_network:
  registered_inputs empty_network.
Proof.
  unfold registered_inputs, empty_network;
    repeat light.
Qed.

Lemma registered_inputs_set_cell_with_inputs:
  forall N cell k ks,
    registered_inputs N ->
    inputs N k = [] ->
    registered_inputs (set_cell_with_inputs N k cell ks).
Proof.
  unfold registered_inputs, set_cell_with_inputs;
    repeat light || destruct_match || rewrite_any.
Qed.

Lemma registered_inputs_make_network':
  forall A (s: Syntax A) G (descr: Description G) k N,
    registered_inputs N ->
    (forall k', k' >= k -> inputs N k' = []) ->
    registered_inputs (make_network' s descr k N).
Proof.
  induction s; repeat light;
    eauto using registered_inputs_set_cell_with_inputs.

  - apply registered_inputs_set_cell_with_inputs; repeat light || unchanged_rewrites; eauto with lia.
    apply_any; repeat light || unchanged_rewrites; eauto with lia.

  - apply registered_inputs_set_cell_with_inputs; repeat light || unchanged_rewrites; eauto with lia.
    apply_any; repeat light || unchanged_rewrites; eauto with lia.

  - apply registered_inputs_set_cell_with_inputs; repeat light || unchanged_rewrites; eauto with lia.
Qed.

Lemma registered_inputs_init_env_network:
  forall G (descr: Description G),
    registered_inputs (init_env_network descr).
Proof.
  unfold init_env_network; lights.

  match goal with
  | |- context[fold_left ?f ?l ?a] =>
    unshelve epose proof
      fold_left_invariant
        (fun N xs =>
           (forall k, k >= sum_sizes xs -> inputs N k = []) /\
           registered_inputs N
        )
        f l a
        _ _
  end;
    repeat light || unchanged_rewrites ||
           rewrite sum_sizes_append in * || (erewrite sum_sizes_until_prefix in * by eauto);
    eauto using registered_inputs_empty_network;
    eauto using registered_inputs_make_network';
    eauto with lia.
Qed.

Lemma registered_inputs_make_network:
  forall A (s: Syntax A) G (descr: Description G),
    registered_inputs (make_network s descr).
Proof.
  unfold make_network; lights.
  apply registered_inputs_make_network'; lights;
    eauto using registered_inputs_init_env_network;
    eauto using empty_inputs_init_env_network.
Qed.

Lemma max_pointer_make_network:
  forall A (s: Syntax A) G (descr: Description G),
    max_pointer (sum_sizes vars + syntax_size s) (make_network s descr).
Proof.
  unfold max_pointer; repeat light || rewrite registered_inputs_make_network in *.

  pose proof (registered_inputs_make_network _ s _ descr); unfold registered_inputs in *;
    rewrite_any.

  destruct (Compare_dec.lt_dec k' (sum_sizes vars + syntax_size s)); lights.
  rewrite empty_inputs_make_network in *; lights; try lia.
Qed.

Lemma cell_type_compute_cell:
  forall N k pre N' k',
    compute_cell N k pre = Some N' ->
    cell_type (cells N' k') = cell_type (cells N k').
Proof.
  unfold compute_cell;
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Lemma compute_cell_still_make_cell:
  forall A (s: Syntax A) G (descr: Description G) N N' k k0 opt pre,
    cells N k = make_cell_with_state s descr opt ->
    compute_cell N k0 pre = Some N' ->
    exists opt', cells N' k = make_cell_with_state s descr opt'.
Proof.
  unfold compute_cell;
    repeat light || destruct_match || invert_constructor_equalities; eauto.
  unshelve eexists (@snd (Syntax A) (option (G A)) (cast _
    (update (cells N k)
      (eq_rect (map (fun k' : nat => cell_type (cells N k')) (inputs N k))
         (fun H0 : list Type => hlist H0)
         (h_map (fun k' : nat => state (cells N k')) (inputs N k))
         (input_types (cells N k)) (PropagatorNetwork.compute_cell_obligation_1 N k pre)))));
    try solve [ rewrite_known_cells; rewrite cell_type_node_type; reflexivity ];
    eauto using update_make_cell2.
Qed.

Opaque compute_cells.
Opaque compute_cell.

Lemma cell_type_compute_cells':
  forall m num_cells N ks pre k',
    (sum_measures num_cells N, length ks) = m ->
    cell_type (cells (compute_cells num_cells N ks pre) k') = cell_type (cells N k').
Proof.
  induction m using measure_induction; destruct ks;
    repeat light || compute_cells_def || destruct_match || options.

  - clear matched.
    revert i.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_3 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_2 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match || options.

    erewrite H;
      repeat light;
      eauto using cell_type_compute_cell.

    apply left_lex;
      eauto using compute_cell_size.

  - clear matched.
    revert n0.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_5 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match;
      eauto 2 with lights.

    erewrite H;
      repeat light || apply right_lex;
      eauto using cell_type_compute_cell.
Qed.

Lemma cell_type_compute_cells:
  forall num_cells N ks pre k',
    cell_type (cells (compute_cells num_cells N ks pre) k') = cell_type (cells N k').
Proof.
  eauto using cell_type_compute_cells'.
Qed.


(** Lemmas stating that all cells are of the form `make_cell_with_state` *)

Lemma compute_cells_still_make_cell':
  forall m A (s: Syntax A) G (descr: Description G) N k num_cells ks opt pre,
    (sum_measures num_cells N, length ks) = m ->
    cells N k = make_cell_with_state s descr opt ->
    exists opt', cells (compute_cells num_cells N ks pre) k = make_cell_with_state s descr opt'.
Proof.
  induction m using measure_induction; destruct ks;
    repeat light || compute_cells_def || destruct_match || options; eauto.

  - clear matched.
    revert i.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_3 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_2 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match || options.

    pose proof (compute_cell_still_make_cell _ _ _ _ _ _ _ _ _ _ H1 matched);
      lights.


    lazymatch goal with
    | |- context[cells (compute_cells _ ?N ?ks ?pre) ?k] =>
      unshelve epose proof (H _ _ _ s _ descr N k num_cells ks _ (a i1) eq_refl H5)
    end; lights;
      try solve [ apply left_lex; eauto using compute_cell_size ].

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

Lemma compute_cells_still_make_cell:
  forall A (s: Syntax A) G (descr: Description G) N k num_cells ks opt pre,
    cells N k = make_cell_with_state s descr opt ->
    exists opt', cells (compute_cells num_cells N ks pre) k = make_cell_with_state s descr opt'.
Proof.
  eauto using compute_cells_still_make_cell'.
Qed.
