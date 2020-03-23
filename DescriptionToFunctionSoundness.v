Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.DescriptionInd.
Require Export Parser.DescriptionToFunction.
Require Export Parser.NetworkProperties.
Require Export Parser.NetworkWipCells.
Require Export Parser.Cast.

Opaque range.
Opaque Nat.eq_dec.

Open Scope nat_scope.

(** The goal of this file is to prove that if the network for a description
    `descr` and a syntax `s` computes some value `v`, then `s` and `v` are in
    relation according to the description `descr` using the inductive definition
    *)
Definition fun_soundness_statement: Prop :=
  forall G (descr: Description G) A (s: Syntax A) v,
    build_fun descr s = Some v ->
    descr_ind descr s v.

Lemma main_type_compute_cell:
  forall N k pre N' k',
    compute_cell N k pre = Some N' ->
    main_type (cells N' k') = main_type (cells N k').
Proof.
  unfold compute_cell;
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Opaque compute_cells.
Opaque compute_cell.

Lemma main_type_compute_cells':
  forall m num_cells N ks pre k',
    (sum_measures num_cells N, length ks) = m ->
    main_type (cells (compute_cells num_cells N ks pre) k') = main_type (cells N k').
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
      eauto using main_type_compute_cell.

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
      eauto using main_type_compute_cell.
Qed.

(** `main_type` does not change after running the network *)
Lemma main_type_compute_cells:
  forall num_cells N ks pre k',
    main_type (cells (compute_cells num_cells N ks pre) k') = main_type (cells N k').
Proof.
  eauto using main_type_compute_cells'.
Qed.

Lemma main_type_top:
  forall A (s: Syntax A) G (descr: Description G),
    main_type (cells (make_network s descr) (sum_sizes vars)) = A.
Proof.
  unfold make_network;
    repeat light || rewrite cell_make_network' || rewrite main_type_make_cell.
Qed.

Transparent make_cell_with_state.

Lemma same_cell_same_syntax:
  forall A G (s1: Syntax A) (s2: Syntax A) (descr: Description G) opt1 opt2
    (H: make_cell_with_state s1 descr opt1 = make_cell_with_state s2 descr opt2),
    s1 = s2.
Proof.
  intros.
  pose proof (f_equal_dep _ state H);
    repeat light || eq_dep || rewrite state_make_cell in *.
Qed.

Lemma fun_soundness: fun_soundness_statement.
Proof.
  unfold fun_soundness_statement; unfold build_fun; intros.
  unshelve epose proof
    (wip_cells_compute_cells_make_network _ s _ descr
      (DescriptionToFunction.build_fun_obligation_1 G descr A s)) as W.
  unfold wip_cells, wip_cell in *.
  unshelve epose proof (W (sum_sizes vars) _ _) as W2; lights;
    try solve [ repeat syntax_size_gt_0; eauto with lia ].

  repeat f_equal_dep.

  rewrite state_make_cell in *; repeat eq_dep.
  rewrite H6 in H; repeat eq_dep.
  pose proof (f_equal_dep _ main_type H1);
    repeat cbn in * ||
           eq_dep || rewrite main_type_make_cell in * || rewrite main_type_compute_cells in * ||
           rewrite main_type_top in *.
  repeat light || eq_dep.

  pose proof (cell_make_network _ s _ descr) as HS.
  match goal with
  | H: context[compute_cells ?num_cells ?N ?ks ?pre] |- _ =>
    pose proof (compute_cells_still_make_cell _ _ _ _ _ _ _ ks _ pre HS)
  end; lights.
  pose proof (eq_trans (eq_sym H1) H) as HM.
  pose proof (same_cell_same_syntax _ _ _ _ _ _ _ HM); lights.
Qed.
