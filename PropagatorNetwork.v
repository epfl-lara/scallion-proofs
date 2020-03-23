Require Import Equations.Equations.
Require Import Equations.Prop.Subterm. (* lexicographic ordering *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz. (* lia tactic for linear integer arithmetic *)

Require Export Parser.HList.
Require Export Parser.Lexicographic.
Require Export Parser.Option.

Record Cell: Type := mkCell {
  (** when building networks from syntaxes, we use the field `main_type` to
      store the type of the syntax node corresponding to this cell *)
  main_type: Type;
  cell_type: Type;
  input_types: list Type;
  update: hlist input_types -> cell_type;
  measure: cell_type -> nat;
  state: cell_type;
}.

Arguments mkCell main_type { cell_type } { input_types }.

Record Network: Type := mkNetwork {
  cells: nat -> Cell;
  inputs: nat -> list nat;
  registered: nat -> list nat;
}.

Definition set_cell (N: Network) (k: nat) (cell: Cell): Network := {|
  cells := fun k' => if Nat.eq_dec k k' then cell else cells N k';
  inputs := inputs N;
  registered := registered N;
|}.

Definition io_types (N: Network): Prop :=
  forall k, map (fun k' => cell_type (cells N k')) (inputs N k) = input_types (cells N k).

Definition io_types_instantiate:
  forall N k,
    io_types N ->
    map (fun k' => cell_type (cells N k')) (inputs N k) = input_types (cells N k).
Proof.
  unfold io_types; lights.
Qed.

Ltac io_types_instantiate :=
  match goal with
  | H: io_types ?N, k: nat |- _ =>
    poseNew (Mark (k, N) "io_types_instantiate");
    pose proof (io_types_instantiate N k H)
  end.

Definition max_pointer (num_cells: nat) (N: Network): Prop :=
  forall k,
    k < num_cells ->
    forall k', In k' (registered N k) -> k' < num_cells.

Ltac rewrite_cell :=
  match goal with
  | H: cells _ _ = mkCell _ _ _ |- _ => rewrite H in *
  end.

Definition io_types_set_cell:
  forall N k cell,
    io_types N ->
    input_types (cells N k) = input_types cell ->
    cell_type (cells N k) = cell_type cell ->
    io_types (set_cell N k cell).
Proof.
  unfold set_cell;
    repeat match goal with
    | H: map _ _ = input_types _ |- _ => rewrite <- H in *
    | _ => light || unfold io_types || io_types_instantiate || destruct_match || apply map_ext
    end.
Qed.

Definition set_cell_with_inputs (N: Network) (k: nat) (cell: Cell) (ks: list nat): Network := {|
  cells := fun k' => if Nat.eq_dec k k' then cell else cells N k';
  inputs := fun k' => if Nat.eq_dec k k' then ks else inputs N k';
  registered := fun k' => if in_dec Nat.eq_dec k' ks then k :: registered N k' else registered N k';
|}.

Definition io_types_set_cell_with_inputs:
  forall N k cell ks,
    io_types N ->
    ~ In k ks ->
    (forall k', ~ In k (inputs N k')) ->
    map (fun k' => cell_type (cells N k')) ks = input_types cell ->
    io_types (set_cell_with_inputs N k cell ks).
Proof.
  unfold set_cell_with_inputs;
    repeat match goal with
    | H: map _ _ = input_types _ |- _ => rewrite <- H in *
    | _ => light || unfold io_types || io_types_instantiate || destruct_match || apply map_ext_in
    end;
    eauto with exfalso.
Qed.

Lemma max_pointer_set_cell:
  forall N k cell num_cells,
    max_pointer num_cells N ->
    max_pointer num_cells (set_cell N k cell).
Proof.
  unfold max_pointer; lights.
Qed.

Definition get_measure (cell: Cell): nat := measure cell (state cell).

Fixpoint sum_measures (num_cells: nat) (N: Network): nat :=
  match num_cells return nat with
  | 0 => 0
  | S k => sum_measures k N + get_measure (cells N k)
  end.

(* Update the state of cell `k`. Returns `None` if there is nothing to do *)
Program Definition compute_cell (N: Network) (k: nat) (pre: io_types N): option Network :=
  let cell: Cell := cells N k in
  let inputs: hlist (input_types cell) :=
    h_map (fun k' => state (cells N k')) (inputs N k) in
  let q': cell_type cell := update cell inputs in
  if (Compare_dec.lt_dec (measure cell q') (measure cell (state cell)))
  then Some (set_cell N k (mkCell (main_type cell) (update cell) (measure cell) q'))
  else None.

Fail Next Obligation. (* no more obligations for compute_cell *)

Lemma io_types_compute_cell:
  forall N k pre N',
    compute_cell N k pre = Some N' ->
    io_types N ->
    io_types N'.
Proof.
  unfold compute_cell;
    repeat light || destruct_match || apply io_types_set_cell || invert_constructor_equalities.
Qed.

Opaque io_types.

Lemma max_pointer_compute_cell:
  forall num_cells N k pre N',
    compute_cell N k pre = Some N' ->
    max_pointer num_cells N ->
    max_pointer num_cells N'.
Proof.
  unfold compute_cell;
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Lemma set_cell_different:
  forall N k k' cell,
    k <> k' ->
    cells (set_cell N k cell) k' = cells N k'.
Proof.
  unfold set_cell;
    repeat light || destruct_match.
Qed.

Lemma set_cell_same:
  forall N k cell,
    cells (set_cell N k cell) k = cell.
Proof.
  unfold set_cell;
    repeat light || destruct_match.
Qed.

Lemma sum_measure_set_cell_1:
  forall (num_cells: nat) (N: Network) (k: nat) cell,
    k >= num_cells ->
    sum_measures num_cells (set_cell N k cell) = sum_measures num_cells N.
Proof.
  induction num_cells; repeat light || destruct_match; eauto with lia.
Qed.

Opaque set_cell.

Lemma sum_measure_set_cell_2:
  forall (num_cells: nat) (N: Network) (k: nat) (cell: Cell),
    k < num_cells ->
    get_measure cell < get_measure (cells N k) ->
    sum_measures num_cells (set_cell N k cell) < sum_measures num_cells N.
Proof.
  induction num_cells; lights; eauto with lia.
  destruct (Nat.eq_dec k num_cells); lights.

  - rewrite sum_measure_set_cell_1; lights; eauto with lia.
    apply Nat.add_lt_mono_l.
    rewrite set_cell_same; auto.

  - rewrite set_cell_different; lights.
    apply Nat.add_lt_mono_r.
    eauto with lia.
Qed.

Lemma compute_cell_size:
  forall num_cells N k pre N',
    compute_cell N k pre = Some N' ->
    k < num_cells ->
    sum_measures num_cells N' < sum_measures num_cells N.
Proof.
  unfold compute_cell;
    repeat light || destruct_match || apply sum_measure_set_cell_2 || invert_constructor_equalities.
Qed.

Equations (noind) compute_cells (num_cells: nat) (N: Network) (ks: list nat)
  (pre:
     io_types N /\
     max_pointer num_cells N /\
     (forall k, In k ks -> k < num_cells)
  ): Network
  by wf (sum_measures num_cells N, length ks) lt_lex :=

  compute_cells num_cells N [] _ := N;
  compute_cells num_cells N (k :: ks) _ :=
    let opt := compute_cell N k _ in
    if (is_some_dec opt)
    then compute_cells num_cells (get_option opt _) (ks ++ registered N k) _
    else compute_cells num_cells N ks _.

Next Obligation.
  repeat light || lists || options || destruct_match;
    eauto using max_pointer_compute_cell;
    eauto using io_types_compute_cell.
Qed.

Next Obligation.
  apply left_lex;
    repeat light || options || destruct_match;
    eauto using compute_cell_size.
Qed.

Next Obligation.
  apply right_lex; auto.
Qed.

Fail Next Obligation. (* No more obligations for compute_cells *)

Ltac compute_cells_def :=
  rewrite compute_cells_equation_1 in * ||
  rewrite compute_cells_equation_2 in *.

Ltac rewrite_known_states :=
  match goal with
  | H1: state _ = eq_rect _ _ (_, ?opt) _ _,
    H2: opt_forall ?opt _ |- _ =>
    rewrite H1
  end.

Ltac rewrite_known_cell_types :=
  match goal with
  | H: cell_type _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_updates :=
  match goal with
  | H: update _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_inputs2 :=
  match goal with
  | H:inputs _ _ = [] |- _ => rewrite H in *
  | H:inputs _ _ = _ :: _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_states2 :=
  match goal with
  | H: state _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_inputs :=
  match goal with
  | H: inputs _ _ = [] |- _ => rewrite H in *; clear H
  | H: inputs _ _ = _ :: _ |- _ => rewrite H in *; clear H
  end.

Ltac rewrite_known_cells :=
  match goal with
  | H: cells _ _ = _ |- _ => rewrite H in *; clear H
  end.

Ltac rewrite_known_input_types :=
  match goal with
  | H: input_types _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_measures :=
  match goal with
  | H: measure _ = _ |- _ => rewrite H in *
  end.
