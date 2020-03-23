Require Export Parser.NetworkProperties.
Require Export Parser.Cast.

Open Scope nat_scope.

Opaque range.

(** `build_fun` constructs a progatator network from a description `descr`, and
    after running it, extract the value for the cell corresponding to the syntax
    s *)
Program Definition build_fun { G } (descr: Description G) { A } (s: Syntax A): option (G A) :=
  let num_cells: nat := sum_sizes vars + syntax_size s in
  let N' := compute_cells num_cells (make_network s descr) (range 0 num_cells) _ in
  let s: node_type A G := cast _ (state (cells N' (sum_sizes vars))) in
  snd s.

Next Obligation.
  repeat light || destruct_proj1_sigs || rewrite range_spec in *;
    eauto using io_types_make_network;
    eauto using max_pointer_make_network.
Qed.

Next Obligation.
  rewrite cell_type_compute_cells.
  unfold make_network.
  rewrite cell_make_network';
    eauto using cell_type_node_type.
Qed.

Fail Next Obligation. (* no more obligations for build_fun *)
