Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.DescriptionInd.
Require Export Parser.NetworkProperties.
Require Export Parser.Cast.

Opaque range.

Open Scope nat_scope.

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

Definition wip_cells { G } (descr: Description G) (N: Network) (b1 b2: nat): Prop :=
  forall k, b1 <= k -> k < b2 -> wip_cell descr N k b1 b2.

Opaque Nat.eq_dec.

Polymorphic Lemma f_equal_dep_1_2_3:
  forall (f: forall (M: Type) (T: Type) (TS: list Type), (hlist TS -> T) -> (T -> nat) -> T -> Cell),
    forall (M: Type) (M': Type)
      (T: Type) (T': Type)
      (TS: list Type) (TS': list Type)
      (x3: hlist TS -> T) (x3': hlist TS' -> T')
      (x4 : T -> nat) (x4': T' -> nat)
      (x5: T) (x5': T'),
      forall (H3: (hlist TS -> T) = (hlist TS' -> T'))
        H4
        H5,

      M = M' ->
      T = T' ->
      TS = TS' ->
      cast H3 x3 = x3' ->
      cast H4 x4 = x4' ->
      cast H5 x5 = x5' ->
      f M T TS x3 x4 x5 = f M' T' TS' x3' x4' x5'.
Proof.
  destruct 1; destruct 1;
    repeat light || f_equal || rewrite cast_irrelevance.
Qed.

Ltac add_equal_dep H f x :=
  poseNew (Mark (f, x) "add_equal_dep");
  pose proof (f_equal_dep _ f H);
  pose proof (eq_sym (f_equal_dep _ f (eq_sym H))).

Ltac add_equal_dep2 H f x :=
  poseNew (Mark (H, f, x) "add_equal_dep");
  pose proof (f_equal_dep _ f H);
  pose proof (eq_sym (f_equal_dep _ f (eq_sym H))).

Ltac rewrite_equal_dep H f x :=
  poseNew (Mark (f, x) "rewrite_equal_dep");
  rewrite (f_equal_dep _ f H) in *;
  rewrite (eq_sym (f_equal_dep _ f (eq_sym H))) in *.

Ltac f_equal_dep :=
  match goal with
  | H: ?x = _ |- context[cell_type ?x] => add_equal_dep H cell_type x
  | H: ?x = _, H': context[cell_type ?x] |- _ => add_equal_dep H cell_type x
  | H: ?x = _ |- context[measure ?x] => add_equal_dep H measure x
  | H: ?x = _, H': context[measure ?x] |- _ => add_equal_dep H measure x
  | H: ?x = _ |- context[update ?x] => add_equal_dep H update x
  | H: ?x = _, H': context[update ?x] |- _ => add_equal_dep H update x
  | H: ?x = _ |- context[input_types ?x] => add_equal_dep H input_types x
  | H: ?x = _, H': context[input_types ?x] |- _ => add_equal_dep H input_types x
  | H: ?x = _ |- context[state ?x] => add_equal_dep H state x
  | H: ?x = _, H': context[state ?x] |- _ => add_equal_dep H state x
  end.

Ltac f_equal_dep2 :=
  match goal with
  | H: ?x = _ |- context[cell_type ?x] => add_equal_dep2 H cell_type x
  | H: ?x = _, H': context[cell_type ?x] |- _ => add_equal_dep2 H cell_type x
  | H: ?x = _ |- context[measure ?x] => add_equal_dep2 H measure x
  | H: ?x = _, H': context[measure ?x] |- _ => add_equal_dep2 H measure x
  | H: ?x = _ |- context[update ?x] => add_equal_dep2 H update x
  | H: ?x = _, H': context[update ?x] |- _ => add_equal_dep2 H update x
  | H: ?x = _ |- context[input_types ?x] => add_equal_dep2 H input_types x
  | H: ?x = _, H': context[input_types ?x] |- _ => add_equal_dep2 H input_types x
  | H: ?x = _ |- context[state ?x] => add_equal_dep2 H state x
  | H: ?x = _, H': context[state ?x] |- _ => add_equal_dep2 H state x
  end.

Lemma update_make_cell:
  forall G (descr : Description G) A (s : Syntax A) (N : Network) k H
    (opt : option (G A)) pre,

    cells N k = make_cell_with_state s descr opt ->

    {|
      main_type := main_type (cells N k);
      cell_type := cell_type (cells N k);
      input_types := input_types (cells N k);
      update := update (cells N k);
      measure := measure (cells N k);
      state := update (cells N k)
        (eq_rect (map (fun k' : nat => cell_type (cells N k')) (inputs N k))
                 (fun H : list Type => hlist H)
                 (h_map (fun k' : nat => state (cells N k')) (inputs N k))
                 (input_types (cells N k)) pre) |} =
    make_cell_with_state s descr
      (@snd (Syntax A) (option (G A)) (cast H (update (cells N k)
         (eq_rect (map (fun k' : nat => cell_type (cells N k')) (inputs N k))
                  (fun H : list Type => hlist H)
                  (h_map (fun k' : nat => state (cells N k')) (inputs N k))
                  (input_types (cells N k)) pre)))).
Proof.
  unfold make_cell_with_state;
    repeat light || destruct_match || unshelve eapply f_equal_dep_1_2_3;
    eauto;
    try solve [ rewrite_known_cells; lights ];
    try solve [ repeat f_equal_dep; rewrite eq_rekt in *; eauto 2 using eq_trans, eq_rect_irrelevance2 ];
    try solve [
      repeat f_equal_dep; repeat eq_dep;
      rewrite H4; lights;
      generalize_proofs;
      rewrite H5; cbn;
      rewrite H in *; repeat proofs_refl || light
    ].
Qed.

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

Lemma update_make_cell2:
  forall G (descr : Description G) A (s : Syntax A) (N : Network) k H hl (opt : option (G A)),

    cells N k = make_cell_with_state s descr opt ->

    {|
      main_type := main_type (cells N k);
      cell_type := cell_type (cells N k);
      input_types := input_types (cells N k);
      update := update (cells N k);
      measure := measure (cells N k);
      state := update (cells N k) hl |} =
    make_cell_with_state s descr
      (@snd (Syntax A) (option (G A)) (cast H (update (cells N k) hl))).
Proof.
  unfold make_cell_with_state;
    repeat light || destruct_match || unshelve eapply f_equal_dep_1_2_3;
    eauto;
    try solve [ rewrite_known_cells; lights ];
    try solve [ repeat f_equal_dep; rewrite eq_rekt in *; eauto 2 using eq_trans, eq_rect_irrelevance2 ];
    try solve [
      repeat f_equal_dep; repeat eq_dep;
      rewrite H4; lights;
      repeat generalize_proofs || cbn;
      generalize hl;
      rewrite_known_cell_types;
      rewrite H5;
      repeat eq_dep || light
    ].
Qed.

Lemma state_obligation:
  forall A (s : Syntax A) G (descr : Description G) (opt : option (G A)),
    (Syntax A * option (G A))%type = cell_type (make_cell_with_state s descr opt).
Proof.
  destruct s; repeat light.
Qed.

Lemma state_make_cell:
  forall A (s: Syntax A) G (descr: Description G) (opt: option (G A)),
    state (make_cell_with_state s descr opt) = cast (state_obligation A s G descr opt) (s, opt).
Proof.
  unfold make_cell_with_state, cast;
    repeat light || destruct_match || eq_dep.
Qed.

Ltac equal_main_types :=
  match goal with
  | H: cells ?N ?k = _ |- _ => add_equal_dep2 H main_type (cells N k)
  end.

Lemma main_type_make_cell:
  forall A (s: Syntax A) G (descr: Description G) (opt: option (G A)),
    main_type (make_cell_with_state s descr opt) = A.
Proof.
  unfold make_cell_with_state, cast;
    repeat light || destruct_match.
Qed.

Lemma same_cell_same_type:
  forall A1 A2 G (s1: Syntax A1) (s2: Syntax A2) (descr: Description G) opt1 opt2,
    make_cell_with_state s1 descr opt1 = make_cell_with_state s2 descr opt2 ->
    A1 = A2.
Proof.
  unfold make_cell_with_state; repeat light || destruct_match;
    try solve [ injection H; repeat light ].
Qed.

Ltac same_cell_same_type :=
  match goal with
  | H1: cells ?N ?k = make_cell_with_state ?s1 ?descr ?opt1,
    H2: cells ?N ?k = make_cell_with_state ?s2 ?descr ?opt2 |- _ =>
    poseNew (Mark (H1, H2) "same_cell_same_type");
    pose proof (same_cell_same_type _ _ _ _ _ _ _ _ (eq_trans (eq_sym H1) H2))
  end.

Ltac equate_states :=
  match goal with
  | H1: state (cells ?N ?k) = ?q1,
    H2: state (cells ?N ?k) = ?q2 |- _ =>
    poseNew (Mark (H1, H2) "equate_states");
    pose proof (eq_trans (eq_sym H1) H2)
  end.

Lemma in_disj_descr:
  forall A (s1 s2: Syntax A) G (descr: Description G) v r opt1 opt2,
    In r (disj_descr descr s1 s2) ->
    opt_forall opt1 (descr_ind descr s1) ->
    opt_forall opt2 (descr_ind descr s2) ->
    r (HCons opt1 (HCons opt2 HNil)) = Some v ->
    descr_ind descr (Disjunction s1 s2) v.
Proof.
  destruct opt1; destruct opt2;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_seq_descr:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) G (descr: Description G) v r opt1 opt2,
    In r (seq_descr descr s1 s2) ->
    opt_forall opt1 (descr_ind descr s1) ->
    opt_forall opt2 (descr_ind descr s2) ->
    r (HCons opt1 (HCons opt2 HNil)) = Some v ->
    descr_ind descr (Sequence s1 s2) v.
Proof.
  destruct opt1; destruct opt2;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_map_descr:
  forall A B (f: A -> B) g (s': Syntax A) G (descr: Description G) v r opt,
    In r (map_descr descr f g s') ->
    opt_forall opt (descr_ind descr s') ->
    r (HCons opt HNil) = Some v ->
    descr_ind descr (Map f g s') v.
Proof.
  destruct opt;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_var_descr:
  forall x G (descr: Description G) v r opt,
    In r (var_descr descr x (e x)) ->
    opt_forall opt (descr_ind descr (e x)) ->
    r (HCons opt HNil) = Some v ->
    descr_ind descr (Var x) v.
Proof.
  destruct opt;
    repeat light;
    eauto with descr_ind.
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

Lemma main_type_compute_cells:
  forall num_cells N ks pre k',
    main_type (cells (compute_cells num_cells N ks pre) k') = main_type (cells N k').
Proof.
  eauto using main_type_compute_cells'.
Qed.

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

Lemma wip_cells_make_network:
  forall A (s: Syntax A) G (descr: Description G) k,
    k < sum_sizes vars + syntax_size s ->
    wip_cell descr (make_network s descr) k 0 (sum_sizes vars + syntax_size s).
Proof.
  intros; apply good_cell_wip_cell;
    eauto using good_cells_make_network;
    eauto using var_cells_make_network.
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

Lemma main_type_top:
  forall A (s: Syntax A) G (descr: Description G),
    main_type (cells (make_network s descr) (sum_sizes vars)) = A.
Proof.
  unfold make_network;
    repeat light || rewrite cell_make_network' || rewrite main_type_make_cell.
Qed.

Lemma cell_make_network:
  forall A (s : Syntax A) G (descr : Description G),
    cells (make_network s descr) (sum_sizes vars) = make_cell_with_state s descr None.
Proof.
  unfold make_network;
    repeat light || rewrite cell_make_network'.
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

Lemma fun_soundness:
  forall G (descr: Description G) A (s: Syntax A) v,
    build_fun descr s = Some v ->
    descr_ind descr s v.
Proof.
  unfold build_fun; intros.
  unshelve epose proof (wip_cells_compute_cells_make_network _ s _ descr (build_fun_obligation_1 G descr A s)) as W.
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
