Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import PeanoNat.

Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.Monotonicity.
Require Export Parser.HListCast.

Opaque compute_cells.
Opaque range.

Definition is_up_to_date (N: Network) k: Prop :=
  (exists H,
    measure (cells N k) (state (cells N k)) <=
    measure (cells N k) (update (cells N k) (cast H (h_map (fun k' => state (cells N k')) (inputs N k)))))
  \/
  (exists q, measure (cells N k) (state (cells N k)) < measure (cells N k) q).

Lemma compute_cell_up_to_date_some:
  forall N k pre N',
    compute_cell N k pre = Some N' ->
    is_up_to_date N' k.
Proof.
  unfold compute_cell, set_cell, is_up_to_date, cast;
    repeat light || destruct_match || invert_constructor_equalities;
    eauto with lia.
Qed.

Lemma compute_cell_up_to_date_none:
  forall N k pre,
    compute_cell N k pre = None ->
    is_up_to_date N k.
Proof.
  unfold compute_cell, set_cell, is_up_to_date, cast;
    repeat light || destruct_match || invert_constructor_equalities || eq_dep || clear matched.

    left.
    exists (f_equal (fun H : list Type => hlist H)
                 (PropagatorNetwork.compute_cell_obligation_1 N k pre));
            eauto with lia.
Qed.
Lemma sum_sizes_until_sum_sizes2:
  forall x n, sum_sizes_until x < sum_sizes vars + n.
Proof.
  intros.
  pose proof (sum_sizes_until_sum_sizes x); eauto with lia.
Qed.


Lemma registered_inputs_compute_cell:
  forall N k pre N',
    compute_cell N k pre = Some N' ->
    registered_inputs N ->
    registered_inputs N'.
Proof.
  unfold compute_cell, set_cell;
    repeat light || destruct_match || invert_constructor_equalities.
Qed.

Lemma compute_cell_up_to_date_some_other:
  forall N k1 k2 pre N',
    is_up_to_date N k1 ->
    k1 <> k2 ->
    ~ In k2 (inputs N k1) ->
    compute_cell N k2 pre = Some N' ->
    is_up_to_date N' k1.
Proof.
  unfold compute_cell, set_cell;
    repeat light || destruct_match || invert_constructor_equalities;
    eauto with lia.

  clear matched.

  unfold is_up_to_date in *;
    repeat light || eq_dep || destruct_match; eauto.

  left.
  unshelve eexists; repeat light || eq_dep || destruct_match.
  - eapply eq_trans; try eassumption.
    f_equal.
    apply map_ext_in;
      repeat light || eq_dep || destruct_match.
  -
(*    Notation "'<<' x '>>'" := (eq_rect _ (fun T => T) x _ _). *)
    unshelve erewrite (h_map_ext _ _ _ _
      (fun k' : nat =>
            state
              (if Nat.eq_dec k2 k'
               then
                {|
                main_type := main_type (cells N k2);
                cell_type := cell_type (cells N k2);
                input_types := input_types (cells N k2);
                update := update (cells N k2);
                measure := measure (cells N k2);
                state := update (cells N k2)
                           (eq_rect
                              (hlist (map (fun k'0 : nat => cell_type (cells N k'0)) (inputs N k2)))
                              (fun T : Type => T)
                              (h_map (fun k'0 : nat => state (cells N k'0)) (inputs N k2))
                              (hlist (input_types (cells N k2)))
                              (f_equal (fun H3 : list Type => hlist H3)
                                 (PropagatorNetwork.compute_cell_obligation_1 N k2 pre))) |}
               else cells N k'))
      (fun k' : nat => state (cells N k'))); repeat light || destruct_match.

    + f_equal. apply map_ext_in; repeat light || destruct_match.
    + repeat eq_dep. proof_irrelevance.
      rewrite H3 in H2; lights.
    + eexists; repeat light || rewrite cast_refl.
Qed.

Lemma compute_cells_up_to_date':
    forall m num_cells N ks pre k,
    (sum_measures num_cells N, length ks) = m ->
    registered_inputs N ->
    (forall k, k < num_cells -> In k ks \/ is_up_to_date N k) ->
    k < num_cells ->
    is_up_to_date (compute_cells num_cells N ks pre) k.
Proof.
  induction m using measure_induction; destruct ks;
    repeat light || compute_cells_def || destruct_match || options;
    try solve [ instantiate_any; lights ].

  - clear matched.
    revert i.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_3 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_2 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match || options.

    eapply_any; repeat light || rewrite in_app_iff in *;
      eauto using registered_inputs_compute_cell;
      try solve [ apply left_lex; eauto using compute_cell_size ].

    match goal with
    | H1: forall k, _ -> _ \/ _, H2: _ < _ |- _ => pose proof (H1 _ H2)
    end; lights;
      eauto using compute_cell_up_to_date_some.

    pose proof (Nat.eq_dec k0 n); lights;
      eauto using compute_cell_up_to_date_some.

    pose proof (in_dec Nat.eq_dec k0 (registered N n)); lights.
    unfold registered_inputs in *.
    rewrite H1 in *; eauto using compute_cell_up_to_date_some_other.


  - clear matched.
    revert n0.
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_5 num_cells N n ks pre).
    generalize (PropagatorNetwork.compute_cells_obligations_obligation_1 num_cells N n ks pre).
    repeat light || destruct_match;
      eauto 2 with lights.

    eapply_any; repeat light || rewrite in_app_iff in *;
      eauto;
      try solve [ apply right_lex; eauto using compute_cell_size ].

    match goal with
    | H1: forall k, _ -> _ \/ _, H2: _ < _ |- _ => pose proof (H1 _ H2)
    end; lights;
      eauto using compute_cell_up_to_date_none.
Qed.

Lemma compute_cells_up_to_date:
  forall G (descr: Description G) A0 (s0: Syntax A0) k,
    k < sum_sizes vars + syntax_size s0 ->
    is_up_to_date
      (compute_cells
        (sum_sizes vars + syntax_size s0)
        (make_network s0 descr)
        (range 0 (sum_sizes vars + syntax_size s0))
        (DescriptionToFunctionSoundness.build_fun_obligation_1 G descr A0 s0))
      k.
Proof.
  intros.
  eapply compute_cells_up_to_date'; repeat light || rewrite range_spec;
    eauto using registered_inputs_make_network;
    eauto with lia.
Qed.

Ltac cell_equality_transitivity :=
  match goal with
  | H1: cells ?N ?k = _, H2: cells ?N ?k = make_cell_with_state _ _ _ |- _ =>
    poseNew (Mark (H1, H2) "cell_equality_transitivity");
    pose proof (eq_trans (eq_sym H1) H2)
  end.

Ltac main_type_solve :=
  match goal with
  | H: {| main_type := _ |} = make_cell_with_state _ _ _ |- _ =>
    poseNew (Mark H "main_type_solve");
    pose proof (f_equal_dep _ main_type H);
      repeat eq_dep || cbn in * || rewrite main_type_make_cell in *
  end.

Ltac state_solve :=
  match goal with
  | H: {| main_type := _ |} = make_cell_with_state _ _ _ |- _ =>
    poseNew (Mark H "state_solve");
    pose proof (f_equal_dep _ state H);
      repeat eq_dep || cbn in * || rewrite state_make_cell in * || invert_constructor_equalities
  end.

Ltac derive_members :=
  match goal with
  | H: cells (compute_cells _ (make_network _ _) _ _) ?k = _ |- _ =>
    poseNew (Mark k "derive_members");
    pose proof (eq_sym ((f_equal_dep _ update (eq_sym H))));
    pose proof (eq_sym ((f_equal_dep _ cell_type (eq_sym H))));
    pose proof (eq_sym ((f_equal_dep _ measure (eq_sym H))));
    pose proof (eq_sym ((f_equal_dep _ state (eq_sym H))));
    pose proof (eq_sym ((f_equal_dep _ input_types (eq_sym H))))
  end; repeat eq_dep || cbn in *.

Ltac rewrite_known_input_types :=
  match goal with
  | H: input_types _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_measures :=
  match goal with
  | H: measure _ = _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_cell_types2 :=
  match goal with
  | H: cell_type _ = node_type _ _ |- _ => rewrite H in *
  end.

Lemma rules_to_update_epsilon:
  forall G (descr : Description G) A (R : Rule nil (G A)) (v : G A) (a: A) (opt: option (G A)) rules,

    R HNil = Some v ->
    In R rules ->
    (Epsilon a, opt) = rules_to_update (Epsilon a) G rules HNil ->
    is_some opt.
Proof.
  repeat light || unfold is_some || destruct_match || unfold rules_to_update in * ||
         invert_constructor_equalities;
    eauto using fold_left_not_none2.
Qed.

Lemma rules_to_update_failure:
  forall G (descr : Description G) A (R : Rule nil (G A)) (v : G A) (opt: option (G A)) rules,

    R HNil = Some v ->
    In R rules ->
    (Failure A, opt) = rules_to_update (Failure A) G rules HNil ->
    is_some opt.
Proof.
  repeat light || unfold is_some || destruct_match || unfold rules_to_update in * ||
         invert_constructor_equalities;
    eauto using fold_left_not_none2.
Qed.

Lemma rules_to_update_elem:
  forall G (descr : Description G) (R : Rule nil (G token)) (v : G token) (opt: option (G token)) rules tc,

    R HNil = Some v ->
    In R rules ->
    (Elem tc, opt) = rules_to_update (Elem tc) G rules HNil ->
    is_some opt.
Proof.
  repeat light || unfold is_some || destruct_match || unfold rules_to_update in * ||
         invert_constructor_equalities;
    eauto using fold_left_not_none2.
Qed.

Ltac rewrite_known_inputs2 :=
  match goal with
  | H:inputs _ _ = [] |- _ => rewrite H in *
  | H:inputs _ _ = _ :: _ |- _ => rewrite H in *
  end.

Ltac rewrite_known_states2 :=
  match goal with
  | H: state _ = _ |- _ => rewrite H in *
  end.

Lemma rules_to_update_monotonic_1:
  forall A T
    (R : Rule (A :: nil) T) opt0 opt1 opt2 rules,

    is_some (R (HCons opt1 HNil)) ->
    In R rules ->
    monotonic_rule_1 R ->
    is_some_is_some opt1 opt2 ->
    is_some (fold_left (fun acc f => or_else acc (f (HCons opt2 HNil))) rules opt0).
Proof.
  unfold monotonic_rule_1; unfold is_some_is_some; intros.
  apply fold_is_some with R; lights;
  eapply H1; eauto; lights.
Qed.

Lemma rules_to_update_monotonic_1':
  forall A T v
    (R : Rule (A :: nil) T) opt0 opt1 opt2 rules,

    R (HCons opt1 HNil) = Some v ->
    In R rules ->
    monotonic_rule_1 R ->
    is_some_is_some opt1 opt2 ->
    fold_left (fun acc f => or_else acc (f (HCons opt2 HNil))) rules opt0 = None ->
    False.
Proof.
  intros.
  unshelve epose proof (rules_to_update_monotonic_1 A T R opt0 opt1 opt2 rules _ _ _ _);
    repeat light || options || destruct_match.
Qed.

Lemma rules_to_update_monotonic_2:
  forall A1 A2 T
    (R : Rule (A1 :: A2 :: nil) T) opt0 opt1 opt2 opt1' opt2' rules,

    is_some (R (HCons opt1 (HCons opt2 HNil))) ->
    In R rules ->
    monotonic_rule_2 R ->
    is_some_is_some opt1 opt1' ->
    is_some_is_some opt2 opt2' ->
    is_some (fold_left (fun acc f => or_else acc (f (HCons opt1' (HCons opt2' HNil)))) rules opt0).
Proof.
  unfold monotonic_rule_2; unfold is_some_is_some; intros.
  apply fold_is_some with R; lights;
  eapply H1; eauto; lights.
  unfold are_some_are_some_2; lights.
Qed.

Lemma rules_to_update_monotonic_2':
  forall A1 A2 T v
    (R : Rule (A1 :: A2 :: nil) T) opt0 opt1 opt2 opt1' opt2' rules,

    R (HCons opt1 (HCons opt2 HNil)) = Some v ->
    In R rules ->
    monotonic_rule_2 R ->
    is_some_is_some opt1 opt1' ->
    is_some_is_some opt2 opt2' ->
    fold_left (fun acc f => or_else acc (f (HCons opt1' (HCons opt2' HNil)))) rules opt0 = None ->
    False.
Proof.
  intros.
  unshelve epose proof (rules_to_update_monotonic_2 A1 A2 T R opt0 opt1 opt2 opt1' opt2' rules _ _ _ _ _);
    repeat light || options || destruct_match.
Qed.

Ltac instantiate_wip_cells k :=
  match goal with
  | H: wip_cells _ _ _ _ |- _ =>
    poseNew (Mark k "instantiate_wip_cells");
    let W := fresh "W" in
    unshelve epose proof (H k _ _) as W; eauto with lia; unfold wip_cell in W
  end.

Ltac introduce_up :=
  match goal with
  | H: cells (compute_cells _ (make_network ?s0 ?descr) _ _) ?k = {| main_type := _ |} |- _ =>
    poseNew (Mark 0 "introduce_up");
    unshelve epose proof (compute_cells_up_to_date _ descr _ s0 k _); lights;
    unfold is_up_to_date in *; lights
  end.

Ltac revert_up :=
  match goal with
  | H: measure _ (state _) <= _ |- _ => revert H
  | H: measure _ (state _) < _ |- _ => revert H
  end.

Lemma rules_to_update_0:
  forall T (R : Rule [] T) rules opt0,

    is_some (R HNil) ->
    In R rules ->
    is_some (fold_left (fun acc f => or_else acc (f HNil)) rules opt0).
Proof.
  intros.
  apply fold_is_some with R; lights.
Qed.

Lemma rules_to_update_0':
  forall T (R : Rule [] T) rules opt0 v,

    R HNil = Some v ->
    In R rules ->
    fold_left (fun acc f => or_else acc (f HNil)) rules opt0 = None ->
    False.
Proof.
  intros.
  unshelve epose proof (rules_to_update_0 T R rules opt0 _ _);
    repeat light || destruct_match || rewrite_any.
Qed.

Ltac generalize_lt_right :=
  match goal with
  | |- context[measure _ _ < measure ?c ?q] => generalize q
  end.

Lemma small_node_measure:
  forall A G (q: node_type A G), 1 < node_measure q -> False.
Proof.
  unfold node_measure;
    repeat light || destruct_match; try lia.
Qed.

Lemma fun_completeness':
  forall G (descr: Description G) A (s: Syntax A) v A0 (s0: Syntax A0),
    descr_ind descr s v ->
    monotonic_descr descr ->
    wip_cells descr
      (compute_cells (sum_sizes vars + syntax_size s0)
                          (make_network s0 descr)
                          (range 0 (sum_sizes vars + syntax_size s0))
                          (DescriptionToFunctionSoundness.build_fun_obligation_1 G descr A0 s0))
      0 (sum_sizes vars + syntax_size s0) ->
    forall k opt,
      cells (compute_cells (sum_sizes vars + syntax_size s0)
                            (make_network s0 descr)
                            (range 0 (sum_sizes vars + syntax_size s0))
                            (DescriptionToFunctionSoundness.build_fun_obligation_1 G descr A0 s0))
            k =
        make_cell_with_state s descr opt ->
      k < sum_sizes vars + syntax_size s0 ->
      is_some opt.
Proof.
  induction 1;
    try solve [
      repeat light || destruct_match || cell_equality_transitivity ||
           unshelve instantiate_wip_cells k ||
           unshelve instantiate_wip_cells k0 ||
           invert_constructor_equalities || rewrite_known_inputs2 || eq_dep ||
           main_type_solve || state_solve; try (
        introduce_up; revert_up; try generalize_lt_right; repeat derive_members;
        repeat rewrite_known_updates; repeat eq_dep || cbn || generalize_proofs;
        repeat rewrite_known_measures; repeat eq_dep || cbn || generalize_proofs;
        repeat rewrite_known_input_types; repeat eq_dep || cbn || generalize_proofs;
        repeat rewrite_known_inputs2; repeat eq_dep || cbn || generalize_proofs;
        repeat rewrite_known_states2;
          repeat eq_dep || generalize_proofs || rewrite state_make_cell;
        repeat rewrite_known_cell_types;
          repeat eq_dep || cbn || generalize_proofs || light ||
                 rewrite cast_hcons in * ||
                 rewrite cast_hcons2 in *;
        repeat unfold rules_to_update in * || invert_constructor_equalities;
          try solve [ repeat light || destruct_match; try lia; eauto using rules_to_update_0' ];
          try solve [ repeat light || destruct_match; eauto using small_node_measure ];
          try solve [ repeat light || destruct_match;
                      try lia; eapply rules_to_update_monotonic_1';  eauto;
            try solve [ unfold monotonic_descr in *; repeat light; eauto ];
            try solve [ unfold is_some_is_some; lights;
                        eauto using sum_sizes_until_sum_sizes2 with lia ]
          ];
          try solve [ repeat light || destruct_match;
                      try lia; eapply rules_to_update_monotonic_2';  eauto;
            try solve [ unfold monotonic_descr in *; repeat light; eauto ];
            try solve [ unfold is_some_is_some; lights;
                        eauto using sum_sizes_until_sum_sizes2 with lia ]
          ]
      )
    ].
Qed.

Lemma fun_completeness:
  forall G (descr: Description G) A (s: Syntax A) v,
    descr_ind descr s v ->
    monotonic_descr descr ->
    is_some (build_fun descr s).
Proof.
  unfold build_fun;
    repeat light.

  match goal with
  | |- context[compute_cells ?num_cells ?N ?ks ?pre] =>
    unshelve epose proof (compute_cells_still_make_cell
      A s G descr N (sum_sizes vars) num_cells ks None pre _
    )
  end;
    eauto using cell_make_network; lights.

  apply fun_completeness' with descr s v A s (sum_sizes vars);
    repeat light || apply wip_cells_compute_cells || unfold wip_cells ||
           rewrite range_spec in * || syntax_size_gt_0;
    eauto using sum_sizes_until_sum_sizes2;
    eauto using wip_cells_make_network;
    eauto with lia;
    eauto using var_cells_make_network.

  - repeat derive_members.
    rewrite_known_states2; repeat cbn || eq_dep || rewrite state_make_cell; lights.
Qed.
