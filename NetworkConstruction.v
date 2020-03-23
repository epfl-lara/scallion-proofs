Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.PropagatorNetwork.
Require Export Parser.Description.
Require Export Parser.Cast.

Open Scope type_scope.

Definition node_type (A: Type) (G: Type -> Type): Type := Syntax A * option (G A).

Ltac rewrite_known_cell_types2 :=
  match goal with
  | H: cell_type _ = node_type _ _ |- _ => rewrite H in *
  end.

Definition node_measure { A G } (n: node_type A G): nat :=
  match n with
  | (_, None) => 1
  | (_, Some _) => 0
  end.

Definition get_input_types { A } (s: Syntax A): list Type :=
  match s with
  | Epsilon _ => []
  | Failure _ => []
  | Elem _ => []
  | @Disjunction A _ _ => [ A; A ]
  | @Sequence A1 A2 _ _ => [A1; A2]
  | @Map A B _ _ _ => [ A ]
  | Var x =>  [ get_type x ]
  end.

Fixpoint map_snd { F G } (l: list Type) (hl: hlist (map (fun A => F A * G A) l)):
    hlist (map G l) :=

  match l as l return hlist (map (fun A => F A * G A) l) -> hlist (map G l)  with
  | [] => fun hl => HNil
  | _ :: Ts => fun hl => HCons (snd (h_head hl)) (map_snd Ts (h_tail hl))
  end hl.

Fixpoint map_expand { F G: Type -> Type } (l: list Type) (hl: hlist (map (fun A => F (G A)) l)):
    hlist (map F (map G l)) :=

  match l as l return hlist (map (fun A => F (G A)) l) -> hlist (map F (map G l)) with
  | [] => fun hl => HNil
  | _ :: Ts => fun hl => HCons (h_head hl) (map_expand Ts (h_tail hl))
  end hl.

Definition rules_to_update { A } (s: Syntax A) (G: Type -> Type)
             (rules: list (Rule (map G (get_input_types s)) (G A)))
             (inputs: hlist (map (fun A => node_type A G) (get_input_types s))): node_type A G :=
    (s, @fold_left
      (option (G A))
      (Rule (map G (get_input_types s)) (G A))
        (fun acc r => or_else acc (r (@map_expand option G (get_input_types s)
                                               (map_snd (get_input_types s) inputs))))
        rules
        None).

Definition make_cell_with_state
  { A G } (s: Syntax A) (descr: Description G) (opt: option (G A)): Cell :=

  match s in Syntax A' return option (G A') -> Cell with
  | @Epsilon A v as s => fun opt =>
      @mkCell A (node_type A G) [] (rules_to_update s G (epsilon_descr descr v)) node_measure (s, opt)
  | Failure A as s => fun opt =>
      @mkCell A (node_type A G) [] (rules_to_update s G (failure_descr descr A)) node_measure (s, opt)
  | Elem tc as s => fun opt =>
      @mkCell A (node_type token G) [] (rules_to_update s G (token_descr descr tc))
              node_measure (s, opt)
  | @Disjunction A s1 s2 as s => fun opt =>
      @mkCell A (node_type A G) [node_type A G; node_type A G] (rules_to_update s G (disj_descr descr s1 s2)) node_measure (s, opt)
  | @Sequence A1 A2 s1 s2 as s => fun opt =>
      @mkCell (A1 * A2) (node_type (A1 * A2) G) [ node_type A1 G; node_type A2 G ]
              (rules_to_update s G (seq_descr descr s1 s2))
              node_measure (s, opt)
  | @Map A B f g s' as s => fun opt =>
      @mkCell B (node_type B G) [ node_type A G ] (rules_to_update s G (map_descr descr f g s'))
              node_measure (s, opt)
  | Var x as s => fun opt =>
      @mkCell (get_type x) (node_type (get_type x) G) [ node_type (get_type x) G ]
              (rules_to_update s G (var_descr descr x (e x)))
             node_measure (s, opt)
  end opt.

Fixpoint make_network' { A G }
  (s: Syntax A) (descr: Description G) (k: nat) (N: Network): Network :=

  let cell: Cell := make_cell_with_state s descr None in
  match s with
  | Epsilon v =>
      set_cell_with_inputs N k cell []

  | Failure A =>
      set_cell_with_inputs N k cell []

  | Elem tc =>
      set_cell_with_inputs N k cell []

  | Disjunction s1 s2 =>
      let N1 := make_network' s1 descr (S k) N in
      let N2 := make_network' s2 descr (S (k + syntax_size s1)) N1 in
      set_cell_with_inputs N2 k cell [ S k; S (k + syntax_size s1) ]

  | Sequence s1 s2 =>
      let N1 := make_network' s1 descr (S k) N in
      let N2 := make_network' s2 descr (S (k + syntax_size s1)) N1 in
      set_cell_with_inputs N2 k cell [S k; (S (k + syntax_size s1)) ]

  | Map f g s' =>
      let N' := make_network' s' descr (S k) N in
      set_cell_with_inputs N' k cell [ S k ]

  | Var x =>
      set_cell_with_inputs N k cell [ sum_sizes_until x ]
  end
.

Fail Next Obligation. (* no more obligations for `make_network'` *)

Definition empty_cell: Cell :=
  @mkCell unit unit nil (fun _ => tt) (fun _ => 0) tt.

Definition empty_network: Network :=
  mkNetwork (fun _ => empty_cell) (fun _ => nil) (fun _ => nil).

Definition init_env_network { G } (descr: Description G): Network :=
  fold_left
    (fun N x => make_network' (e x) descr (sum_sizes_until x) N)
    vars
    empty_network.

Definition make_network { A G } (s: Syntax A) (descr: Description G): Network :=
  make_network' s descr (sum_sizes vars) (init_env_network descr).


(** A few simple lemmas about cell construction *)

Lemma main_type_make_cell:
  forall A (s: Syntax A) G (descr: Description G) (opt: option (G A)),
    main_type (make_cell_with_state s descr opt) = A.
Proof.
  unfold make_cell_with_state;
    repeat light || destruct_match.
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

Lemma cell_type_node_type:
  forall G (descr : Description G) A (s: Syntax A) opt,
    cell_type (make_cell_with_state s descr opt) = node_type A G.
Proof.
  unfold make_cell_with_state;
    repeat light || destruct_match.
Qed.


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

Ltac equal_main_types :=
  match goal with
  | H: cells ?N ?k = _ |- _ => add_equal_dep2 H main_type (cells N k)
  end.

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
