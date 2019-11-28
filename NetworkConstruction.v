Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.PropagatorNetwork.
Require Export Parser.Option.
Require Export Parser.Structures.
Require Export Parser.Description.

Open Scope type_scope.

Definition node_type (A: Type) (G: Type -> Type): Type := Syntax A * option (G A).

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
