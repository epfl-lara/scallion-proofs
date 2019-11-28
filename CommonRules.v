Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Description.
Require Export Parser.Option.

Definition disj_rule { A }: Rule [A; A] A :=
  fun (premises: hlist [ option A; option A ]) =>
    let opt1: option A := h_head premises in
    let opt2: option A := h_head (h_tail premises) in
    or_else opt1 opt2.

Definition id_rule { A }: Rule [A] A :=
  fun (premises: hlist [ option A ]) =>
    h_head premises.

Definition some_rule { AS A } (a: A): Rule AS A :=
  fun _ => Some a.

Definition map_rule { A B } (f: A -> B): Rule [A] B :=
  fun (premises: hlist [ option A ]) =>
    let opt: option A := h_head premises in
    option_map f opt.

Definition combine_rule { A1 A2 A: Type } (f: A1 -> A2 -> A): Rule [A1; A2] A :=
  fun (premises: hlist [ option A1; option A2 ]) =>
    let opt1: option A1 := h_head premises in
    let opt2: option A2 := h_head (h_tail premises) in
    option_flat_map (fun v1 => option_map (fun v2 => f v1 v2) opt2) opt1.

Definition left_rule { A1 A2: Type }: Rule [A1; A2] A1 :=
  fun (premises: hlist [ option A1; option A2 ]) =>
    h_head premises.

Definition right_rule { A1 A2: Type }: Rule [A1; A2] A2 :=
  fun (premises: hlist [ option A1; option A2 ]) =>
    h_head (h_tail premises).

Ltac rules :=
  unfold disj_rule in * ||
  unfold id_rule in * ||
  unfold some_rule in * ||
  unfold map_rule in * ||
  unfold combine_rule in * ||
  unfold left_rule in * ||
  unfold right_rule in *.
