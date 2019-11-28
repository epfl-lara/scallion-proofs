Require Import Coq.Lists.List.
Import ListNotations.

Require Import Parser.Structures.
Require Import Parser.List.

Require Import Parser.NullableFun.
Require Import Parser.ProductiveFun.

Require Export Parser.Description.
Require Export Parser.CommonRules.

Definition first_descr (k: token_class): Description (fun A => unit) := {|
  epsilon_descr := fun A a => [];
  failure_descr := fun A => [];
  token_descr := fun k' => when_sum (class_eq_dec k k') [ some_rule tt ];
  map_descr := fun _ _ _ _ _ => [ @id_rule unit ];
  disj_descr := fun _ _ _ => [ disj_rule ];
  seq_descr :=
    fun _ _ s1 s2 =>
      when (productive_fun s2) [ left_rule ] ++ when_opt (nullable_fun s1) [ right_rule ];
  var_descr := fun _ _ => [ @id_rule unit ];
|}.
