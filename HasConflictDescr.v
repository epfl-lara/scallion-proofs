Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Option.
Require Export Parser.List.
Require Export Parser.DescriptionToFunctionSoundness.
Require Export Parser.DescriptionToFunctionCompleteness.

Require Export  Parser.NullableFun.
Require Export Parser.ProductiveFun.
Require Export Parser.FirstFun.
Require Export Parser.ShouldNotFollowFun.
Require Export Parser.CommonRules.

Definition has_conflict_descr: Description (fun A => unit) := {|
  epsilon_descr := fun A a => [];
  failure_descr := fun A => [];
  token_descr := fun k => [];
  map_descr := fun _ _ _ _ _ => [ @id_rule unit ];
  disj_descr := fun _ s1 s2 =>
    left_rule :: right_rule ::
    when (negb (disjoint kind_eq_dec (first_fun s1) (first_fun s2))) [ some_rule tt ] ++
    when (is_some_b (nullable_fun s1) && is_some_b (nullable_fun s2)) [ some_rule tt ];
  seq_descr := fun _ _ s1 s2 =>
    left_rule :: right_rule ::
    when (negb (disjoint kind_eq_dec (should_not_follow_fun s1) (first_fun s2))) [ some_rule tt ];
  var_descr := fun _ _ => [ @id_rule unit ];
|}.
