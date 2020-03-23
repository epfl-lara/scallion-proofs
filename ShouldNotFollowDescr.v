Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.Option.
Require Export Parser.List.
Require Export Parser.DescriptionInd.
Require Export Parser.CommonRules.
Require Export Parser.NullableFun.
Require Export Parser.ProductiveFun.
Require Export Parser.FirstFun.

Open Scope bool_scope.

Search in_dec.

Definition should_not_follow_descr (k: token_class): Description (fun A => unit) := {|
  epsilon_descr := fun A a => [];
  failure_descr := fun A => [];
  token_descr := fun k' => [];
  map_descr := fun _ _ _ _ _ => [ @id_rule unit ];
  disj_descr := fun _ s1 s2 =>
    [ disj_rule ] ++
    when_opt (nullable_fun s2) (when_sum (in_dec kind_eq_dec k (first_fun s1)) [ some_rule tt ])  ++
    when_opt (nullable_fun s1) (when_sum (in_dec kind_eq_dec k (first_fun s2)) [ some_rule tt ]);
  seq_descr :=
    fun _ _ s1 s2 =>
      when_opt (nullable_fun s2) [ left_rule ] ++
      when (productive_fun s1) [ right_rule ];
  var_descr := fun _ _ => [ @id_rule unit ];
|}.
