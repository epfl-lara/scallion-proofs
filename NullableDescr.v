Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.CommonRules.

Definition nullable_descr: Description (fun A => A) := {|
  epsilon_descr := fun A a => [ some_rule a ];
  failure_descr := fun A => [];
  token_descr := fun k => [];
  map_descr := fun A B f _ _ => [ map_rule f ];
  disj_descr := fun A _ _ => [ disj_rule ];
  seq_descr := fun A B _ _ => [ combine_rule (fun v1 v2 => (v1, v2)) ];
  var_descr := fun x _ => [ id_rule ];
|}.
