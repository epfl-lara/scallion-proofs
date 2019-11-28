Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Description.
Require Export Parser.CommonRules.

Definition productive_descr: Description (fun A => unit) := {|
  epsilon_descr := fun A a => [ some_rule tt ];
  failure_descr := fun A => [];
  token_descr := fun k => [ some_rule tt ];
  map_descr := fun _ _ _ _ _ => [ id_rule ] ;
  disj_descr := fun A _ _ => [ disj_rule ];
  seq_descr := fun A B _ _ => [ combine_rule (fun _ _ => tt) ];
  var_descr := fun x _  => [ id_rule ];
|}.
