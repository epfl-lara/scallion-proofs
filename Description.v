Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.HList.

(* This describes a function on syntaxes, with type, forall A, Syntax A -> F A *)

Definition Rule (AS: list Type) (B: Type): Type := hlist (map option AS) -> option B.

Record Description (G: Type -> Type) := mkDescription {
  epsilon_descr: forall A, A -> list (Rule [] (G A));
  failure_descr: forall A, list (Rule [] (G A));
  token_descr: token_class ->  list (Rule [] (G token));
  map_descr: forall A B, (A -> B) -> (B -> list A) -> Syntax A -> list (Rule [G A] (G B));
  disj_descr: forall A, Syntax A -> Syntax A -> list (Rule [G A; G A] (G A));
  seq_descr: forall A1 A2, Syntax A1 -> Syntax A2 -> list (Rule [G A1; G A2] (G (A1 * A2)%type));
  var_descr: forall x, Syntax (get_type x) -> list (Rule [G (get_type x)] (G (get_type x)));
}.

Arguments epsilon_descr { G } d { A }.
Arguments failure_descr { G }.
Arguments token_descr { G }.
Arguments map_descr { G } d { A B }.
Arguments disj_descr { G } d { A }.
Arguments seq_descr { G } d { A1 A2 }.
Arguments var_descr { G }.
