Require Import Coq.Lists.List.

Require Export Parser.Description.
Require Export Parser.Option.

Definition is_some_is_some { A } { B } (opt1: option A) (opt2: option B): Prop :=
  is_some opt1 ->
  is_some opt2.

Definition are_some_are_some_1
           { A } { B }
           (hl1: hlist (option A :: nil)) (hl2: hlist (option B :: nil)): Prop :=

  is_some_is_some (h_head hl1) (h_head hl2).

Definition are_some_are_some_2
           { A1 A2 } { B1 B2 }
           (hl1: hlist (option A1 :: option A2 :: nil))
           (hl2: hlist (option B1 :: option B2 :: nil)): Prop :=

  is_some_is_some (h_head hl1) (h_head hl2) /\
  is_some_is_some (h_head (h_tail hl1)) (h_head (h_tail hl2)).

Definition monotonic_rule_1 { A B } (f: hlist (option A :: nil) -> option B): Prop :=
  forall hl1 hl2,
    are_some_are_some_1 hl1 hl2 ->
    is_some_is_some (f hl1) (f hl2).

Definition monotonic_rule_2 { A1 A2 B } (f: hlist (option A1 :: option A2 :: nil) -> option B): Prop :=
  forall hl1 hl2,
    are_some_are_some_2 hl1 hl2 ->
    is_some_is_some (f hl1) (f hl2).

Definition monotonic_descr { G } (descr: Description G): Prop :=
  (forall A B (f: A -> B) g (s: Syntax A) R, In R (map_descr descr f g s) -> monotonic_rule_1 R) /\
  (forall A (s1 s2: Syntax A) R, In R (disj_descr descr s1 s2) -> monotonic_rule_2 R) /\
  (forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) R, In R (seq_descr descr s1 s2) -> monotonic_rule_2 R) /\
  (forall x R, In R (var_descr descr x (e x)) -> monotonic_rule_1 R).
