Require Export Equations.Prop.Subterm. (* lexicographic ordering *)

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.Tactics.

Definition wf_lex := wellfounded_lexprod nat nat lt lt lt_wf lt_wf.
Definition lt_lex: (nat * nat) -> (nat * nat) -> Prop := lexprod nat nat lt lt.
Notation "p1 '<<' p2" := (lt_lex p1 p2) (at level 80).

Lemma measure_induction:
  forall P,
    (forall m, (forall m', m' << m -> P m') -> P m) ->
    (forall m, P m).
Proof.
  lights.
  pose proof (wf_lex (a, b)) as H.
  induction H; lights.
Qed.

Lemma leq_lt_lex:
  forall a1 b1 a2 b2,
    a1 <= a2 ->
    b1 < b2 ->
    (a1, b1) << (a2, b2).
Proof.
  unfold "<<"; intros.
  destruct (Nat.eq_dec a1 a2); lights;
    eauto using right_lex, left_lex with lia.
Qed.

Ltac lex :=
  solve [ apply left_lex; lia ] ||
  solve [ apply leq_lt_lex; lia ].

Hint Extern 1 => lex: lex.
