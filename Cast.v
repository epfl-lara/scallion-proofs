Require Import Coq.Strings.String.

Require Export Parser.Structures.

Polymorphic Definition cast { A B } (p: A = B) (v: A): B := eq_rect A (fun T => T) v B p.

Definition cast_syntax { A B } (p: A = B) (s: Syntax A): Syntax B :=
  eq_rect A (fun T => Syntax T) s B p.

Lemma cast_refl:
  forall A (v: A), cast eq_refl v = v.
Proof.
  lights.
Qed.

Lemma cast_syntax_refl:
  forall A (s: Syntax A), cast_syntax eq_refl s = s.
Proof.
  lights.
Qed.

Ltac cast_refl :=
  rewrite cast_refl in * ||
  rewrite cast_syntax_refl in *.


(** Proof Irrelevance axiom **)

Axiom UIP: forall A (x y: A) (p1 p2: x = y), p1 = p2.
Arguments UIP { A x y}.

Lemma proofs_refl:
  forall (A: Type) (x: A) (H: x = x), H = eq_refl.
Proof.
  intros.
  apply UIP.
Qed.

Polymorphic Lemma cast_irrelevance:
  forall A H (x: A), cast H x = x.
Proof.
  intros A H.
  intros.
  pose proof (proofs_refl _ _ H) as HR.
  rewrite HR.
  lights.
Qed.

Polymorphic Lemma eq_rekt:
  forall A (x1 x2: A) (F: A -> Type) (y: F x1) (H: x1 = x2),
    eq_rect x1 F y x2 H = eq_rect (F x1) (fun T => T) y (F x2) (f_equal F H).
Proof.
  intros.
  destruct H; lights.
Qed.

Lemma eq_rect_irrelevance:
  forall A (x1 x2: A) (F: A -> Type) (y: F x1) (H H': x1 = x2),
    eq_rect x1 F y x2 H = eq_rect x1 F y x2 H'.
Proof.
  destruct H; lights.
  pose proof (proofs_refl _ _ H') as HR.
  rewrite HR; lights.
Qed.

Lemma eq_rect_irrelevance2:
  forall (x1 x2: Type) (y: x1) (H H': x1 = x2),
    eq_rect x1 (fun T => T) y x2 H = eq_rect x1 (fun T => T) y x2 H'.
Proof.
  destruct H; lights.
  pose proof (proofs_refl _ _ H') as HR.
  rewrite HR; lights.
Qed.

Ltac proofs_refl :=
  match goal with
  | H: context[eq_rect _ _ _ _ ?H'] |- _ => progress (rewrite (proofs_refl _ _ H') in H)
  | |- context[eq_rect _ _ _ _ ?H'] => progress (rewrite (proofs_refl _ _ H'))
  end.

Ltac generalize_proofs :=
  repeat match goal with
  | |- context[eq_rect _ _ _ _ ?H] => generalize H
  | |- context[cast ?H _] => generalize H
  end.

Ltac eq_rekt :=
  match goal with
  | |- context[eq_rect ?x1 ?P ?y ?x2 ?H] =>
    tryif unify P (fun (T: Type) => T)
    then fail
    else rewrite (eq_rekt _ x1 x2 P y H) in *
  | H: context[eq_rect ?x1 ?P ?y ?x2 ?H] |- _ =>
    tryif unify P (fun (T: Type) => T)
    then fail
    else rewrite (eq_rekt _ x1 x2 P y H) in *
  end.

Ltac eq_dep' := proofs_refl || (unfold cast in *) || eq_rekt || rewrite rew_compose in *.

Lemma eq_rect_reverse:
  forall (T1 T2: Type) H H' y y',
    eq_rect T1 (fun T: Type => T) y T2 H = eq_rect T1 (fun T: Type => T) y' T2 H' ->
    y = y'.
Proof.
  intros T1 T2 H H' y y' HE.
  pose proof (f_equal (fun z => eq_rect T2 (fun T: Type => T) z T1 (eq_sym H)) HE);
    repeat light || eq_dep'.
Qed.

Ltac eq_dep := apply_anywhere eq_rect_reverse || eq_dep'.

Ltac proof_irrelevance :=
  match goal with
  | H: context[eq_rect _ _ _ _ ?p1] |- context[eq_rect _ _ _ _ ?p2] =>
    not_unify p1 p2;
    poseNew (Mark (p1, p2) "proof_irrelevance");
    pose proof (UIP p1 p2)
  | H1: context[eq_rect _ _ _ _ ?p1], H2: context[eq_rect _ _ _ _ ?p2] |- _ =>
    not_unify p1 p2;
    poseNew (Mark (p1, p2) "proof_irrelevance");
    pose proof (UIP p1 p2)
  | |- context[eq_rect _ _ _ _ ?p1] =>
    match goal with
    | |- context[eq_rect _ _ _ _ ?p2] =>
      not_unify p1 p2;
      poseNew (Mark (p1, p2) "proof_irrelevance");
      pose proof (UIP p1 p2)
    end
  end.
