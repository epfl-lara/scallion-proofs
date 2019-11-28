Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.List.

Polymorphic Inductive hlist: list Type -> Type :=
| HNil: hlist nil
| HCons { X } { XS: list Type } (x: X) (xs: hlist XS): hlist (X :: XS)
.

Fixpoint support (l: list { A: Type & A }): list Type :=
  match l with
  | nil => nil
  | cons (existT _ A _) xs => A :: support xs
  end
.

Fixpoint list_to_hlist (l: list { A: Type & A }): hlist (support l) :=
  match l with
  | [] => HNil
  | existT _ _ x :: xs => HCons x (list_to_hlist xs)
  end
.

Lemma dep_support:
  forall T (l : list T) x y,
    support (map (fun k' => existT (fun A => A) (x k') (y k')) l) =
    map (fun k' => x k') l.
Proof.
  induction l; repeat light || f_equal.
Qed.

Program Definition h_head { A AS } (hl: hlist (A :: AS)): A :=
  match hl in hlist L return forall H: L = A :: AS, head L _ with
  | HCons a _ => fun _ => a
  | _ => _
  end eq_refl.

Fail Next Obligation. (* no more obligations for h_head *)

Program Definition h_tail { A AS } (hl: hlist (A :: AS)): hlist AS :=
  match hl in hlist L return forall H: L = A :: AS, hlist (tail L _) with
  | HCons _ xs => fun _ => xs
  | _ => _
  end eq_refl.

Fail Next Obligation. (* no more obligations for h_tail *)

Fixpoint h_map { T } { F: T -> Type } (f: forall t, F t) (l: list T): hlist (map F l) :=
  match l as l' return hlist (map F l') with
  | [] => HNil
  | x :: xs => HCons (f x) (h_map f xs)
  end.
