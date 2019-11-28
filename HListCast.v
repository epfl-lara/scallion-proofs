Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.HList.
Require Export Parser.Cast.

Lemma cast_head_tail:
  forall T1 T2 TS1 TS2 (t: T1) (ts: hlist TS1) HT (HTS: TS1 = TS2) H,
    exists H',
    HCons
      (eq_rect T1 (fun T => T) t T2 HT)
      (eq_rect (hlist TS1) (fun T => T) ts (hlist TS2) H) =
    eq_rect _ (fun T => T) (HCons t ts) _ H'.
Proof.
  repeat light || eq_dep || exists eq_refl.
Qed.

Lemma h_map_ext:
  forall T l (F1 F2: T -> Type) (f1: forall t, F1 t) (f2: forall t, F2 t) H,
    (forall x, In x l -> exists Hx, f1 x = cast Hx (f2 x)) ->
    h_map f1 l = eq_rect _ (fun T => T) (h_map f2 l) _ H.
Proof.
  induction l;
    repeat light || eq_dep.

  pose proof (H0 a); lights.
  unshelve epose proof (IHl F1 F2 f1 f2 _ _);
    repeat light.
  - f_equal. apply map_ext_in; lights.
    pose proof (H0 a0); lights.
  - rewrite H1. rewrite H2.
    match goal with
    | |- context[HCons (eq_rect ?T1 _ ?t ?T2 ?HT) (eq_rect (hlist ?TS1) _ ?ts (hlist ?TS2) ?H)] =>
      unshelve epose proof (cast_head_tail T1 T2 TS1 TS2 t ts HT _ H)
    end; lights.
    + apply map_ext_in; lights.
      pose proof (H0 a0); lights.
    + rewrite_any; proof_irrelevance; lights.
Qed.

Lemma cast_hcons:
  forall A B b H1 H2,
    eq_rect
      (hlist (A :: nil))
      (fun T : Type => T)
      (HCons (eq_rect B (fun T : Type => T) b A H1) HNil)
      (hlist (B :: nil))
      H2 =
    HCons b HNil.
Proof.
  lights;
    repeat eq_dep || cbn || f_equal.
Qed.

Lemma cast_hcons2:
  forall A A' B B' b b' H1 H1' H2,
    eq_rect
      (hlist (A :: A' :: nil))
      (fun T : Type => T)
      (HCons (eq_rect B (fun T : Type => T) b A H1)
        (HCons (eq_rect B' (fun T: Type => T) b' A' H1')
          HNil))
      (hlist (B :: B' :: nil))
      H2 =
    HCons b (HCons b' HNil).
Proof.
  lights;
    repeat eq_dep || cbn || f_equal.
Qed.

