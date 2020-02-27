Require Import Equations.Init.
Require Import Equations.Equations.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import PeanoNat.
Require Import Psatz.

Require Export Parser.Option.

(* Basic list rewrites *)
Ltac list_rewrites := rewrite List.app_nil_l in * || rewrite List.app_nil_r in *.
Hint Extern 1 => list_rewrites : list_rewrites.

Definition sublist { T } (xs1 xs2: list T) := exists pre post,
  app (app pre xs1) post = xs2.

Lemma sublist_refl: forall T (xs: list T), sublist xs xs.
Proof.
  unfold sublist; intros; eauto with list_rewrites.
Qed.

Lemma sublist_right: forall T (xs ys: list T),
  sublist xs (xs ++ ys).
Proof.
  unfold sublist; lights.
  exists nil, ys; eauto with datatypes.
Qed.

Lemma sublist_left: forall T (xs ys: list T),
  sublist xs (ys ++ xs).
Proof.
  unfold sublist; lights.
  exists ys, nil; eauto with datatypes.
Qed.

Lemma sublist_trans: forall T (xs ys zs: list T),
  sublist xs ys ->
  sublist ys zs ->
  sublist xs zs.
Proof.
  unfold sublist; lights.
  exists (pre ++ pre0), (post0 ++ post); repeat light || rewrite app_assoc.
Qed.

Lemma sublist_right_right: forall T (xs ys zs: list T),
  sublist xs ys ->
  sublist xs (ys ++ zs).
Proof.
  intros; eauto using sublist_trans, sublist_right.
Qed.

Lemma sublist_right_left: forall T (xs ys zs: list T),
  sublist xs ys ->
  sublist xs (zs ++ ys).
Proof.
  intros; eauto using sublist_trans, sublist_left.
Qed.

Lemma sublist_nil: forall T (xs: list T),
  sublist xs nil ->
  xs = nil.
Proof.
  unfold sublist; destruct xs; lights.
  destruct pre; lights.
Qed.

Ltac t_sublist_nil :=
  match goal with
  | H: sublist ?xs nil |- _ =>
    pose proof (sublist_nil _ _ H); clear H
  end.

Ltac t_app_inv :=
  match goal with
  | H: ?l ++ _ = ?l ++ _ |- _ => apply app_inv_head in H
  | H: _ ++ ?l = _ ++ ?l |- _ => apply app_inv_tail in H
  end.

Lemma app_eq_nil_equiv:
  forall A (xs xs': list A), xs ++ xs' = [] <-> (xs = [] /\ xs' = []).
Proof.
  lights; apply app_eq_nil in H; lights.
Qed.

Ltac t_app_eq_nil :=
  rewrite app_eq_nil_equiv in * ||
  match goal with
  | H: nil = _ ++ _ |- _ =>
    apply eq_sym in H; rewrite app_eq_nil_equiv in H
  end.

Ltac app_cons_destruct :=
  match goal with
  | H: ?xs1 ++ _ = ?xs2 :: _ |- _ => is_var xs1; is_var xs2; destruct xs1
  | H: ?xs1 :: _ = ?xs2 ++ _ |- _ => is_var xs1; is_var xs2; destruct xs2
  end.

Definition when {A: Type} (b : bool) (xs : list A) : list A :=
  if b then xs else nil.

Definition when_opt {A B : Type} (opt : option A) (xs : list B) : list B :=
  if opt then xs else nil.

Definition when_sum { A B: Prop } { C : Type } (sum : { A } + { B }) (xs : list C) : list C :=
  if sum then xs else nil.

Lemma Forall_app:
  forall T (P: T -> Prop) (l1: list T) (l2: list T),
    Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
Proof.
  induction l1; repeat light || invert_pred Forall || rewrite_any || constructor.
Qed.

Ltac lists :=
  unfold when in * ||
  unfold when_opt in * ||
  unfold when_sum in * ||
  list_rewrites ||
  (rewrite in_app_iff in *) ||
  (rewrite Forall_app in *) ||
  t_app_eq_nil ||
  t_app_inv ||
  t_sublist_nil.

Hint Extern 1 => lists: lists.

Lemma split_in:
  forall T (xs: list T) (t: T),
    In t xs ->
    exists pre post,
      xs = pre ++ t :: post.
Proof.
  induction xs; repeat light || instantiate_any; eauto with lists datatypes.
Qed.

Ltac t_split_in :=
  match goal with
  | H: In ?t ?xs |- _ =>
    is_var xs;
    pose proof (split_in _ _ _ H)
  end.

Lemma app_cons_in:
  forall T (ys1 ys2 xs: list T) t,
    xs = ys1 ++ t :: ys2 ->
    In t xs.
Proof.
  induction ys1; repeat light; eauto with datatypes.
Qed.

(*  Two cases:                          *)
(*  *     [      xs1  ] [  xs2 ]        *)
(*        [ ys1 ] t [    ys2   ]        *)
(*   or                                 *)
(*  *     [  xs1  ]  [      xs2      ]  *)
(*        [       ys1    ] t [  ys2  ]  *)
Lemma app_app_cons:
  forall T (ys1 ys2 xs1 xs2: list T) t,
    xs1 ++ xs2 = ys1 ++ t :: ys2 ->
    (exists mid,
        (xs1 = ys1 ++ t :: mid /\ mid ++ xs2 = ys2) \/
        (ys1 = xs1 ++ mid /\ mid ++ t :: ys2 = xs2)).
Proof.
  induction ys1; repeat light || app_cons_destruct || instantiate_any || invert_constructor_equalities;
    eauto.
Qed.

Lemma forallb_forall_false:
  forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false <-> (exists x : A, In x l /\ f x = false).
Proof.
  induction l;
    repeat light || bools; eauto.
Qed.

Definition disjoint { T } (eq_dec: forall n m: T, { n = m } + { ~ n = m }) xs ys : bool :=
  forallb (fun x => forallb (fun y => if (eq_dec x y) then false else true) ys) xs.

Theorem disjoint_true_spec_1 : forall T eq_dec (xs ys: list T),
  disjoint eq_dec xs ys = true ->
  (forall x, In x xs -> In x ys -> False).
Proof.
  unfold disjoint; induction xs;
    repeat light || bools || eapply_any || rewrite forallb_forall in * || instantiate_any || nats || destruct_match.
Qed.

Theorem disjoint_true_spec_2 : forall T eq_dec (xs ys: list T),
  (forall x y, In x xs -> In y ys -> x <> y) ->
  disjoint eq_dec xs ys = true.
Proof.
  unfold disjoint; induction xs;
    repeat light || bools || eapply_any || rewrite forallb_forall in * || instantiate_any || nats || destruct_match;
    eauto with exfalso.
Qed.

Theorem disjoint_true_spec : forall T eq_dec (xs ys: list T),
  (forall x y, In x xs -> In y ys -> x <> y) <->
  disjoint eq_dec xs ys = true.
Proof.
  lights; eauto using disjoint_true_spec_1, disjoint_true_spec_2.
Qed.

Theorem disjoint_false_spec_1 : forall T eq_dec (xs ys: list T),
  disjoint eq_dec xs ys = false ->
  exists k,
  In k xs /\
  In k ys.
Proof.
  unfold disjoint; induction xs;
    repeat light || bools || nats || destruct_match || rewrite forallb_forall_false in *;
    eauto.
Qed.

Theorem disjoint_false_spec_2 : forall T eq_dec (xs ys: list T),
  (exists k, In k xs /\ In k ys) ->
  disjoint eq_dec xs ys = false.
Proof.
  unfold disjoint; induction xs;
    repeat light || bools || nats || destruct_match || rewrite forallb_forall_false in *;
    eauto.

  - left; eexists; lights; eauto; repeat light || bools || nats || destruct_match.
  - right; eexists; lights; eauto.
    apply forallb_forall_false; lights.
    eexists; lights; eauto.
    repeat bools || nats || light || destruct_match.
Qed.

Theorem disjoint_false_spec: forall T eq_dec (xs ys: list T),
  (exists k, In k xs /\ In k ys) <->
  disjoint eq_dec xs ys = false.
Proof.
  lights; eauto using disjoint_false_spec_1, disjoint_false_spec_2.
Qed.

Ltac t_disjoint :=
  rewrite <- disjoint_false_spec in * ||
  rewrite <- disjoint_true_spec in *.

Ltac clear_in_dec :=
  match goal with
  | H: in_dec _ _ _ = _ |- _ => clear H
  end.

Lemma app_sep {A : Type}: forall (xs1 ys1 xs2 ys2 : list A),
  xs1 ++ ys1 = xs2 ++ ys2 ->
  (exists z zs,
    xs1 ++ z :: zs = xs2 /\
    ys1 = z :: zs ++ ys2) \/
  (xs1 = xs2 /\ ys1 = ys2) \/
  (exists z zs,
    xs1 = xs2 ++ z :: zs /\
    z :: zs ++ ys1 = ys2).
Proof.
  induction xs1; destruct xs2; repeat light || instantiate_any || invert_constructor_equalities;
    eauto with lights.
Qed.

Hint Extern 1 => t_sublist_nil: sublist.
Hint Immediate sublist_right_right: sublist.
Hint Immediate sublist_right_left: sublist.
Hint Immediate sublist_trans: sublist.
Hint Immediate sublist_left: sublist.
Hint Immediate sublist_right: sublist.
Hint Immediate sublist_refl: sublist.

Program Definition head { T } (l: list T) (pre: ~(l = [])) :=
  match l with
  | [] => _
  | x :: _ => x
  end.

Program Definition tail { T } (l: list T) (pre: ~(l = [])) :=
  match l with
  | [] => _
  | _ :: xs => xs
  end.

(* a, a + 1, ..., b - 1 *)
Equations (noind) range (a: nat) (b: nat): list nat by wf (b - a) lt :=
  range a b :=
    if (Compare_dec.ge_dec a b)
    then []
    else a :: range (S a) b.

Next Obligation. lia. Qed.

Opaque range.

Fail Next Obligation. (* no more obligations for range *)

Ltac range_def := rewrite range_equation_1 in *.

Lemma range_spec':
  forall n a b k,
    b - a < n ->
      (In k (range a b) <-> (a <= k /\ k < b)).
Proof.
  induction n;
    repeat light; try lia;
    range_def;
      repeat light || destruct_match ||
        match goal with
        | IHn: forall a b k, _, H: In ?k (range ?a ?b) |- _ =>
          unshelve epose proof (IHn a b k _); clear IHn
        | IHn: forall a b k, _ |- context[In ?k (range ?a ?b)] =>
          unshelve epose proof (IHn a b k _); clear IHn
        end;
    eauto with lia.

  destruct (Nat.eq_dec a k);
    repeat light;
    eauto with lia.
Qed.

Lemma range_spec:
  forall a b k,
    In k (range a b) <-> a <= k /\ k < b.
Proof.
  eauto using range_spec'.
Qed.

Lemma incl_more { A }:
  forall l1 l2: list A, forall x,
      NoDup l1 ->
      ~In x l1 ->
      In x l2 ->
      incl l1 l2 ->
      List.length l1 < List.length l2.
Proof.
  intros.
  unshelve epose proof (@NoDup_incl_length A (x :: l1) l2 _ _);
    repeat light || constructor || apply incl_cons.
Qed.

Lemma incl_nil:
  forall T (l: list T), incl [] l.
Proof.
  unfold incl; lights.
Qed.

Lemma fold_left_move:
  forall A B (f: A -> B -> A) (l: list B) b a,
    fold_left f (l ++ [ b ]) a =
    f (fold_left f l a) b.
Proof.
  induction l;
    repeat light.
Qed.

Lemma fold_left_invariant' { A B }:
  forall (P: A -> list B -> Prop) (f: A -> B -> A) (l'' l' l: list B) a0,
    l = l' ++ l'' ->
    P (fold_left f l' a0) l' ->
    (forall a b l' l'', l = l' ++ b :: l'' -> P a l' -> P (f a b) (l' ++ [ b ])) ->
    P (fold_left f l'' (fold_left f l' a0)) l.
Proof.
  induction l''; repeat light || lists.

  unshelve epose proof (IHl'' (l' ++ [ a ]) _ a0 eq_refl _ _);
    repeat light ||
           rewrite fold_left_move in * ||
           rewrite <- app_assoc in * ||
           unshelve eauto.
Qed.

Lemma fold_left_invariant { A B }:
  forall (P: A -> list B -> Prop) (f: A -> B -> A) (l: list B) a0,
    P a0 [] ->
    (forall a b l' l'', l = l' ++ b :: l'' -> P a l' -> P (f a b) (l' ++ [ b ])) ->
    P (fold_left f l a0) l.
Proof.
  intros.
  eapply (fold_left_invariant' _ _ l [] l);
    eauto.
Qed.

Lemma obvious_in:
  forall A (l1 l2: list A) x,
    In x (l1 ++ x :: l2).
Proof.
  induction l1; repeat light.
Qed.

Lemma not_in_prefix:
  forall A (l1 l2: list A) x,
    NoDup (l1 ++ x :: l2) ->
    In x l1 ->
    False.
Proof.
  induction l1; repeat light || invert_pred NoDup; eauto using obvious_in.
Qed.

Lemma app_comm_cons2:
  forall A (l1 l2: list A) (a: A), l1 ++ a :: l2 = (l1 ++ [ a ]) ++ l2.
Proof.
  repeat light || rewrite <- app_assoc.
Qed.

Ltac map_ext_in :=
  match goal with
  | H: context[map ?f ?l] |- context[map ?g ?l] =>
    rewrite (map_ext_in f g l) in H
  end.

Lemma fold_left_or_else':
  forall X T l x t opt,
    fold_left (fun (acc : option T) (f : X -> option T) => or_else acc (f x)) l opt = Some t ->
    opt = Some t \/ exists f, In f l /\ f x = Some t.
Proof.
  induction l;
    repeat light || instantiate_any || options || destruct_match;
    eauto.
Qed.

Lemma fold_left_or_else:
  forall X T l x t,
    fold_left (fun (acc : option T) (f : X -> option T) => or_else acc (f x)) l None = Some t ->
    exists f, In f l /\ f x = Some t.
Proof.
  intros.
  pose proof (fold_left_or_else' _ _ _ _ _ _ H); lights.
Qed.

Lemma fold_left_not_none:
  forall A B (fs: list (A -> option B)) v x,
    fold_left (fun acc f => or_else acc (f x)) fs (Some v) = None ->
    False.
Proof.
  induction fs; lights.
Qed.

Lemma fold_left_not_none2:
  forall A B (fs: list (A -> option B)) f v x opt,
    In f fs ->
    f x = Some v ->
    fold_left (fun acc f => or_else acc (f x)) fs opt = None ->
    False.
Proof.
  induction fs; repeat light || rewrite_any || options || destruct_match;
    eauto using fold_left_not_none.
Qed.

Lemma fold_is_some:
  forall A B fs (f: A -> option B) opt x,
    is_some (f x) ->
    In f fs ->
    is_some (fold_left (fun acc f => or_else acc (f x)) fs opt).
Proof.
  induction fs; repeat light || options || destruct_match || rewrite_any;
    eauto using fold_left_not_none.

  unshelve epose proof (IHfs f _ x _ _); repeat light || destruct_match.
Qed.

Ltac rewrite_nil :=
  match goal with
  | H: _ = [] |- _ => rewrite H in *
  end.
