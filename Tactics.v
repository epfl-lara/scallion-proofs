Require Import Equations.Equations.

Require Import PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Psatz. (* lia tactic for linear integer arithmetic *)

Hint Extern 1 => exfalso: exfalso.
Hint Extern 1 => lia: lia.
Hint Extern 1 => congruence: congruence.

(** Light tactic which is fast to execute **)

Ltac destruct_pairs :=
  match goal with
  | H: _ * _ |- _ => destruct H
  end.

Ltac destruct_exists :=
  match goal with
  | H: exists x, _ |- _ => let freshX := fresh x in destruct H as [ freshX ]
  end.

Ltac destruct_refinements :=
  match goal with
  | H: { x: _ | _ } |- _ => let freshX := fresh x in destruct H as [ freshX ]
  end.

Ltac destruct_and :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Ltac destruct_or :=
  match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Ltac destruct_unit :=
  match goal with
  | u: unit |- _ => destruct u
  end.

Ltac not_unify t1 t2 := tryif unify t1 t2 then fail else idtac.

Ltac invert_constructor_equalities :=
  match goal with
  | H: ?F _ = ?F _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  | H: ?F _ _ = ?F _ _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  | H: ?F _ _ _ = ?F _ _ _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ = ?F _ _ _ _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ _ = ?F _ _ _ _ _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  | H: ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ |- _ => not_unify existT F; is_constructor F; inversion H; clear H
  end.

Ltac f_equal_constructors :=
  match goal with
  | |- ?F _ = ?F _ => is_constructor F; f_equal
  | |- ?F _ _ = ?F _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ = ?F _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ = ?F _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ = ?F _ _ _ _ _ => is_constructor F; f_equal
  | |- ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ => is_constructor F; f_equal
  end.

Ltac light :=
  (intuition auto) ||
  congruence ||
  subst ||
  (cbn in *) ||
  destruct_exists ||
  destruct_pairs ||
  destruct_refinements
.

Ltac lights := repeat light.
Hint Extern 1 => lights: lights.

(** Some extra tactics used in particular cases **)

Ltac inversion_solve :=
  match goal with
  | H: _ |- _ => solve [ inversion H; lights ]
  end.

Ltac invert_hyp H :=
  (inversion H; [ idtac ]; clear H) ||
  (inversion H; fail).

Ltac invert_pred P :=
  match goal with
  | H: ?F _ |- _ => unify F P; invert_hyp H
  | H: ?F _ _ |- _ => unify F P; invert_hyp H
  | H: ?F _ _ _ |- _ => unify F P; invert_hyp H
  | H: ?F _ _ _ _ |- _ => unify F P; invert_hyp H
  | H: ?F _ _ _ _ _ |- _ => unify F P; invert_hyp H
  | H: ?F _ _ _ _ _ _ |- _ => unify F P; invert_hyp H
  end.

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?t with _ => _ end]] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  end.


(** Tactics on Coq datastructures, need to be enriched **)

Ltac strings := rewrite String.eqb_eq in * || rewrite eqb_neq in *.
Hint Extern 1 => strings: strings.

Ltac nats := rewrite Nat.eqb_eq in * || rewrite Nat.eqb_neq in *.
Hint Extern 1 => nats: nats.

Ltac bools :=
  rewrite Bool.orb_false_iff in * ||
  rewrite Bool.orb_true_iff in * ||
  rewrite Bool.andb_false_iff in * ||
  rewrite Bool.andb_true_iff in * ||
  rewrite Bool.negb_true_iff in * ||
  rewrite Bool.negb_false_iff in *
.

Hint Extern 1 => bools: bools.


(** Tactics used to mark contexts to avoid applying the same tactics twice **)

Ltac isThere P := match goal with
  | H: ?Q |- _ => unify P Q
  end.

Ltac termNotThere p :=
  let P := type of p in
    tryif (isThere P) then fail else idtac.

Ltac poseNew E := termNotThere E; pose proof E.

Inductive Marked {T}: T -> string -> Type :=
| Mark: forall t s, Marked t s
.

Ltac clear_marked :=
  repeat match goal with
         | H: Marked _ _ |- _ => clear H
         end.

Notation "'internal'" := (Marked _ _) (at level 50).



(** Useful shorthands that work on any hypothesis in the the context *)

Ltac apply_any :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac rewrite_any :=
  match goal with
  | H: _ |- _ => rewrite H in *
  end.

Ltac erewrite_any :=
  match goal with
  | H: _ |- _ => erewrite H in *
  end.

Ltac rewrite_back_any :=
  match goal with
  | H: _ |- _ => rewrite <- H in *
  end.

Ltac eapply_any :=
  match goal with
  | H: _ |- _ => eapply H
  end.

Ltac apply_anywhere f :=
  match goal with
  | H: _ |- _ => apply f in H
  end.

Ltac eapply_anywhere f :=
  match goal with
  | H: _ |- _ => eapply f in H
  end.

Ltac rewrite_anywhere f :=
  match goal with
  | H: _ |- _ => rewrite f in H
  end.

Ltac erewrite_anywhere f :=
  match goal with
  | H: _ |- _ => erewrite f in H
  end.

Ltac instantiate_any :=
  match goal with
  | H1: forall x1, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) "instantiation");
    pose proof (H1 _ H2)
  | H1: forall x1 x2, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1, H2) "instantiation");
    pose proof (H1 _ _ H2)
  | H1: forall x1 x2 x3, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) "instantiation");
    pose proof (H1 _ _ _ H2)
  | H1: forall x1 x2 x3 x4, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) "instantiation");
    pose proof (H1 _ _ _ _ H2)
  | H1: forall x1 x2 x3 x4 x5, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) "instantiation");
    pose proof (H1 _ _ _ _ _ H2)
  | H1: forall x1 x2 x3 x4 x5 x6, _ -> _, H2: _ |- _ =>
    poseNew (Mark (H1,H2) "instantiation");
    pose proof (H1 _ _ _ _ _ _ H2)
  end.

Ltac instantiate_forall :=
  match goal with
  | H: forall x, _, x: _ |- _ =>
    poseNew (Mark (H, x) "instantiate_forall");
    pose proof (H x)
  end.

Hint Extern 1 => apply_any: apply_any.
Hint Extern 1 => eapply_any: eapply_any.
Hint Extern 1 => rewrite_any: rewrite_any.
Hint Extern 1 => erewrite_any: erewrite_any.


(** Remove duplicate propositions **)

Ltac removeDuplicateProps :=
  repeat match goal with
  | [ H1: ?P, H2: ?P |- _ ] =>
    match type of P with
    | Prop => idtac
    end;  clear H2
  end.


(** An another way of getting postcondition of function calls **)

Ltac has_proj T :=
  match T with
  | context[proj1_sig] => idtac
  end.

Ltac no_proj T := tryif has_proj T then fail else idtac.

(* We use no_proj to first destruct innermost calls *)
Ltac destruct_proj1_sigs :=
  match goal with
  | |- context[proj1_sig ?T] => no_proj T; destruct T
  | H: context[proj1_sig ?T] |- _ => no_proj T; destruct T
  | |- context[proj1_sig ?T] => destruct T
  | H: context[proj1_sig ?T] |- _ => destruct T
  end.

Ltac is_cons e :=
  match e with
  | _ :: _ => idtac
  end.

Ltac find_false :=
  match goal with
  | H: context[?e] |- _ =>
    let T := type of e in
    unify T False; destruct e
  | |- context[?e] =>
    let T := type of e in
    unify T False; destruct e
  end.

Lemma smaller_greater:
  forall a b, a <= b -> b < a + 1 -> a = b.
Proof.
  intros; lia.
Qed.

Ltac smaller_greater :=
  match goal with
  | H1: ?a <= ?b, H2: ?b < ?a + 1 |- _ =>
    pose proof (smaller_greater a b H1 H2); clear H1; clear H2
  end.
