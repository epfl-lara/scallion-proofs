Require Import Coq.Program.Equality.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.Tactics.
Require Export Parser.HList.
Require Export Parser.Option.
Require Export Parser.Description.

(* Given an `Description`, we build the corresponding inductive predicate *)
Inductive descr_ind { G } (descr: Description G): forall A, Syntax A -> G A -> Prop :=
| EpsInd: forall A a R v,
    In R (epsilon_descr descr a) ->
    R HNil = Some v ->
    descr_ind descr A (Epsilon a) v

| FailureInd: forall A R v,
    In R (failure_descr descr A) ->
    R HNil = Some v ->
    descr_ind descr A (Failure A) v

| ElemInd: forall k R v,
    In R (token_descr descr k) ->
    R HNil = Some v ->
    descr_ind descr token (Elem k) v

| MapInd0: forall A B (f: A -> B) g s R vB,
    In R (map_descr descr f g s) ->
    R (HCons None HNil) = Some vB ->
    descr_ind descr B (Map f g s) vB

| MapInd1: forall A B (f: A -> B) g s R vA vB,
    descr_ind descr A s vA ->
    In R (map_descr descr f g s) ->
    R (HCons (Some vA) HNil) = Some vB ->
    descr_ind descr B (Map f g s) vB

| DisjInd0: forall A s1 s2 R v,
    In R (disj_descr descr s1 s2) ->
    R (HCons None (HCons None HNil)) = Some v ->
    descr_ind descr A (Disjunction s1 s2) v

| DisjInd1: forall A s1 s2 R v1 v,
    descr_ind descr A s1 v1 ->
    In R (disj_descr descr s1 s2) ->
    R (HCons (Some v1) (HCons None HNil)) = Some v ->
    descr_ind descr A (Disjunction s1 s2) v

| DisjInd2: forall A s1 s2 R v2 v,
    descr_ind descr A s2 v2 ->
    In R (disj_descr descr s1 s2) ->
    R (HCons None (HCons (Some v2) HNil)) = Some v ->
    descr_ind descr A (Disjunction s1 s2) v

| DisjInd12: forall A s1 s2 R v1 v2 v,
    descr_ind descr A s1 v1 ->
    descr_ind descr A s2 v2 ->
    In R (disj_descr descr s1 s2) ->
    R (HCons (Some v1) (HCons (Some v2) HNil)) = Some v ->
    descr_ind descr A (Disjunction s1 s2) v

| SeqInd0: forall A B s1 s2 R v,
    In R (seq_descr descr s1 s2) ->
    R (HCons None (HCons None HNil)) = Some v ->
    descr_ind descr (A * B) (Sequence s1 s2) v

| SeqInd1: forall A B s1 s2 R v1 v,
    descr_ind descr A s1 v1 ->
    In R (seq_descr descr s1 s2) ->
    R (HCons (Some v1) (HCons None HNil)) = Some v ->
    descr_ind descr (A * B) (Sequence s1 s2) v

| SeqInd2: forall A B s1 s2 R v2 v,
    descr_ind descr B s2 v2 ->
    In R (seq_descr descr s1 s2) ->
    R (HCons None (HCons (Some v2) HNil)) = Some v ->
    descr_ind descr (A * B) (Sequence s1 s2) v

| SeqInd12: forall A B s1 s2 R v1 v2 v,
    descr_ind descr A s1 v1 ->
    descr_ind descr B s2 v2 ->
    In R (seq_descr descr s1 s2) ->
    R (HCons (Some v1) (HCons (Some v2) HNil)) = Some v ->
    descr_ind descr (A * B) (Sequence s1 s2) v

| VarInd0: forall x R v',
    In R (var_descr descr x (e x)) ->
    R (HCons None HNil) = Some v' ->
    descr_ind descr (get_type x) (Var x) v'

| VarInd1: forall x R v v',
    descr_ind descr (get_type x) (e x) v ->
    In R (var_descr descr x (e x)) ->
    R (HCons (Some v) HNil) = Some v' ->
    descr_ind descr (get_type x) (Var x) v'
.

Arguments descr_ind { G } descr { A }.

Hint Constructors descr_ind: descr_ind.

Lemma descr_same:
  forall F (descr: Description F) A (s: Syntax A) v1 v2,
    descr_ind descr s v1 ->
    v1 = v2 ->
    descr_ind descr s v2.
Proof.
  intros; subst; auto.
Qed.

Program Definition descr_ind_epsilon_inversion G (descr: Description G) A (a: A) v
  (H: descr_ind descr (Epsilon a) v) :=
  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Epsilon a => fun v'' =>
      exists R,
        In R (epsilon_descr descr a) /\
        R HNil = Some v''
    | _ => fun _ => True
   end v'
  with
  | ElemInd _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligation for `descr_ind_epsilon_inversion` *)

Program Definition descr_ind_elem_inversion G (descr: Description G) k (v: G token)
  (H: descr_ind descr (Elem k) v) :=
  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Elem k => fun v'' =>
      exists R,
        In R (token_descr descr k) /\
        R HNil = Some v''
    | _ => fun _ => True
   end v'
  with
  | ElemInd _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligation for `descr_ind_elem_inversion` *)

Program Definition descr_ind_failure_inversion G (descr: Description G) A v
  (H: descr_ind descr (Failure A) v) :=
  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Failure A => fun v'' =>
      exists R,
        In R (failure_descr descr A) /\
        R HNil = Some v''
    | _ => fun _ => True
   end v'
  with
  | ElemInd _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligation for `descr_ind_failure_inversion` *)

Program Definition descr_ind_disj_inversion G (descr: Description G) A (s: Syntax A) (v: G A)
  (H: descr_ind descr s v) :=

  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Disjunction s1' s2' =>
      fun v'' =>
      exists R, In R (disj_descr descr s1' s2') /\ (
          (R (HCons None (HCons None HNil)) = Some v'') \/
          (exists v1, descr_ind descr s1' v1 /\ R (HCons (Some v1) (HCons None HNil)) = Some v'') \/
          (exists v2, descr_ind descr s2' v2 /\ R (HCons None (HCons (Some v2) HNil)) = Some v'') \/
          (exists v1 v2,
              descr_ind descr s1' v1 /\
              descr_ind descr s2' v2 /\
              R (HCons (Some v1) (HCons (Some v2) HNil)) = Some v''
          )
        )
    | _ => fun _ => True
    end v'
  with
  | SeqInd0 _ _ _ _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligation for `descr_ind_disj_inversion` *)

Program Definition descr_ind_seq_inversion G (descr: Description G) A (s: Syntax A) (v: G A)
  (H: descr_ind descr s v) :=

  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Sequence s1' s2' =>
      fun v'' =>
      exists R, In R (seq_descr descr s1' s2') /\ (
        (R (HCons None (HCons None HNil)) = Some v'') \/
        (exists v1, descr_ind descr s1' v1 /\ R (HCons (Some v1) (HCons None HNil)) = Some v'') \/
        (exists v2, descr_ind descr s2' v2 /\ R (HCons None (HCons (Some v2) HNil)) = Some v'') \/
        (exists v1 v2,
            descr_ind descr s1' v1 /\
            descr_ind descr s2' v2 /\
            R (HCons (Some v1) (HCons (Some v2) HNil)) = Some v''
        )
      )
    | _ => fun _ => True
    end v'
  with
  | SeqInd0 _ _ _ _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligations for `descr_ind_seq_inversion` *)

Program Definition descr_ind_map_inversion G (descr: Description G) A (s: Syntax A) (v: G A)
  (H: descr_ind descr s v) :=

  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Map f g s' =>
      fun v'' =>
        exists R, In R (map_descr descr f g s') /\ (
          (R (HCons None HNil) = Some v'') \/
          (exists v', descr_ind descr s' v' /\ R (HCons (Some v') HNil) = Some v'')
        )
    | _ => fun _ => True
    end v'
  with
  | SeqInd0 _ _ _ _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligations for `descr_ind_seq_inversion` *)

Program Definition descr_ind_var_inversion G (descr: Description G) x v
  (H: descr_ind descr (Var x) v) :=
  match H in descr_ind _ s' v' return
    match s' in Syntax A' return G A' -> Prop with
    | Var x' => fun v'' =>
      exists R, In R (var_descr descr x' (e x')) /\ (
        (R (HCons None HNil) = Some v'') \/
        (exists v', descr_ind descr (e x') v' /\ R (HCons (Some v') HNil) = Some v'')
      )
    | _ => fun _ => True
   end v'
  with
  | VarInd0 _ _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 10.

Fail Next Obligation. (* no more obligations for `descr_ind_var_inversion` *)

Ltac descr_ind_inversion :=
  match goal with
  | H: descr_ind _ (Epsilon _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_epsilon_inversion _ _ _ _ _ H)

  | H: descr_ind _ (Elem _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_elem_inversion _ _ _ _ H)

  | H: descr_ind _ (Failure _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_failure_inversion _ _ _ _ H)

  | H: descr_ind _ (Sequence _ _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_seq_inversion _ _ _ _ _ H)

  | H: descr_ind _ (Disjunction _ _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_disj_inversion _ _ _ _ _ H)

  | H: descr_ind _ (Map _ _ _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_map_inversion _ _ _ _ _ H)

  | H: descr_ind _ (Var _) _ |- _ =>
      poseNew (Mark H "descr_ind_inversion");
      pose proof (descr_ind_var_inversion _ _ _ _ H)
  end.

Lemma in_disj_descr:
  forall A (s1 s2: Syntax A) G (descr: Description G) v r opt1 opt2,
    In r (disj_descr descr s1 s2) ->
    opt_forall opt1 (descr_ind descr s1) ->
    opt_forall opt2 (descr_ind descr s2) ->
    r (HCons opt1 (HCons opt2 HNil)) = Some v ->
    descr_ind descr (Disjunction s1 s2) v.
Proof.
  destruct opt1; destruct opt2;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_seq_descr:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) G (descr: Description G) v r opt1 opt2,
    In r (seq_descr descr s1 s2) ->
    opt_forall opt1 (descr_ind descr s1) ->
    opt_forall opt2 (descr_ind descr s2) ->
    r (HCons opt1 (HCons opt2 HNil)) = Some v ->
    descr_ind descr (Sequence s1 s2) v.
Proof.
  destruct opt1; destruct opt2;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_map_descr:
  forall A B (f: A -> B) g (s': Syntax A) G (descr: Description G) v r opt,
    In r (map_descr descr f g s') ->
    opt_forall opt (descr_ind descr s') ->
    r (HCons opt HNil) = Some v ->
    descr_ind descr (Map f g s') v.
Proof.
  destruct opt;
    repeat light;
    eauto with descr_ind.
Qed.

Lemma in_var_descr:
  forall x G (descr: Description G) v r opt,
    In r (var_descr descr x (e x)) ->
    opt_forall opt (descr_ind descr (e x)) ->
    r (HCons opt HNil) = Some v ->
    descr_ind descr (Var x) v.
Proof.
  destruct opt;
    repeat light;
    eauto with descr_ind.
Qed.
