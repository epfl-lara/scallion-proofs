Require Export Coq.Strings.String.
Require Export Coq.Lists.List.
Export ListNotations.

Require Import Psatz.

Require Import Equations.Equations.

Require Export Parser.FirstFun.
Require Export Parser.NullableFun.
Require Export Parser.AmbiguityConflict.

Inductive Layer: Type -> Type -> Type :=
| LApply { T1 T2 } (f: T1 -> T2) (g: T2 -> list T1): Layer T1 T2
| LPrepend { T1 } T2 (v: T1): Layer T2 (T1 * T2)
| LFollowBy T1 { T2 } (s: Syntax T2): Layer T1 (T1 * T2).

Inductive Layers: Type -> Type -> Type :=
| Empty T: Layers T T
| Cons { T1 T2 T3 } (l: Layer T1 T2) (ls: Layers T2 T3): Layers T1 T3.

Definition empty_layers { T1 T2 } (ls: Layers T1 T2): Prop :=
  match ls with
  | Empty _ => True
  | Cons _ _ => False
  end.

Lemma dec_empty_layers { T1 T2 }:
  forall (ls: Layers T1 T2),
    { empty_layers ls } + { ~ (empty_layers ls) }.
Proof.
  destruct ls; lights.
Qed.

Fixpoint length { T1 T2 } (layers: Layers T1 T2): nat :=
  match layers with
  | Empty _ => 0
  | Cons _ ls => S (length ls)
  end.

Fixpoint count_follow_by { T1 T2 } (layers: Layers T1 T2): nat :=
  match layers with
  | Empty _ => 0
  | Cons (LFollowBy _ _) ls => S (length ls)
  | Cons _ ls => length ls
  end.

Lemma count_follow_by_length:
  forall T1 T2 (ls: Layers T1 T2),
    count_follow_by ls <= length ls.
Proof.
  induction ls; repeat light || destruct_match; eauto with lia.
Qed.

Record Focused_Syntax (A: Type) := mkFocused {
  interface_type: Type;
  core: Syntax interface_type;
  layers: Layers interface_type A;
}.

Arguments interface_type { A }.
Arguments core { A }.
Arguments layers { A }.

Program Definition focus { A } (s: Syntax A): Focused_Syntax A := {|
  core := s;
  layers := Empty A;
|}.

Unset Equations With Funext.

Equations (noind) unfocus_helper { A T } (layers: Layers T A) (core: Syntax T): Syntax A
  by wf (length layers) lt :=

  unfocus_helper (Empty _) core := core;
  unfocus_helper (Cons (LApply f g) ls) core := unfocus_helper ls (Map f g core);
  unfocus_helper (Cons (LPrepend _ v) ls) core := unfocus_helper ls (Sequence (Epsilon v) core);
  unfocus_helper (Cons (LFollowBy _ s) ls) core := unfocus_helper ls (Sequence core s).

Fail Next Obligation. (* no more obligations for unfocus_helper *)

Ltac unfocus_helper_def :=
  rewrite unfocus_helper_equation_1 in * ||
  rewrite unfocus_helper_equation_2 in * ||
  rewrite unfocus_helper_equation_3 in * ||
  rewrite unfocus_helper_equation_4 in *.

Opaque unfocus_helper.

Program Definition unfocus { A } (fs: Focused_Syntax A): Syntax A := unfocus_helper (layers fs) (core fs).

Fail Next Obligation. (* no more obligations for unfocus *)

Theorem unfocus_focus:
  forall A (s: Syntax A), unfocus (focus s) = s.
Proof.
  unfold unfocus, focus; repeat light || unfocus_helper_def.
Qed.

Fixpoint have_conflict_ind { T1 T2 } (layers: Layers T1 T2): Prop :=
  match layers with
  | Empty _ => False
  | Cons (LFollowBy _ s) ls => has_conflict_ind s \/ have_conflict_ind ls
  | Cons _ ls => have_conflict_ind ls
  end.

Ltac destruct_layer :=
  match goal with
  | l: Layer _ _ |-  _ => destruct l
  end.

Lemma matches_unfocus_helper_sub:
  forall A T (ls: Layers T A) (core1 core2: Syntax T) ts v,
    matches (unfocus_helper ls core1) ts v ->
    (forall ts' v', matches core1 ts' v' -> matches core2 ts' v') ->
    matches (unfocus_helper ls core2) ts v.
Proof.
  induction ls;
    repeat light || destruct_layer || unfocus_helper_def || invert_matches || eapply_any || invert_constructor_equalities;
    eauto with matches.
Qed.

Lemma matches_unfocus_sub:
  forall A T (core1 core2: Syntax T) (ls: Layers T A) ts v,
    matches (unfocus {| core := core1; layers := ls |}) ts v ->
    (forall ts' v', matches core1 ts' v' -> matches core2 ts' v') ->
    matches (unfocus {| core := core2; layers := ls |}) ts v.
Proof.
  unfold unfocus; eauto using matches_unfocus_helper_sub.
Qed.

Lemma matches_unfocus_helper_nil:
  forall A T (ls: Layers T A) (s: Syntax T) v,
    matches (unfocus_helper ls s) [] v ->
    exists v', matches s [] v'.
Proof.
  induction ls;
    repeat light || destruct_layer || unfocus_helper_def || instantiate_any || invert_matches || lists;
    eauto.
Qed.

Ltac matches_unfocus_helper_nil :=
  match goal with
  | H: matches (unfocus_helper _ _) [] _ |- _ =>
    poseNew (Mark H "matches_unfocus_helper_nil");
    pose proof (matches_unfocus_helper_nil _ _ _ _ _ H)
  end.

Lemma matches_unfocus_nil:
  forall A (fs: Focused_Syntax A) v,
    matches (unfocus fs) [] v ->
    exists v', matches (core fs) [] v'.
Proof.
  unfold unfocus; eauto using matches_unfocus_helper_nil.
Qed.

Lemma unfocus_conflict_remains:
  forall A T (ls: Layers T A) (s: Syntax T),
    has_conflict_ind s ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  induction ls;
    repeat light || unfocus_helper_def || destruct_layer || apply_any;
    eauto using has_conflict_map;
    eauto using has_conflict_seq_l;
    eauto using has_conflict_seq_r.
Qed.

Lemma unfocus_conflict_remains2:
  forall A T (ls: Layers T A) (s: Syntax T),
    have_conflict_ind ls ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  induction ls; try destruct_layer; lights; try unfocus_helper_def;
    eauto using has_conflict_map;
    eauto using has_conflict_seq_l;
    eauto using unfocus_conflict_remains, has_conflict_seq_r.
Qed.

Lemma unfocus_conflict_more:
  forall A T (ls: Layers T A) (s1 s2: Syntax T),
    has_conflict_ind (unfocus_helper ls s1) ->
    (has_conflict_ind s1 -> has_conflict_ind s2) ->
    (forall ts v, matches s1 ts v -> exists ts' v', matches s2 ts' v') ->
    (forall k, In k (should_not_follow_fun s1) -> In k (should_not_follow_fun s2)) ->
    has_conflict_ind (unfocus_helper ls s2).
Proof.
  induction ls;
    repeat light || unfocus_helper_def || destruct_layer ||
           (poseNew (Mark 0 "IHls"); eapply IHls);
    eauto with has_conflict_ind;
    eauto with should_not_follow_fun;
    eauto using has_conflict_seq_monotone_l;

    repeat match goal with
    | H1: forall ts v, matches ?s ts v -> _, H2: matches ?s ?ts ?v |- _ =>
      pose proof (H1 _ _ H2); clear H1
    | _ => light || invert_matches || lists || invert_constructor_equalities
    end;
    eauto with matches;
    eauto using should_not_follow_fun_seq_monotone_l.
Qed.

Ltac unfocus_conflict_more :=
  eapply unfocus_conflict_more; eauto;
    repeat light || invert_matches || invert_constructor_equalities || options ||
           destruct_match || clear_some_dec;
    eauto with matches;
    eauto with has_conflict_ind;
    eauto with should_not_follow_fun.

Hint Extern 1 => unfocus_conflict_more: unfocus_conflict_more.

Lemma unfocus_conflict_disj_l:
  forall A T (ls: Layers T A) (s1 s2: Syntax T),
    has_conflict_ind (unfocus_helper ls s1) ->
    has_conflict_ind (unfocus_helper ls (Disjunction s1 s2)).
Proof.
  intros; unfocus_conflict_more.
Qed.

Lemma unfocus_conflict_disj_r:
  forall A T (ls: Layers T A) (s1 s2: Syntax T),
    has_conflict_ind (unfocus_helper ls s2) ->
    has_conflict_ind (unfocus_helper ls (Disjunction s1 s2)).
Proof.
  intros; unfocus_conflict_more.
Qed.

Lemma unfocus_conflict_eps_seq:
  forall A T1 T2 (ls: Layers (T1 * T2) A) (s1: Syntax T1) (a: T1) (s2: Syntax T2),
    has_conflict_ind (unfocus_helper ls (Sequence (Epsilon a) s2)) ->
    matches s1 [] a ->
    has_conflict_ind (unfocus_helper ls (Sequence s1 s2)).
Proof.
  intros; unfocus_conflict_more.
Qed.

Lemma unfocus_conflict_var:
  forall A x (ls: Layers (get_type x) A),
    has_conflict_ind (unfocus_helper ls (e x)) ->
    has_conflict_ind (unfocus_helper ls (Var x)).
Proof.
  intros; unfocus_conflict_more.
Qed.

Lemma matches_unfocus_helper_prefix:
  forall A T (ls: Layers T A) (core: Syntax T) ts v,
    matches (unfocus_helper ls core) ts v ->
    exists ts' ts'' v',
      ts = ts' ++ ts'' /\
      matches core ts' v'.
Proof.
  induction ls;
    repeat light || destruct_layer || unfocus_helper_def || invert_constructor_equalities ||
           (poseNew (Mark 0 "IHls");  apply_anywhere IHls) || invert_matches;
    eauto with datatypes.
Qed.

Ltac matches_unfocus_helper_prefix :=
  match goal with
  | H: matches (unfocus_helper _ _) _ _ |- _ =>
    poseNew (Mark 0 "matches_unfocus_helper_prefix");
    pose proof (matches_unfocus_helper_prefix _ _ _ _ _ _ H)
  end.

Lemma matches_unfocus_helper_sub_first:
  forall A T (ls: Layers T A) (core1 core2: Syntax T) t ts v,
    matches (unfocus_helper ls core1) (t :: ts) v ->
    In (class t) (first_fun core1) ->
    ~ has_conflict_ind (unfocus_helper ls core1) ->
    (forall ts' v', matches core1 (t :: ts') v' -> matches core2 (t :: ts') v') ->
    matches (unfocus_helper ls core2) (t :: ts) v.
Proof.
  induction ls; intros; try destruct_layer; try solve [
    repeat light || destruct_layer || unfocus_helper_def || invert_matches ||
           eapply_any || invert_constructor_equalities || app_cons_destruct || lists;
    eauto with matches;
    eauto with first_fun
    ].

  repeat light || destruct_layer || unfocus_helper_def || invert_matches ||
         apply_anywhere first_fun_sound ||
         eapply_any || invert_constructor_equalities || app_cons_destruct || lists;
    eauto with matches;
    eauto with first_fun;
    eauto using unfocus_conflict_remains, has_conflict_seq_follow2 with exfalso.

  - apply_anywhere matches_unfocus_helper_prefix;
      repeat light || invert_matches || invert_constructor_equalities.
    eapply first_fun_seq_l;
      repeat light || rewrite <- H4;
      eauto using first_fun_complete.
Qed.

Lemma matches_unfocus_helper_sub_first2:
  forall A T (ls: Layers T A) (core1 core2: Syntax T) t ts v,
    matches (unfocus_helper ls core1) (t :: ts) v ->
    ~ has_conflict_ind (unfocus_helper ls core1) ->
    (forall v', matches core1 [] v' -> matches core2 [] v') ->
    (forall ts' v', matches core1 (t :: ts') v' -> matches core2 (t :: ts') v') ->
    matches (unfocus_helper ls core2) (t :: ts) v.
Proof.
  induction ls; intros; try destruct_layer;
    repeat light || destruct_layer || unfocus_helper_def || invert_matches ||
           eapply_any || invert_constructor_equalities || app_cons_destruct || lists;
    eauto with matches;
    eauto with first_fun.
Qed.

Lemma matches_unfocus_prepend:
  forall A T (ls: Layers T A) (s1 s2: Syntax T) ts ts' v,
    matches (unfocus_helper ls s1) ts v ->
    (forall ts v, matches s1 ts v -> matches s2 (ts' ++ ts) v) ->
    matches (unfocus_helper ls s2) (ts' ++ ts) v.
Proof.
  induction ls;
    repeat light || unfocus_helper_def || destruct_layer || eapply_any || invert_matches ||
           invert_constructor_equalities;
    eauto with matches.
Qed.

Lemma matches_unfocus_prepend_one:
  forall A (ls: Layers token A) t ts v,
    matches (unfocus_helper ls (Epsilon t)) ts v ->
    matches (unfocus_helper ls (Elem (class t))) (t :: ts) v.
Proof.
  intros.
  change (matches (unfocus_helper ls (Elem (class t))) ([ t ] ++ ts) v).
  eapply matches_unfocus_prepend;
    eauto; repeat light || invert_matches || lists;
      eauto with matches.
Qed.

Lemma matches_unfocus_drop:
  forall A T (ls: Layers T A) (s1 s2: Syntax T) t ts v,
    matches (unfocus_helper ls s1) (t :: ts) v ->
    In (class t) (first_fun s1) ->
    ~ has_conflict_ind (unfocus_helper ls s1) ->
    (forall ts v, matches s1 (t :: ts) v -> matches s2 ts v) ->
    matches (unfocus_helper ls s2) ts v.
Proof.
  induction ls;
    repeat light || unfocus_helper_def || destruct_layer || eapply_any || invert_matches ||
           invert_constructor_equalities || app_cons_destruct ||
           matches_unfocus_helper_prefix || rewrite <- app_assoc in *;
    eauto with matches;
    eauto with first_fun;
    eauto with has_conflict_ind;
    try solve [
      repeat light || apply_anywhere first_fun_sound;
        eauto using unfocus_conflict_remains with has_conflict_ind exfalso
    ].
Qed.

Lemma matches_unfocus_inj:
  forall A T (ls: Layers T A) (s1 s2: Syntax T) v v1' v2',
    matches (unfocus_helper ls s1) [] v1' ->
    matches (unfocus_helper ls s2) [] v2' ->
    ~ has_conflict_ind (unfocus_helper ls s1) ->
    ~ has_conflict_ind (unfocus_helper ls s2) ->
    matches s1 [] v ->
    matches s2 [] v ->
    v1' = v2'.
Proof.
  induction ls;
    repeat light || unfocus_helper_def || destruct_layer ||
           matches_unfocus_helper_nil || invert_matches || lists ||
           invert_constructor_equalities || matches_nil_unicity2;
      eauto using unfocus_conflict_remains with has_conflict_ind;
      eauto using unfocus_conflict_remains with matches.
Qed.

Lemma matches_unfocus_propagate:
  forall A T (ls: Layers T A) (s1 s2: Syntax T) v v',
    matches (unfocus_helper ls s1) [] v' ->
    ~ has_conflict_ind (unfocus_helper ls s1) ->
    ~ has_conflict_ind (unfocus_helper ls s2) ->
    matches s1 [] v ->
    matches s2 [] v ->
    matches (unfocus_helper ls s2) [] v'.
Proof.
  induction ls;
    repeat light || unfocus_helper_def || matches_nil_unicity || destruct_layer;
    eauto using unfocus_conflict_remains with has_conflict_ind matches.

  repeat light || matches_unfocus_helper_nil || invert_matches || lists ||
         invert_constructor_equalities || matches_nil_unicity2;
      eauto with matches;
      eauto using unfocus_conflict_remains with has_conflict_ind.
Qed.

Lemma matches_unfocus_propagate_first:
  forall A T (ls: Layers T A) (s1 s2: Syntax T) t ts v v',
    matches (unfocus_helper ls s1) (t :: ts) v' ->
    ~ In (class t) (first_fun s1) ->
    ~ has_conflict_ind (unfocus_helper ls s1) ->
    ~ has_conflict_ind (unfocus_helper ls s2) ->
    matches s1 [] v ->
    matches s2 [] v ->
    matches (unfocus_helper ls s2) (t :: ts) v'.
Proof.
  intros.
  eapply matches_unfocus_helper_sub_first2;
    eauto; repeat light || matches_nil_unicity2;
      eauto using unfocus_conflict_remains with has_conflict_ind;
      eauto using first_fun_complete with exfalso.
Qed.
