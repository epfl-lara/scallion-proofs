Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.Structures.
Require Export Parser.ProductiveFun.
Require Export Parser.ProductiveInd.
Require Export Parser.NullableFun.
Require Export Parser.HasConflictInd.
Require Export Parser.ShouldNotFollowFun.
Require Export Parser.SubSyntax.
Require Export Parser.Prefix.

Opaque nullable_fun.
Opaque productive_fun.
Opaque should_not_follow_fun.
Opaque first_fun.

Inductive visitable (x: id): forall A, Syntax A -> Prop :=
| VDisjL:
    forall A (s1 s2: Syntax A),
      visitable x A s1 ->
      visitable x A (Disjunction s1 s2)
| VDisjR:
    forall A (s1 s2: Syntax A),
      visitable x A s2 ->
      visitable x A (Disjunction s1 s2)
| VSeqL:
    forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) ts v,
      visitable x A1 s1 ->
      matches s2 ts v ->
      visitable x (A1 * A2) (Sequence s1 s2)
| VSeqR:
    forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) v,
      matches s1 [] v ->
      visitable x A2 s2 ->
      visitable x (A1 * A2) (Sequence s1 s2)
| VMap:
    forall A B (f: A -> B) g (s: Syntax A),
      visitable x A s ->
      visitable x B (Map f g s)
| VVar:
    visitable x (get_type x) (Var x)
| VRec:
    forall y,
      visitable x (get_type y) (e y) ->
      visitable x (get_type y) (Var y)
.

Arguments visitable x { A }.

Hint Constructors visitable: visitable.

Program Definition visitable_inversion { A } x (s: Syntax A) (H: visitable x s) :=
  match H in visitable _ s' return
    match s' return Prop with
    | Disjunction s1' s2' => visitable x s1' \/ visitable x s2'
    | Sequence s1' s2' =>
      (visitable x s1' /\ exists ts v, matches s2' ts v) \/
      (exists v, matches s1' [] v /\ visitable x s2')
    | Map f g s' => visitable x s'
    | Var y => x = y \/ visitable x (e y)
    | _ => True
    end
  with
  | VDisjL _ _ _ _ _ => _
  | _ => _
  end.

Solve Obligations with eauto 6.

Fail Next Obligation. (* no more obligations visitable_inversion *)

Ltac visitable_inversion :=
  match goal with
  | H: visitable _ (Disjunction _ _) |- _ =>
    poseNew (Mark H "visitable_inversion");
    pose proof (visitable_inversion _ _ H)
  | H: visitable _ (Sequence _ _) |- _ =>
    poseNew (Mark H "visitable_inversion");
    pose proof (visitable_inversion _ _ H)
  | H: visitable _ (Map _ _ _) |- _ =>
    poseNew (Mark H "visitable_inversion");
    pose proof (visitable_inversion _ _ H)
  | H: visitable _ (Var _) |- _ =>
    poseNew (Mark H "visitable_inversion");
    pose proof (visitable_inversion _ _ H)
  end.

Lemma visitable_extend:
  forall A (s: Syntax A) x ts v,
    visitable x s ->
    matches (e x) ts v ->
    exists ts' v, matches s (ts ++ ts') v.
Proof.
  intros.
  revert v ts H0.
  induction H;
    repeat light || instantiate_any ||
      options || destruct_match;
    eauto 6 with matches.
Qed.

Ltac visitable_extend :=
  match goal with
  | H1: visitable ?x ?s,
    H2: matches (e ?x) _ _ |- _ =>
    poseNew (Mark s "visitable_extend");
    pose proof (visitable_extend _ _ _ _ _ H1 H2)
  end.

Lemma visitable_non_empty_conflict':
  forall x A (s: Syntax A),
    visitable x s ->
    forall t ts v tsx vx,
      matches_without [ x ] s (t :: ts) v ->
      matches (e x) (t :: tsx) vx ->
      has_conflict_ind s.
Proof.
  induction 1;
    repeat light || visitable_inversion || inversion_solve || invert_constructor_equalities ||
           visitable_extend || invert_matches || app_cons_destruct;
    eauto with has_conflict_ind.

  - eapply has_conflict_disj_first;
      repeat light || options || eapply first_fun_complete || destruct_match;
      eauto using matches_incl, incl_nil.

  - eapply has_conflict_disj_first;
      repeat light || options || eapply first_fun_complete || destruct_match;
      eauto using matches_incl, incl_nil.

  - eapply has_conflict_seq_follow;
      repeat light || eapply first_fun_complete;
      eauto using should_not_follow_fun_first, matches_incl, incl_nil.

  - repeat light || invert_constructor_equalities || rewrite <- app_assoc in * ||
           options || nullable_fun_spec || destruct_match;
     eauto using
       should_not_follow_fun_first,
       first_fun_complete,
       has_conflict_seq_follow,
       matches_incl, incl_nil.
Qed.

Lemma visitable_prefix_conflict:
  forall x A (s: Syntax A) t ts v,
    visitable x s ->
    prefix s (e x) ->
    matches_without [ x ] s (t :: ts) v ->
    has_conflict_ind s.
Proof.
  intros.
  repeat prefix || light;
    eauto using visitable_non_empty_conflict';
    eauto using matches_incl, incl_nil.
Qed.

Lemma visitable_not_nullable_conflict':
  forall x A (s: Syntax A),
    visitable x s ->
    forall t ts v1 v2,
      prefix s (e x) ->
      matches s (t :: ts) v1 ->
      (forall v, ~ matches s [] v) ->
      matches (e x) [] v2 ->
      has_conflict_ind s.
Proof.
  induction 1;
    repeat light || invert_matches || prefix_sub || nullable_fun_spec || options || destruct_match ||
           visitable_extend || prefix || app_cons_destruct || invert_constructor_equalities;
    eauto with has_conflict_ind matches.

  - pose proof (visitable_extend _ _ _ _ _ H H7); lights.
    apply has_conflict_disj_first with (get_kind t);
    repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
      eauto.

  - pose proof (visitable_extend _ _ _ _ _ H H8); lights.
    apply has_conflict_disj_first with (get_kind t);
    repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
      eauto.

  - pose proof (visitable_extend _ _ _ _ _ H H13); lights.
    apply has_conflict_seq_follow with (get_kind t);
      repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
      eauto.

  - destruct xs2 eqn:XS2; lights;
      eauto with has_conflict_ind matches.
    destruct ts' eqn:TSP; repeat light || prefix_sub || prefix.
    + pose proof (visitable_extend _ _ _ _ _ H H5); lights.
      apply has_conflict_seq_follow with (get_kind t);
        repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
        eauto.
    + destruct (nullable_fun s1) eqn:N1;
        repeat light || nullable_fun_spec || prefix_sub || prefix.
      * pose proof (visitable_extend _ _ _ _ _ H H5); lights.
        apply has_conflict_seq_follow with (get_kind t);
          repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
          eauto.
      * apply has_conflict_seq_l.
        eapply_any;
          repeat light || nullable_fun_spec; eauto.

  - destruct (nullable_fun s1) eqn:N1;
      repeat light || nullable_fun_spec || prefix_sub || prefix.
    destruct (nullable_fun s2) eqn:N2;
      repeat light || nullable_fun_spec || prefix_sub || prefix;
      eauto with matches exfalso.
    destruct ts'; repeat light || nullable_fun_spec.
    apply has_conflict_seq_r.
    eapply_any;
      repeat light || nullable_fun_spec; eauto.

  - eauto with matches exfalso.
  - apply has_conflict_var.
    eapply_any; lights;
      eauto using prefix_var with matches.
Qed.

Lemma visitable_not_nullable_conflict:
  forall x A (s: Syntax A) v,
    visitable x s ->
    prefix s (e x) ->
    (forall v, ~ matches s [] v) ->
    matches (e x) [] v ->
    has_conflict_ind s.
Proof.
  repeat light || visitable_extend.
  destruct ts';
    repeat light; eauto using visitable_not_nullable_conflict' with exfalso.
Qed.

Lemma visitable_not_first_conflict':
  forall x A (s: Syntax A),
    visitable x s ->
    forall k ts v,
      prefix s (e x) ->
      matches s ts v ->
      ~ In k (first_fun s) ->
      In k (first_fun (e x)) ->
      has_conflict_ind s.
Proof.
  induction 1;
    repeat light || invert_matches || prefix_sub || options || destruct_match || nullable_fun_spec ||
           visitable_extend || prefix || app_cons_destruct || invert_constructor_equalities;
    eauto with has_conflict_ind matches first_fun exfalso;
    eauto 6 with has_conflict_ind prefix first_fun.
Qed.

Lemma visitable_not_first_conflict:
  forall x A (s: Syntax A),
    visitable x s ->
    forall t ts v,
      prefix s (e x) ->
      ~ In (get_kind t) (first_fun s) ->
      matches (e x) (t :: ts) v ->
      has_conflict_ind s.
Proof.
  repeat light || visitable_extend;
    eauto using first_fun_complete, visitable_not_first_conflict'.
Qed.

Lemma subsyntax_prefix:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2),
    subsyntax s1 s2 ->
    prefix s1 s2.
Proof.
  unfold subsyntax, prefix, accepts;
    repeat light || exists [] || lists; eauto.
Qed.

Lemma subsyntax_prefix_seq_l:
  forall A1 A2 A (s1: Syntax A1) (s2: Syntax A2) (s: Syntax A) ts v,
    subsyntax (Sequence s1 s2) s ->
    matches s2 ts v ->
    prefix s1 s.
Proof.
  unfold subsyntax, accepts, prefix; lights;
    eauto with matches.
Qed.

Lemma visitable_subsyntax_conflict:
  forall x A (s: Syntax A),
    visitable x s ->
    forall ts v,
      matches_without [ x ] s ts v ->
      subsyntax s (e x) ->
      has_conflict_ind s.
Proof.
  induction 1;
    repeat light || invert_matches || inversion_solve || nullable_fun_spec ||
           prefix_sub || invert_constructor_equalities;
    eauto with has_conflict_ind subsyntax.

  - destruct ts; lights.
    + decide_nullable_one s1;
        repeat light || nullable_fun_spec.
      * eapply has_conflict_disj_nullable;
          repeat light || options || destruct_match || nullable_fun_spec;
          eauto using matches_incl, incl_nil.
      * apply has_conflict_disj_l.
        unshelve epose proof (H1 [] _);
          unfold accepts in *; eauto using matches_incl, incl_nil with matches;
            lights.
        apply visitable_not_nullable_conflict with x v0;
          repeat light; eauto using subsyntax_prefix with subsyntax.
    + destruct (in_dec kind_eq_dec (get_kind t) (first_fun s1)).
      * eapply has_conflict_disj_first;
          repeat light || apply_anywhere first_fun_sound || rewrite first_fun_spec ||
                 invert_constructor_equalities;
          eauto 6 using matches_incl, incl_nil with lights.
      * apply has_conflict_disj_l.
        unshelve epose proof (H1 (t :: ts) _);
          unfold accepts in *; eauto using matches_incl, incl_nil with matches;
            lights.
        eapply visitable_not_first_conflict;
          eauto using subsyntax_prefix with subsyntax.

  - destruct ts; lights.
    + decide_nullable_one s2;
        repeat light || nullable_fun_spec.
      * eapply has_conflict_disj_nullable;
          repeat light || options || destruct_match || nullable_fun_spec;
          eauto using matches_incl, incl_nil.
      * apply has_conflict_disj_r.
        unshelve epose proof (H1 [] _);
          unfold accepts in *; eauto using matches_incl, incl_nil with matches;
            lights.
        apply visitable_not_nullable_conflict with x v0;
          repeat light; eauto using subsyntax_prefix with subsyntax.
    + destruct (in_dec kind_eq_dec (get_kind t) (first_fun s2)).
      * eapply has_conflict_disj_first;
          repeat light || apply_anywhere first_fun_sound || rewrite first_fun_spec ||
                 invert_constructor_equalities;
          eauto 6 using matches_incl, incl_nil with lights.
      * apply has_conflict_disj_r.
        unshelve epose proof (H1 (t :: ts) _);
          unfold accepts in *; eauto using matches_incl, incl_nil with matches;
            lights.
        eapply visitable_not_first_conflict;
          eauto using subsyntax_prefix with subsyntax.

  - decide_nullable_one s2;
      repeat light || nullable_fun_spec || unshelve eauto with has_conflict_ind subsyntax.

    destruct xs2; lights; eauto using matches_incl, incl_nil with exfalso.
    destruct xs1; lights; eauto using matches_incl, incl_nil with exfalso.

    + unshelve epose proof (H2 (t :: xs2) _);
        unfold accepts in *; lights; eauto using matches_incl, incl_nil with matches.

      visitable_extend; lights.
      eapply has_conflict_seq_follow;
        repeat light || eapply first_fun_complete || eapply should_not_follow_fun_first;
        eauto with matches.

    + repeat light || productive_fun_spec.
      apply has_conflict_seq_l.
      eapply visitable_prefix_conflict;
        eauto using subsyntax_prefix_seq_l.
Qed.

Lemma self_visitable_conflict:
  forall x ts v,
    matches (Var x) ts v ->
    visitable x (e x) ->
    has_conflict_ind (Var x).
Proof.
  repeat light || invert_matches || matches_forget_x.
  eauto using has_conflict_var, visitable_subsyntax_conflict
    with visitable matches subsyntax has_conflict_ind.
Qed.
