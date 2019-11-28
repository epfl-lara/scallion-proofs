Require Import Equations.Equations.

Require Import Psatz.

Require Export Parser.FocusedSyntax.
Require Export Parser.AmbiguityConflict.

Unset Equations With Funext.

Opaque unfocus_helper.
Opaque nullable_fun.
Opaque productive_fun.
Opaque should_not_follow_fun.
Opaque first_fun.

Equations (noind) plug' { A T } (layers: Layers T A) (v: T): Focused_Syntax A
  by wf (length layers) lt :=

  plug' (Empty T) v := {| core := Epsilon v; layers := Empty T |};
  plug' (Cons (LApply f g) ls) v := plug' ls (f v);
  plug' (Cons (LPrepend _ v') ls) v := plug' ls (v', v);
  plug' (Cons (LFollowBy _ s) ls) v := {| core := s; layers := Cons (LPrepend _ v) ls |}.

Fail Next Obligation. (* no more obligations for plug *)

Ltac plug'_def :=
  rewrite plug'_equation_1 in * ||
  rewrite plug'_equation_2 in * ||
  rewrite plug'_equation_3 in * ||
  rewrite plug'_equation_4 in *.

Opaque plug'.

(* We wrap plug' in `Qed`-ended definition to get something really opaque *)
Definition plug_and_props:
  { plug: forall A T (layers: Layers T A) (v: T), Focused_Syntax A &
      (forall T (v : T),
        plug _ _ (Empty T) v = {| core := Epsilon v; layers := Empty T |}) /\
      (forall T3 T4 T5 (f : T4 -> T5) (g : T5 -> list T4) (ls : Layers T5 T3) (v : T4),
        plug _ _ (Cons (LApply f g) ls) v = plug _ _ ls (f v)) /\
      (forall T3 T7 T6 (v0 : T6) (ls : Layers (T6 * T7) T3) (v : T7),
        plug _ _ (Cons (LPrepend T7 v0) ls) v = plug _ _ ls (v0, v)) /\
      (forall T3 T8 T9 (s : Syntax T9) (ls : Layers (T8 * T9) T3) (v : T8),
        plug _ _ (Cons (LFollowBy T8 s) ls) v = {| core := s; layers := Cons (LPrepend T9 v) ls |}) }.
Proof.
  refine (existT _ (@plug') _);
    repeat light || plug'_def.
Qed.

Definition plug { A T } (layers: Layers T A) (v: T): Focused_Syntax A :=
  projT1 plug_and_props A T layers v.

Definition plug_equation_1 := proj1 (projT2 plug_and_props).
Definition plug_equation_2 := proj1 (proj2 (projT2 plug_and_props)).
Definition plug_equation_3 := proj1 (proj2 (proj2 (projT2 plug_and_props))).
Definition plug_equation_4 := proj2 (proj2 (proj2 (projT2 plug_and_props))).

Ltac plug_def :=
  unfold plug in * ||
  rewrite plug_equation_1 in * ||
  rewrite plug_equation_2 in * ||
  rewrite plug_equation_3 in * ||
  rewrite plug_equation_4 in *.

Lemma plug_count_follow_by:
  forall A T (ls: Layers T A) (v: T),
    ~(empty_layers ls) ->
      let ls' := layers (plug ls v) in
      length ls' + count_follow_by ls' < length ls + count_follow_by ls.
Proof.
  induction ls; repeat light || plug_def || destruct_match; try lia.

  - destruct (dec_empty_layers ls); lights.
    + destruct ls; repeat light || plug_def.
    + pose proof (IHls (f v)); lights.
      pose proof (count_follow_by_length _ _ ls); try lia.

  - destruct (dec_empty_layers ls).
    + generalize (v0, v). destruct ls; repeat light || plug_def.
    + pose proof (IHls (v0, v)); lights.
      pose proof (count_follow_by_length _ _ ls); lia.
Qed.

Lemma plug_no_conflict:
  forall A T (ls: Layers T A) (v: T),
    has_conflict_ind (core (plug ls v)) ->
    have_conflict_ind ls.
Proof.
  induction ls; repeat inversion_solve || light || plug_def || destruct_layer;
    eauto.
Qed.

Lemma plug_no_conflicts:
  forall A T (ls: Layers T A) (v: T),
    have_conflict_ind (layers (plug ls v)) ->
    have_conflict_ind ls.
Proof.
  induction ls; repeat light || plug_def || destruct_match;
    eauto.
Qed.

Lemma plug_no_conflict_unfocus:
  forall A T (ls: Layers T A) (v: T) s,
    has_conflict_ind (unfocus_helper (layers (plug ls v)) (core (plug ls v))) ->
    matches s [] v ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  induction ls; repeat light || plug_def || destruct_layer || unfocus_helper_def;
    eauto with matches;
    try inversion_solve.

  eapply unfocus_conflict_more; eauto;
    repeat light || apply_anywhere has_conflict_seq_inv || invert_matches ||
           invert_constructor_equalities;
      eauto with matches;
      eauto with has_conflict_ind;
      eauto with first_fun;
      try inversion_solve;
      try solve [ apply_anywhere should_not_follow_fun_sound; repeat light || invert_matches ].

  - repeat rewrite <- should_not_follow_ind_fun in * || unfold should_not_follow_ind in * ||
           descr_ind_inversion || light || lists || options || destruct_match.
    apply SeqInd2 with right_rule tt;
      repeat light || options || lists || destruct_match || productive_fun_spec.
Qed.

Lemma plug_sound:
  forall A T (ls: Layers T A) (v: T) (ts: list token) (a: A),
    matches (unfocus (plug ls v)) ts a ->
    matches (unfocus {| core := Epsilon v; layers := ls |}) ts a.
Proof.
  induction ls;
    repeat
      light || destruct_layer || plug_def || instantiate_any || unfold unfocus in * || unfocus_helper_def.

  - eapply matches_unfocus_sub; eauto; repeat light || invert_matches || eauto with matches.
  - eapply matches_unfocus_sub; eauto; repeat light || invert_matches || invert_constructor_equalities; eauto with matches.
Qed.

Lemma plug_complete':
  forall A T (ls: Layers T A) (v: T) (ts: list token) (a: A),
    matches (unfocus_helper ls (Epsilon v)) ts a ->
    matches (unfocus (plug ls v)) ts a.
Proof.
  induction ls;
    repeat
      light || destruct_layer || plug_def || unfold unfocus in * || unfocus_helper_def || instantiate_any || apply IHls;
    eauto with matches.

  - eapply matches_unfocus_sub; eauto; repeat light || invert_matches; eauto with matches.
  - eapply matches_unfocus_sub; eauto; repeat light || invert_matches || invert_constructor_equalities; eauto with matches.
Qed.

Lemma plug_complete:
  forall A T (ls: Layers T A) (v: T) (ts: list token) (a: A),
    matches (unfocus {| core := Epsilon v; layers := ls |}) ts a ->
    matches (unfocus (plug ls v)) ts a.
Proof.
  unfold unfocus at 1; eauto using plug_complete'.
Qed.

Lemma plug_nullable:
  forall A T (ls: Layers T A) (s: Syntax T) v1 v2,
    ~ has_conflict_ind (unfocus_helper ls s) ->
    matches (unfocus_helper ls s) [] v1 ->
    matches s [] v2 ->
    matches (unfocus (plug ls v2)) [] v1.
Proof.
  induction ls;
    repeat
      light || destruct_layer || plug_def || unfold unfocus in * ||
      invert_constructor_equalities || lists || invert_matches ||
      unfocus_helper_def || instantiate_any || matches_nil_unicity || eapply IHls ||
      matches_unfocus_helper_nil;
    eauto with matches has_conflict_ind.

  apply matches_unfocus_propagate with (Sequence s s0) (v0, v3);
    lights;
    eauto using unfocus_conflict_remains with has_conflict_ind;
    eauto with matches.

  - apply H.
    apply unfocus_conflict_more with (Sequence (Epsilon v2) s0);
      repeat light || apply_anywhere has_conflict_seq_inv ||
             rewrite <- should_not_follow_ind_fun in * ||
             rewrite first_fun_spec in * || invert_matches;
      eauto with has_conflict_ind;
      eauto 6 with matches;
      try inversion_solve.

    rewrite should_not_follow_ind_fun in *.
    eapply should_not_follow_fun_seq_monotone_l;
      repeat light || rewrite <- should_not_follow_ind_fun in *;
      eauto;
      try inversion_solve.

  - unshelve epose proof (matches_nil_unicity _ _ _ _ _ H1 H4);
      lights;
      eauto with matches;
      eauto using unfocus_conflict_remains with has_conflict_ind.
Qed.
