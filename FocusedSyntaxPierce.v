Require Import Equations.Init.

Require Export Parser.FocusedSyntax.
Require Export Parser.Lexicographic.
Require Export Parser.LeftRecursive.

Opaque nullable_fun.
Opaque first_fun.
Opaque unfocus_helper.

Unset Equations With Funext.

Equations (noind) pierce_helper' { A T } (k: token_class) (s: Syntax A) (ls: Layers A T)
  (* these ghost variables are only used for the measure *)
  (ghost_visited: list id)
  (pre:
     NoDup ghost_visited /\
     (forall x, In x ghost_visited -> visitable x s -> False) /\
     ~ has_conflict_ind s /\
     In k (first_fun s)
  )
    : Layers token T
  by wf (List.length vars - List.length ghost_visited, syntax_size s) lt_lex :=

  pierce_helper' k (Epsilon _) ls gv _ := False_rect _ _;
  pierce_helper' k (Failure _) ls gv _ := False_rect _ _;
  pierce_helper' k (Elem _) ls gv _ := ls;

  pierce_helper' k (Disjunction s1 s2) ls gv _ :=
    if (in_dec class_eq_dec k (first_fun s1))
    then pierce_helper' k s1 ls gv _
    else pierce_helper' k s2 ls gv _;

  pierce_helper' k (@Sequence A1 A2 s1 s2) ls gv _ :=
    let opt := nullable_fun s1 in
    if (is_some_dec opt)
    then
      if (in_dec class_eq_dec k (first_fun s1))
      then pierce_helper' k s1 (Cons (LFollowBy A1 s2) ls) gv _
      else pierce_helper' k s2 (Cons (LPrepend A2 (get_option opt _)) ls) gv _
    else
      pierce_helper' k s1 (Cons (LFollowBy A1 s2) ls) gv _;

  pierce_helper' k (@Map A B f g s') ls gv _ := pierce_helper' k s' (Cons (LApply f g) ls) gv _;
  pierce_helper' k (Var x) ls gv _ := pierce_helper' k (e x) ls (x :: gv) _.

Lemma pierce_var_measure:
  forall gv n1 n2 x,
    NoDup gv ->
    (forall y, In y gv -> visitable y (Var x) -> False) ->
    (Datatypes.length vars - S (Datatypes.length gv), n1) << (Datatypes.length vars - Datatypes.length gv, n2).
Proof.
  intros.
  pose proof (in_dec id_eq_dec x gv); lights;
    eauto with visitable exfalso.
  apply left_lex.
  unshelve epose proof (incl_more gv vars x _ _ _ _);
    repeat light || unfold incl;
    auto using all_vars;
    try lia.
Qed.

Ltac pierce_obligations_tactic :=
  repeat
    light ||
    descr_ind_inversion ||
    lists || invert_matches || app_cons_destruct ||
    rewrite first_fun_spec in * || nullable_fun_spec ||
    invert_constructor_equalities || options ||
    destruct_match ||
    destruct_unit;
  try lex;
  eauto 3 with has_conflict_ind;
  eauto with visitable;
  eauto using pierce_var_measure;
  try solve [ exfalso; eauto 6 ].

Solve All Obligations with pierce_obligations_tactic.

Next Obligation.
  pose proof (in_dec id_eq_dec x gv);
    repeat pierce_obligations_tactic || constructor || apply incl_cons;
    eauto with visitable exfalso;
    eauto using all_vars;
    eauto using self_visitable_conflict with matches.
Qed.

Next Obligation.
  unfold pierce_helper'; unfold_recursor;
    repeat light || destruct_match.
Defined.

Fail Next Obligation. (* no more obligations for pierce *)

Ltac pierce_helper'_def :=
  rewrite pierce_helper'_equation_1 in * ||
  rewrite pierce_helper'_equation_2 in * ||
  rewrite pierce_helper'_equation_3 in * ||
  rewrite pierce_helper'_equation_4 in * ||
  rewrite pierce_helper'_equation_5 in * ||
  rewrite pierce_helper'_equation_6 in * ||
  rewrite pierce_helper'_equation_7 in *.

Opaque pierce_helper'.

Opaque pierce_helper'_obligations_obligation_1.
Opaque pierce_helper'_obligations_obligation_2.
Opaque pierce_helper'_obligations_obligation_3.
Opaque pierce_helper'_obligations_obligation_4.
Opaque pierce_helper'_obligations_obligation_5.
Opaque pierce_helper'_obligations_obligation_6.
Opaque pierce_helper'_obligations_obligation_7.
Opaque pierce_helper'_obligations_obligation_8.
Opaque pierce_helper'_obligations_obligation_9.
Opaque pierce_helper'_obligations_obligation_10.
Opaque pierce_helper'_obligations_obligation_11.
Opaque pierce_helper'_obligations_obligation_12.
Opaque pierce_helper'_obligations_obligation_13.
Opaque pierce_helper'_obligations_obligation_14.
Opaque pierce_helper'_obligations_obligation_15.
Opaque pierce_helper'_obligations_obligation_16.

(* We wrap `pierce_helper'` is Qed-ended definition to make it really opaque *)
(* The equations after `&` are copied from `pierce_helper'_equations_i` *)
Definition pierce_helper_and_props:
  { pierce_helper:
      forall A T (k: token_class) (s: Syntax A) (ls: Layers A T)
        (ghost_visited: list id)
        pre, Layers token T &
           (
             forall (A0 T : Type) (k : token_class) (a : A0) (ls : Layers A0 T) ghost_visited pre,
               pierce_helper _ _ k (Epsilon a) ls ghost_visited pre =
               False_rect (Layers token T) (pierce_helper'_obligations_obligation_1 A0 k a ghost_visited pre
                                           )
           ) /\ (
             forall (A1 T : Type) (k : token_class) (ls : Layers A1 T) ghost_visited pre,
               pierce_helper _ _ k (Failure A1) ls ghost_visited pre =
               False_rect (Layers token T) (pierce_helper'_obligations_obligation_2 A1 k ghost_visited pre)
           ) /\
           (
             forall (T : Type) (k1 k2 : token_class) (ls : Layers token T) ghost_visited pre,
               pierce_helper _ _ k1 (Elem k2) ls ghost_visited pre = ls
           ) /\ (
             forall (A2 T : Type) (k : token_class) (s s0 : Syntax A2) (ls : Layers A2 T)
               ghost_visited pre,
               pierce_helper _ _ k (Disjunction s s0) ls ghost_visited pre =
               match in_dec class_eq_dec k (first_fun s) with
               | left x =>
                 pierce_helper _ _ k s ls ghost_visited
                                (pierce_helper'_obligations_obligation_3 A2 k s s0 ghost_visited pre x)
               | right x =>
                 pierce_helper _ _ k s0 ls ghost_visited
                                (pierce_helper'_obligations_obligation_5 A2 k s s0 ghost_visited pre x)
               end
           ) /\ (
             forall (A3 B T : Type) (k : token_class) (s1 : Syntax A3) (s2 : Syntax B)
               (ls : Layers (A3 * B) T) (ghost_visited : list id) pre,
               pierce_helper _ _ k (Sequence s1 s2) ls ghost_visited pre =
               (let opt := nullable_fun s1 in
                match is_some_dec opt with
                | left x =>
                  match in_dec class_eq_dec k (first_fun s1) with
                  | left x0 =>
                    pierce_helper _ _ k s1 (Cons (LFollowBy A3 s2) ls) ghost_visited
                                   (pierce_helper'_obligations_obligation_7 A3 B k s1 s2 ghost_visited pre x x0)
                  | right x0 =>
                    pierce_helper _ _ k s2
                                   (Cons
                                      (LPrepend B
                                                (get_option opt
                                                            ((let opt0 := nullable_fun s1 in
                                                              fun (i : is_some opt0) (_ : ~ In k (first_fun s1)) =>
                                                                pierce_helper'_obligations_obligation_9 A3 B k s1 s2 ghost_visited pre i) x x0)))
                                      ls) ghost_visited
                                   (pierce_helper'_obligations_obligation_10 A3 B k s1 s2 ghost_visited pre x x0)
                  end
                | right x =>
                  pierce_helper _ _ k s1 (Cons (LFollowBy A3 s2) ls) ghost_visited
                                 (pierce_helper'_obligations_obligation_12 A3 B k s1 s2 ghost_visited pre x)
                end)) /\ (
             forall (B0 T : Type) (k : token_class) (A4 : Type) (f : A4 -> B0) (g : B0 -> list A4)
               (s3 : Syntax A4) (ls : Layers B0 T) (ghost_visited : list id) pre,
               pierce_helper _ _ k (Map f g s3) ls ghost_visited pre =
               pierce_helper _ _ k s3 (Cons (LApply f g) ls) ghost_visited
                              (pierce_helper'_obligations_obligation_14 B0 k A4 f g s3 ghost_visited pre)
           ) /\ (
             forall (x : id) (T : Type) (k : token_class) (ls : Layers (get_type x) T)
               (ghost_visited : list id) pre,
               pierce_helper _ _ k (Var x) ls ghost_visited pre =
               pierce_helper _ _ k (e x) ls (x :: ghost_visited)
                              (pierce_helper'_obligations_obligation_16 x T k ls ghost_visited pre)
           )
  }.
Proof.
  refine (existT _ (@pierce_helper') _);
    repeat light || pierce_helper'_def.
Qed.

Definition pierce_helper { A T } (k: token_class) (s: Syntax A) (ls: Layers A T)
  (ghost_visited: list id) pre
    : Layers token T :=
  projT1 pierce_helper_and_props A T k s ls ghost_visited pre.

Definition pierce_helper_equation_1 := proj1 (projT2 pierce_helper_and_props).
Definition pierce_helper_equation_2 := proj1 (proj2 (projT2 pierce_helper_and_props)).
Definition pierce_helper_equation_3 := proj1 (proj2 (proj2 (projT2 pierce_helper_and_props))).
Definition pierce_helper_equation_4 := proj1 (proj2 (proj2 (proj2 (projT2 pierce_helper_and_props)))).
Definition pierce_helper_equation_5 := proj1 (proj2 (proj2 (proj2 (proj2 (projT2 pierce_helper_and_props))))).
Definition pierce_helper_equation_6 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (projT2 pierce_helper_and_props)))))).
Definition pierce_helper_equation_7 := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (projT2 pierce_helper_and_props)))))).

Ltac pierce_helper_def :=
  unfold pierce_helper in * ||
  rewrite pierce_helper_equation_1 in * ||
  rewrite pierce_helper_equation_2 in * ||
  rewrite pierce_helper_equation_3 in * ||
  rewrite pierce_helper_equation_4 in * ||
  rewrite pierce_helper_equation_5 in * ||
  rewrite pierce_helper_equation_6 in * ||
  rewrite pierce_helper_equation_7 in *.

Program Definition pierce { A T } (k: token_class) (s: Syntax A) (ls: Layers A T)
  (pre:
     ~ has_conflict_ind s /\
     In k (first_fun s)
  )
    : Layers token T
  := pierce_helper k s ls [] _.

Next Obligation.
  repeat light || constructor.
Qed.

Lemma pierce_helper_no_conflicts':
  forall m A T k (s: Syntax A) (ls: Layers A T) gv pre,
    (List.length vars - List.length gv, syntax_size s) = m ->
    have_conflict_ind (pierce_helper k s ls gv pre) ->
      have_conflict_ind ls \/
      has_conflict_ind s
.
Proof.
  induction m using measure_induction; destruct s;
    repeat
      light || find_false || pierce_helper_def || destruct_match || destruct_and ||
      apply_anywhere first_fun_sound || invert_matches;
    try solve [ eapply_anywhere H; eauto; lights; try lex; eauto with has_conflict_ind; eauto using pierce_var_measure ].
Qed.

Lemma pierce_helper_no_conflicts:
  forall A T k (s: Syntax A) (ls: Layers A T) gv pre,
    have_conflict_ind (pierce_helper k s ls gv pre) ->
      have_conflict_ind ls \/
      has_conflict_ind s
.
Proof.
  eauto using pierce_helper_no_conflicts'.
Qed.

Lemma pierce_no_conflicts:
  forall A T k (s: Syntax A) (ls: Layers A T) pre,
    have_conflict_ind (pierce k s ls pre) ->
      have_conflict_ind ls \/
      has_conflict_ind s
.
Proof.
  unfold pierce;
    eauto using pierce_helper_no_conflicts.
Qed.

Lemma pierce_helper_no_conflict_unfocus':
  forall m A T (ls: Layers T A) (s: Syntax T) t gv pre,
    (List.length vars - List.length gv, syntax_size s) = m ->
    has_conflict_ind (unfocus_helper (pierce_helper (class t) s ls gv pre) (Epsilon t)) ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  induction m using measure_induction;
    destruct s;
    repeat light || pierce_helper_def || unfocus_helper_def ||
           invert_matches || invert_constructor_equalities || destruct_match || clear_in_dec;
    try solve [ find_false ];
    try solve [ unfocus_conflict_more ];
    try solve [ eapply_anywhere H;
      repeat light || unfocus_helper_def || destruct_and; try lex; try unfocus_conflict_more;
      eauto 3 using pierce_var_measure with lights
    ].

  - pose proof i.
    destruct (nullable_fun s1) eqn:N1 at 0;
    eapply_anywhere H;
      repeat light || unfocus_helper_def || rewrite N1 in * || nullable_fun_spec;
      try lex; try unfocus_conflict_more.
Qed.

Lemma pierce_helper_no_conflict_unfocus:
  forall A T (ls: Layers T A) (s: Syntax T) t gv pre,
    has_conflict_ind (unfocus_helper (pierce_helper (class t) s ls gv pre) (Epsilon t)) ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  eauto using pierce_helper_no_conflict_unfocus'.
Qed.

Lemma pierce_no_conflict_unfocus:
  forall A T (ls: Layers T A) (s: Syntax T) t pre,
    has_conflict_ind (unfocus_helper (pierce (class t) s ls pre) (Epsilon t)) ->
    has_conflict_ind (unfocus_helper ls s).
Proof.
  unfold pierce;
    eauto using pierce_helper_no_conflict_unfocus.
Qed.
