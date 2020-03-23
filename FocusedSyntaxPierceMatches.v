Require Export Parser.FocusedSyntaxPierce.
Require Export Parser.MatchesInversions.

Opaque unfocus_helper.
Opaque nullable_fun.
Opaque productive_fun.
Opaque should_not_follow_fun.
Opaque first_fun.

Lemma pierce_helper_sound':
  forall m A T (ls: Layers T A) (s: Syntax T) t gv pre ts v,
    (List.length vars - List.length gv, syntax_size s) = m ->
    matches (unfocus_helper (pierce_helper (get_kind t) s ls gv pre) (Elem (get_kind t))) ts v ->
    matches (unfocus_helper ls s) ts v.
Proof.
  induction m using measure_induction;
    destruct s;
    repeat light || pierce_helper_def || unfocus_helper_def || apply_anywhere first_fun_sound ||
           invert_matches || invert_constructor_equalities || destruct_match || clear_in_dec;
    try solve [ find_false ];
    try solve [ eapply_anywhere H;
      repeat light || unfocus_helper_def || destruct_and; try lex; try unfocus_conflict_more;
      eauto 3 using pierce_var_measure with lights;
      eauto using matches_unfocus_helper_sub with matches
    ].

  pose proof i.
  destruct (nullable_fun s1) eqn:N1 at 0;
  eapply_anywhere H;
    repeat light || unfocus_helper_def || rewrite N1 in *;
    try lex; try unfocus_conflict_more.

  eapply matches_unfocus_helper_sub; eauto;
    repeat light || invert_matches || invert_constructor_equalities ||
           erewrite get_option_some by eassumption.

  nullable_fun_spec; eauto with matches.
Qed.

Lemma pierce_helper_sound:
  forall A T (ls: Layers T A) (s: Syntax T) t gv pre ts v,
    matches (unfocus_helper (pierce_helper (get_kind t) s ls gv pre) (Elem (get_kind t))) ts v ->
    matches (unfocus_helper ls s) ts v.
Proof.
  eauto using pierce_helper_sound'.
Qed.

Lemma pierce_sound:
  forall A (fs: Focused_Syntax A) t pre ts v,
    matches (unfocus_helper (pierce (get_kind t) (core fs) (layers fs) pre) (Elem (get_kind t))) ts v ->
    matches (unfocus fs) ts v.
Proof.
  unfold unfocus, pierce;
    eauto using pierce_helper_sound.
Qed.

Lemma pierce_helper_complete':
  forall m A T (ls: Layers T A) (s: Syntax T) gv t ts v pre,
    (List.length vars - List.length gv, syntax_size s) = m ->
    In (get_kind t) (first_fun s) ->
    ~ has_conflict_ind (unfocus_helper ls s) ->
    matches (unfocus_helper ls s) (t :: ts) v ->
    matches (unfocus_helper (pierce_helper (get_kind t) s ls gv pre) (Elem (get_kind t))) (t :: ts) v.
Proof.
  induction m using measure_induction;
    destruct s;
    repeat light || pierce_helper_def || unfocus_helper_def || apply_anywhere first_fun_sound ||
           invert_matches || invert_constructor_equalities || destruct_match || clear_in_dec;
    try solve [ find_false ];
    try solve [
      eapply_any;
        repeat light || unfocus_helper_def || destruct_and || nullable_fun_spec ||
               clear_some_dec || options || destruct_match ||
               apply_anywhere first_fun_disj ||
               apply_anywhere first_fun_seq;
        try lex;
        eauto 3 using pierce_var_measure with lights;
        eauto using
          unfocus_conflict_disj_l,
          unfocus_conflict_disj_r,
          unfocus_conflict_eps_seq,
          unfocus_conflict_var
          with exfalso;
        eauto with first_fun;
        try solve [
          eapply matches_unfocus_helper_sub_first;
            eauto; repeat light;
            eauto using matches_inv_disj_l, matches_inv_disj_r, matches_inv_seq;
            eauto with first_fun;
            try solve [ repeat light || invert_matches ]
        ]
    ].
Qed.

Lemma pierce_helper_complete:
  forall A T (ls: Layers T A) (s: Syntax T) gv t ts v pre,
    In (get_kind t) (first_fun s) ->
    ~ has_conflict_ind (unfocus_helper ls s) ->
    matches (unfocus_helper ls s) (t :: ts) v ->
    matches (unfocus_helper (pierce_helper (get_kind t) s ls gv pre) (Elem (get_kind t))) (t :: ts) v.
Proof.
  eauto using pierce_helper_complete'.
Qed.

Lemma pierce_complete:
  forall A (fs: Focused_Syntax A) t ts v pre,
    In (get_kind t) (first_fun (core fs)) ->
    ~ has_conflict_ind (unfocus fs) ->
    matches (unfocus fs) (t :: ts) v ->
    matches (unfocus_helper (pierce (get_kind t) (core fs) (layers fs) pre) (Elem (get_kind t))) (t :: ts) v.
Proof.
  unfold unfocus, pierce;
    eauto using pierce_helper_complete.
Qed.

Program Definition pierce_correct_statement: Prop :=
  forall A (fs: Focused_Syntax A) k
    (H1: first_ind (core fs) k)
    (H2: ll1_ind (unfocus fs)),
    forall t ts v, get_kind t = k ->
      matches (unfocus_helper (pierce k (core fs) (layers fs) _) (Elem k)) (t :: ts) v <->
      matches (unfocus fs) (t :: ts) v.

Next Obligation.
  unfold ll1_ind in *; lights; eauto using unfocus_conflict_remains.
  apply first_fun_correct; auto.
Qed.

Fail Next Obligation. (* pierce_correct_statement *)

Lemma pierce_correct: pierce_correct_statement.
Proof.
  unfold pierce_correct_statement.
  lights; eauto using pierce_sound.
  apply pierce_complete; lights.
  apply first_fun_correct; auto.
Qed.
