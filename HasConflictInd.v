Require Import Coq.Lists.List.
Import ListNotations.

Require Export Parser.DescriptionInd.
Require Export Parser.HasConflictDescr.

Opaque should_not_follow_fun.
Opaque first_fun_sound.

Definition has_conflict_ind { A } (s: Syntax A): Prop :=
  descr_ind has_conflict_descr s tt.

Definition ll1_ind { A } (s: Syntax A): Prop :=
  ~has_conflict_ind s.

Lemma has_conflict_epsilon:
  forall A (t: A),
    has_conflict_ind (Epsilon t) ->
    False.
Proof.
  unfold has_conflict_ind;
    repeat light || descr_ind_inversion.
Qed.

Lemma has_conflict_disj_l:
  forall A (s1 s2: Syntax A),
    has_conflict_ind s1 ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  unfold has_conflict_ind; intros;
    eauto 3 with lights descr_ind.
Qed.

Lemma has_conflict_disj_r:
  forall A (s1 s2: Syntax A),
    has_conflict_ind s2 ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply DisjInd2 with right_rule tt; lights.
Qed.

Lemma has_conflict_disj_first:
  forall A (s1 s2: Syntax A) k,
    In k (first_fun s1) ->
    In k (first_fun s2) ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply DisjInd0 with (some_rule tt);
    repeat light || lists || destruct_match || bools || t_disjoint;
    eauto with exfalso.
Qed.

Lemma has_conflict_disj_first2:
  forall A (s1 s2: Syntax A) t1 t2 ts1 ts2 v1 v2,
    matches s1 (t1 :: ts1) v1 ->
    matches s2 (t2 :: ts2) v2 ->
    get_kind t1 = get_kind t2 ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  intros.
  eapply has_conflict_disj_first;
    eauto using first_fun_complete;
    rewrite_any;
    eauto using first_fun_complete.
Qed.

Lemma has_conflict_disj_nullable:
  forall A (s1 s2: Syntax A),
    is_some (nullable_fun s1) ->
    is_some (nullable_fun s2) ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply DisjInd0 with (some_rule tt);
    repeat light || lists || options || destruct_match.
Qed.

Lemma has_conflict_disj_nullable2:
  forall A (s1 s2: Syntax A) v1 v2,
    matches s1 [] v1 ->
    matches s2 [] v2 ->
    has_conflict_ind (Disjunction s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply DisjInd0 with (some_rule tt);
    repeat light || lists || nullable_fun_spec || destruct_match || options.
Qed.

Lemma has_conflict_seq_l:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2),
    has_conflict_ind s1 ->
    has_conflict_ind (Sequence s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply SeqInd1 with left_rule tt; lights.
Qed.

Lemma has_conflict_seq_r:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2),
    has_conflict_ind s2 ->
    has_conflict_ind (Sequence s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply SeqInd2 with right_rule tt; lights.
Qed.

Lemma has_conflict_eps_seq:
  forall A1 A2 (v: A1) (s: Syntax A2),
    has_conflict_ind (Sequence (Epsilon v) s) ->
    has_conflict_ind s.
Proof.
  unfold has_conflict_ind;
    repeat light || descr_ind_inversion || options || lists || bools || t_disjoint || destruct_match ||
           apply_anywhere should_not_follow_fun_sound || apply_anywhere first_fun_sound ||
           invert_matches;
    eauto with matches.
Qed.

Lemma has_conflict_seq_follow:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) k,
    In k (should_not_follow_fun s1) ->
    In k (first_fun s2) ->
    has_conflict_ind (Sequence s1 s2).
Proof.
  unfold has_conflict_ind; intros.
  apply SeqInd0 with (some_rule tt);
    repeat light || lists || destruct_match || bools || t_disjoint;
    eauto with exfalso.
Qed.

Lemma has_conflict_seq_follow2:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) v1 t1 ts1 t2 ts2 v1' v2,
    matches s1 [] v1 ->
    matches s1 (t1 :: ts1) v1' ->
    matches s2 (t2 :: ts2) v2 ->
    get_kind t1 = get_kind t2 ->
    has_conflict_ind (Sequence s1 s2).
Proof.
  intros.
  eapply has_conflict_seq_follow;
    eauto using should_not_follow_fun_first;
    repeat light || rewrite_any;
    eauto using first_fun_complete.
Qed.

Lemma has_conflict_seq_follow3:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2) v1 t ts1 ts2 v1' v2,
    matches s1 [] v1 ->
    matches s1 (t :: ts1) v1' ->
    matches s2 (t :: ts2) v2 ->
    has_conflict_ind (Sequence s1 s2).
Proof.
  eauto using has_conflict_seq_follow2.
Qed.

Lemma has_conflict_map:
  forall A B (f: A -> B) g (s: Syntax A),
    has_conflict_ind s ->
    has_conflict_ind (Map f g s).
Proof.
  unfold has_conflict_ind; intros;
    eauto 3 with lights descr_ind.
Qed.

Lemma has_conflict_map2:
  forall A B (f: A -> B) g (s: Syntax A),
    has_conflict_ind (Map f g s) ->
    has_conflict_ind s.
Proof.
  unfold has_conflict_ind;
    repeat light || descr_ind_inversion.
Qed.

Lemma has_conflict_var:
  forall x,
    has_conflict_ind (e x) ->
    has_conflict_ind (Var x).
Proof.
  unfold has_conflict_ind; intros;
    eauto 3 with lights descr_ind.
Qed.

Lemma has_conflict_var2:
  forall x,
    has_conflict_ind (Var x) ->
    has_conflict_ind (e x).
Proof.
  unfold has_conflict_ind;
    repeat light || descr_ind_inversion.
Qed.

Lemma has_conflict_seq_inv:
  forall A1 A2 (s1: Syntax A1) (s2: Syntax A2),
    has_conflict_ind (Sequence s1 s2) ->
      has_conflict_ind s1 \/
      has_conflict_ind s2 \/
      (exists k, In k (should_not_follow_fun s1) /\ In k (first_fun s2)).
Proof.
  unfold has_conflict_ind;
    repeat light || descr_ind_inversion || lists || destruct_match || bools || t_disjoint;
    eauto 3 with lights.
Qed.

Lemma has_conflict_seq_monotone_l:
  forall A1 A2 (s1 s2: Syntax A1) (s: Syntax A2),
    (has_conflict_ind s1 -> has_conflict_ind s2) ->
    (forall k, In k (should_not_follow_fun s1) -> In k (should_not_follow_fun s2)) ->
    has_conflict_ind (Sequence s1 s) ->
    has_conflict_ind (Sequence s2 s).
Proof.
  repeat light || apply_anywhere has_conflict_seq_inv;
    eauto using has_conflict_seq_l, has_conflict_seq_r, has_conflict_seq_follow.
Qed.

Hint Resolve has_conflict_disj_l: has_conflict_ind.
Hint Resolve has_conflict_disj_r: has_conflict_ind.
Hint Resolve has_conflict_disj_first: has_conflict_ind.
Hint Resolve has_conflict_disj_first2: has_conflict_ind.
Hint Resolve has_conflict_disj_nullable: has_conflict_ind.
Hint Resolve has_conflict_disj_nullable2: has_conflict_ind.

Hint Resolve has_conflict_seq_l: has_conflict_ind.
Hint Resolve has_conflict_seq_r: has_conflict_ind.
Hint Immediate has_conflict_seq_follow: has_conflict_ind.
Hint Immediate has_conflict_seq_follow2: has_conflict_ind.
Hint Immediate has_conflict_seq_follow3: has_conflict_ind.
Hint Immediate has_conflict_eps_seq: has_conflict_ind.

Hint Resolve has_conflict_map: has_conflict_ind.
Hint Resolve has_conflict_var: has_conflict_ind.

Hint Immediate has_conflict_map2: has_conflict_ind.
Hint Immediate has_conflict_var2: has_conflict_ind.
Hint Extern 1 => solve [ exfalso; eauto using has_conflict_epsilon ]: has_conflict_ind.
