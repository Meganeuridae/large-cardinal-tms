(** Distinctness and ranges of the literal register and control entries. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeRegisters RuntimeControl RuntimeJumps.
Import ListNotations.

Definition inc_values := [4;87;195;171;131;143;149;156;103;138;329].
Definition dec_values := [32;84;166;169;81;89;100;107;95;117;363].
Lemma inc_values_nodup : NoDup inc_values.
Proof. unfold inc_values. repeat constructor; simpl; intuition congruence. Qed.
Lemma dec_values_nodup : NoDup dec_values.
Proof. unfold dec_values. repeat constructor; simpl; intuition congruence. Qed.

Lemma inc_entry_injective i j : i < 11 -> j < 11 -> inc_entry i = inc_entry j -> i = j.
Proof.
  intros Hi Hj E. unfold inc_entry in E. change (nth i inc_values 4 = nth j inc_values 4) in E.
  pose proof (proj1 (@NoDup_nth nat inc_values 4) inc_values_nodup i j) as H.
  apply H; cbn [inc_values]; assumption.
Qed.
Lemma dec_entry_injective i j : i < 11 -> j < 11 -> dec_entry i = dec_entry j -> i = j.
Proof.
  intros Hi Hj E. unfold dec_entry in E. change (nth i dec_values 32 = nth j dec_values 32) in E.
  pose proof (proj1 (@NoDup_nth nat dec_values 32) dec_values_nodup i j) as H.
  apply H; cbn [dec_values]; assumption.
Qed.
Lemma inc_dec_entries_disjoint i j : i < 11 -> j < 11 -> inc_entry i <> dec_entry j.
Proof.
  intros Hi Hj E.
  assert (I : In (inc_entry i) inc_values).
  { unfold inc_entry. change (In (nth i inc_values 4) inc_values).
    apply nth_In. cbn [inc_values]. exact Hi. }
  assert (J : In (dec_entry j) dec_values).
  { unfold dec_entry. change (In (nth j dec_values 32) dec_values).
    apply nth_In. cbn [dec_values]. exact Hj. }
  rewrite E in I. unfold inc_values, dec_values in *. simpl in *. intuition congruence.
Qed.
Lemma inc_entry_not_halt i : i < 11 -> inc_entry i <> 1385.
Proof.
  intros H E. assert (I : In (inc_entry i) inc_values).
  { unfold inc_entry. change (In (nth i inc_values 4) inc_values).
    apply nth_In. cbn [inc_values]. exact H. }
  rewrite E in I. unfold inc_values in I. simpl in I. intuition congruence.
Qed.
Lemma dec_entry_not_halt i : i < 11 -> dec_entry i <> 1385.
Proof.
  intros H E. assert (I : In (dec_entry i) dec_values).
  { unfold dec_entry. change (In (nth i dec_values 32) dec_values).
    apply nth_In. cbn [dec_values]. exact H. }
  rewrite E in I. unfold dec_values in I. simpl in I. intuition congruence.
Qed.

Definition continue_values := [11;94;128;130].
Definition break_values := [20;46;399].
Lemma continue_values_nodup : NoDup continue_values.
Proof. unfold continue_values. repeat constructor; simpl; intuition congruence. Qed.
Lemma break_values_nodup : NoDup break_values.
Proof. unfold break_values. repeat constructor; simpl; intuition congruence. Qed.

Lemma continue_state_injective i j : i <= 3 -> j <= 3 ->
  continue_state i = continue_state j -> i = j.
Proof.
  intros Hi Hj E. unfold continue_state in E.
  change (nth i continue_values 11 = nth j continue_values 11) in E.
  pose proof (proj1 (@NoDup_nth nat continue_values 11) continue_values_nodup i j) as H.
  apply H; [change (i < 4); lia|change (j < 4); lia|exact E].
Qed.
Lemma break_state_injective i j : i <= 2 -> j <= 2 ->
  break_state i = break_state j -> i = j.
Proof.
  intros Hi Hj E. unfold break_state in E.
  change (nth i break_values 20 = nth j break_values 20) in E.
  pose proof (proj1 (@NoDup_nth nat break_values 20) break_values_nodup i j) as H.
  apply H; [change (i < 3); lia|change (j < 3); lia|exact E].
Qed.
Lemma continue_break_disjoint i j : i <= 3 -> j <= 2 -> continue_state i <> break_state j.
Proof.
  intros Hi Hj E.
  assert (I : In (continue_state i) continue_values).
  { unfold continue_state. change (In (nth i continue_values 11) continue_values).
    apply nth_In. change (i < 4). lia. }
  assert (J : In (break_state j) break_values).
  { unfold break_state. change (In (nth j break_values 20) break_values).
    apply nth_In. change (j < 3). lia. }
  rewrite E in I. unfold continue_values, break_values in *. simpl in *. intuition congruence.
Qed.

