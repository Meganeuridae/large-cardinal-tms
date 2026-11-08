From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import StateMap FiniteMachine.
From Repair Require Import Data.
Import ListNotations.

Module OldSize <: Size.
  Definition top := old_count.
  Lemma positive : 1 <= top. Proof. unfold top, old_count. lia. Qed.
End OldSize.
Module NewSize <: Size.
  Definition top := new_count.
  Lemma positive : 1 <= top. Proof. unfold top, new_count. lia. Qed.
End NewSize.
Module OldCtx := Binary OldSize.
Module NewCtx := Binary NewSize.
Module R := StateMap.StateMap OldCtx NewCtx.
Module Old := R.TA.
Module New := R.TB.

Definition old_tm : Old.TM := fun '(q,s) =>
  option_map (fun '(w,d,n) => (w,d,bounded_mk old_count n)) (lookup old_table (val q) s).
Definition new_tm : New.TM := fun '(q,s) =>
  option_map (fun '(w,d,n) => (w,d,bounded_mk new_count n)) (lookup new_table (val q) s).
Definition map_nat q := nth q state_mapping new_count.
Definition state_map (q : OldCtx.Q) : NewCtx.Q := bounded_mk new_count (map_nat (val q)).

Lemma old_table_size : length old_table = old_count.
Proof. vm_compute. reflexivity. Qed.
Lemma new_table_size : length new_table = new_count.
Proof. vm_compute. reflexivity. Qed.
Lemma mapping_values : forallb (fun n => Nat.leb n new_count) state_mapping = true.
Proof. vm_compute. reflexivity. Qed.
Lemma old_targets : forallb (fun '((_,_,n0),(_,_,n1)) =>
  andb (Nat.leb n0 old_count) (Nat.leb n1 old_count)) old_table = true.
Proof. vm_compute. reflexivity. Qed.
Lemma new_targets : forallb (fun '((_,_,n0),(_,_,n1)) =>
  andb (Nat.leb n0 new_count) (Nat.leb n1 new_count)) new_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma map_nat_bound q : map_nat q <= new_count.
Proof.
  unfold map_nat. destruct (lt_dec q (length state_mapping)).
  - pose proof mapping_values as H. rewrite forallb_forall in H.
    apply Nat.leb_le, H, nth_In. exact l.
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma lookup_old_bound q s w d n : lookup old_table q s = Some (w,d,n) -> n <= old_count.
Proof.
  unfold lookup. destruct (nth_error old_table q) as [r|] eqn:E; try discriminate.
  destruct r as [[[w0 d0] n0] [[w1 d1] n1]].
  pose proof old_targets as H. rewrite forallb_forall in H.
  apply nth_error_In in E. specialize (H _ E). simpl in H.
  apply andb_true_iff in H as [H0 H1].
  destruct s; intro K; inversion K; subst; apply Nat.leb_le; assumption.
Qed.

Lemma transition_certificate :
  forallb (fun q => forallb (fun s => option_eqb
    (lookup new_table (map_nat q) s)
    (option_map (map_target map_nat) (lookup old_table q s))) [false;true])
    (seq 0 (S old_count)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_commutes q s : q <= old_count ->
  lookup new_table (map_nat q) s = option_map (map_target map_nat) (lookup old_table q s).
Proof.
  intro Hq. pose proof transition_certificate as H. rewrite forallb_forall in H.
  specialize (H q). assert (Iq : In q (seq 0 (S old_count))) by (apply in_seq; lia).
  specialize (H Iq). rewrite forallb_forall in H. apply option_eqb_sound, H.
  destruct s; simpl; auto.
Qed.

Lemma state_map_respects : R.respects state_map old_tm new_tm.
Proof.
  intros q s. unfold new_tm, state_map.
  rewrite val_mk by apply map_nat_bound.
  rewrite table_commutes by apply val_bound.
  unfold old_tm. destruct (lookup old_table (val q) s) as [[[w d] n]|] eqn:E; simpl.
  - unfold state_map. rewrite val_mk by (eapply lookup_old_bound; exact E). reflexivity.
  - reflexivity.
Qed.

Lemma initial_map : R.lift state_map Old.c0 = New.c0.
Proof. reflexivity. Qed.

(** This certifies ONLY the repaired 1400 -> 1399 exact state quotient. *)
Theorem quotient_preserves_blank_halting :
  Old.halts old_tm Old.c0 <-> New.halts new_tm New.c0.
Proof.
  rewrite <- initial_map. apply R.halts_equiv, state_map_respects.
Qed.

Print Assumptions state_map_respects.
Print Assumptions quotient_preserves_blank_halting.
