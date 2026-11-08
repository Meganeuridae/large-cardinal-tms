(** Kernel replay of the compressed bootstrap against the literal table. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia NArith PArith.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeControl RuntimeCalls RuntimeSimulation RuntimeTraces BootstrapTape BootstrapMachine.
Import ListNotations.

Definition boot_step c := match boot_macro c with Some d => d | None => c end.
Lemma boot_step_sound c : boot_q c <= new_count ->
  boot_q (boot_step c) <= new_count /\ Runs (boot_encode c) (boot_encode (boot_step c)).
Proof.
  intro Q. unfold boot_step. destruct (boot_macro c) as [d|] eqn:E.
  - eapply boot_macro_sound; eassumption.
  - split; [exact Q|apply runs_refl].
Qed.

Lemma boot_iter_sound p c : boot_q c <= new_count ->
  boot_q (Pos.iter boot_step c p) <= new_count /\
  Runs (boot_encode c) (boot_encode (Pos.iter boot_step c p)).
Proof.
  revert c. induction p as [p IH|p IH|]; intros c Q.
  - change (boot_q (boot_step (Pos.iter boot_step (Pos.iter boot_step c p) p)) <= new_count /\
      Runs (boot_encode c)
        (boot_encode (boot_step (Pos.iter boot_step (Pos.iter boot_step c p) p)))).
    destruct (IH c Q) as [Q1 R1].
    destruct (IH _ Q1) as [Q2 R2].
    destruct (boot_step_sound _ Q2) as [Q3 R3].
    split; [exact Q3|]. eapply runs_trans; [exact R1|]. eapply runs_trans; eassumption.
  - change (boot_q (Pos.iter boot_step (Pos.iter boot_step c p) p) <= new_count /\
      Runs (boot_encode c) (boot_encode (Pos.iter boot_step (Pos.iter boot_step c p) p))).
    destruct (IH c Q) as [Q1 R1].
    destruct (IH _ Q1) as [Q2 R2]. split; [exact Q2|]. eapply runs_trans; eassumption.
  - change (boot_q (boot_step c) <= new_count /\ Runs (boot_encode c) (boot_encode (boot_step c))).
    apply boot_step_sound. exact Q.
Qed.

Definition boot_initial := BootCfg 0 (false,false) false [] [].
Definition boot_final := BootCfg 73 (false,false) false
  [((true,false),1%positive);((false,true),1%positive)]
  [((false,false),1909%positive);((false,true),1910%positive)].

Lemma boot_replay_value : Pos.iter boot_step boot_initial 745755%positive = boot_final.
Proof. vm_compute. reflexivity. Qed.
Theorem boot_replay_runs : Runs (boot_encode boot_initial) (boot_encode boot_final).
Proof.
  pose proof (boot_iter_sound 745755%positive boot_initial ltac:(cbn; unfold new_count; lia)) as [_ H].
  now rewrite boot_replay_value in H.
Qed.
Print Assumptions boot_replay_runs.

Lemma boot_initial_encode : boot_encode boot_initial = New.c0.
Proof.
  change ((st 0, (blank,false,Cons false blank)) = (st 0, (blank,false,blank))).
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  now rewrite B.
Qed.

Lemma pair_zeros n r : pair_copies n (false,false) r = copies (2*n) false r.
Proof.
  induction n; cbn [pair_copies copies]; [reflexivity|].
  replace (2*S n) with (S(S(2*n))) by lia. cbn [copies]. now rewrite IHn.
Qed.
Lemma pair_shift n a b r :
  pair_copies n (a,b) (Cons a r) = Cons a (pair_copies n (b,a) r).
Proof. induction n; cbn [pair_copies]; [reflexivity|now rewrite IHn]. Qed.
Lemma pair_shift_blank n :
  pair_copies n (false,true) blank = Cons false (pair_copies n (true,false) blank).
Proof.
  pose proof (pair_shift n false true blank) as H.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  now rewrite B in H.
Qed.
Lemma zero_regs n r : regs (repeat 0 n) r = pair_copies n (true,false) r.
Proof. induction n; cbn [repeat regs reg copies pair_copies]; [reflexivity|now rewrite IHn]. Qed.

Lemma boot_left_root :
  pair_stack true [((true,false),1%positive);((false,true),1%positive)] = root_left.
Proof.
  change (Cons false (Cons true (Cons true (Cons false blank))) = root_left).
  unfold root_left. assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  now rewrite B.
Qed.
Lemma boot_right_normal n :
  Cons false (Cons false (pair_stack false
    [((false,false),n);((false,true),Pos.succ n)])) =
  copies (S(S(2*Pos.to_nat n+1))) false
    (Cons true (Cons false (regs (repeat 0 (Pos.to_nat n)) blank))).
Proof.
  cbn [pair_stack]. rewrite Pos2Nat.inj_succ, pair_zeros, pair_shift_blank, zero_regs.
  change (copies 2 false (copies (2*Pos.to_nat n) false
      (Cons false (pair_copies (S (Pos.to_nat n)) (true,false) blank))) =
    copies (S(S(2*Pos.to_nat n+1))) false
      (pair_copies (S (Pos.to_nat n)) (true,false) blank)).
  rewrite copies_snoc.
  change (copies 3 false (copies (2*Pos.to_nat n) false
      (pair_copies (S (Pos.to_nat n)) (true,false) blank)) =
    copies (S(S(2*Pos.to_nat n+1))) false
      (pair_copies (S (Pos.to_nat n)) (true,false) blank)).
  rewrite <- copies_add.
  replace (3 + 2 * Pos.to_nat n) with (S(S(2*Pos.to_nat n+1))) by lia.
  reflexivity.
Qed.
Lemma boot_final_encode : boot_encode boot_final = normal 3819 [] (repeat 0 1909).
Proof.
  unfold boot_final, normal, root_cfg.
  change (CR 73 (pair_stack true [((true,false),1%positive);((false,true),1%positive)])
     (Cons false (Cons false (pair_stack false
       [((false,false),1909%positive);((false,true),1910%positive)]))) =
    CR 73 root_left (copies 3821 false (Cons true (Cons false (regs (repeat 0 1909) blank))))).
  rewrite boot_left_root.
  pose proof (boot_right_normal 1909%positive) as H.
  change (Cons false (Cons false (pair_stack false
    [((false,false),1909%positive);((false,true),1910%positive)])) =
    copies 3821 false (Cons true (Cons false (regs (repeat 0 1909) blank)))) in H.
  now rewrite H.
Qed.
Theorem bootstrap_to_normal : Runs New.c0 (normal 3819 [] (repeat 0 1909)).
Proof. rewrite <- boot_initial_encode, <- boot_final_encode. exact boot_replay_runs. Qed.
Theorem bootstrap_halts_iff :
  New.halts new_tm New.c0 <-> New.halts new_tm (normal 3819 [] (repeat 0 1909)).
Proof. apply runs_preserve_halting, bootstrap_to_normal. Qed.
Print Assumptions bootstrap_to_normal.
Print Assumptions bootstrap_halts_iff.

(** The existing forward intermediate halting theorem now applies to the
    literal blank input. The reverse implication still requires a coverage
    and progress invariant for the intermediate machine. *)
Theorem bootstrap_ir_halting_implies_tm :
  IRHalts ([], repeat 0 1909) -> New.halts new_tm New.c0.
Proof.
  intro H. apply (proj2 bootstrap_halts_iff).
  change (New.halts new_tm (encode 3819 ([], repeat 0 1909))).
  apply ir_halting_implies_tm_halting; [unfold fits; simpl; lia|exact H].
Qed.
Print Assumptions bootstrap_ir_halting_implies_tm.
