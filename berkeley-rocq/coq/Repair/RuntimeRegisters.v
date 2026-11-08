(** Unbounded register microcode proofs for the literal quotient table.
    State numbers below are checked against Machine.new_tm in every step.
    The decomposition follows the unary-register invariant also studied in
    Cryptids/Semantics/Zf/Gadgets.lean; these are new Rocq proofs. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape.
Import ListNotations.

(** The return scanners differ only in the control result at the fence. *)
Section Return.
  Variables r1 r2 out : nat.
  Hypothesis one1 : edge r1 true true L r1.
  Hypothesis zero1 : edge r1 false false L r2.
  Hypothesis one2 : edge r2 true true L r1.
  Hypothesis zero2 : edge r2 false false L out.
  Lemma return_reg n l r :
    Runs (CL r1 (back_reg n l) r) (CL r1 l (reg n r)).
  Proof.
    unfold back_reg, reg. cbn [copies].
    eapply runs_trans; [apply step_LL; exact zero1|].
    eapply runs_trans; [apply step_LL; exact one2|].
    rewrite <- copies_snoc. apply scan_L, one1.
  Qed.
  Lemma return_regs ns l r :
    Runs (CL r1 (back ns l) r) (CL r1 l (regs ns r)).
  Proof.
    revert l r. induction ns as [|n ns IH]; intros l r; cbn [back regs].
    - apply runs_refl.
    - eapply runs_trans; [apply IH|apply return_reg].
  Qed.
  Lemma return_fence ns l r :
    Runs (CL r1 (back ns (Cons false (Cons false l))) r)
         (CL out l (Cons false (Cons false (regs ns r)))).
  Proof.
    eapply runs_trans; [apply return_regs|].
    eapply runs_trans; [apply step_LL; exact zero1|].
    apply step_LL, zero2.
  Qed.
End Return.

Lemma return0_reg n l r : Runs (CL 16 (back_reg n l) r) (CL 16 l (reg n r)).
Proof. eapply return_reg; reflexivity. Qed.
Lemma return0_fence ns l r :
  Runs (CL 16 (back ns (Cons false (Cons false l))) r)
       (CL 20 l (Cons false (Cons false (regs ns r)))).
Proof. eapply return_fence; reflexivity. Qed.
Lemma return1_fence ns l r :
  Runs (CL 40 (back ns (Cons false (Cons false l))) r)
       (CL 46 l (Cons false (Cons false (regs ns r)))).
Proof. eapply return_fence; reflexivity. Qed.

(** Complete right shift and return, for arbitrary suffix length/values.
    The explicit zero at the end is consumed by the one-cell extension. *)
Theorem increment_shift suffix m l tail :
  Runs (CR 14 (copies (S m) true l) (regs suffix (Cons false tail)))
       (CL 16 l (regs (m::suffix) tail)).
Proof.
  revert m l. induction suffix as [|n ns IH]; intros m l.
  - cbn [regs]. rl 16 false.
    unfold reg. apply scan_L. reflexivity.
  - cbn [regs reg copies]. rr 12 false.
    eapply runs_trans; [apply (scan_R 12 true true n); reflexivity|].
    rr 14 true.
    change (Runs (CR 14 (copies (S n) true (back_reg m l))
                        (regs ns (Cons false tail)))
                 (CL 16 l (reg m (regs (n::ns) tail)))).
    eapply runs_trans; [apply IH|apply return0_reg].
Qed.

Lemma decrement_shift_reg m l r :
  Runs (CL 51 (copies (S m) true (Cons false l)) r)
       (CL 51 l (reg m r)).
Proof.
  cbn [copies]. ll 49 false.
  eapply runs_trans; [apply (scan_L 49 true true m); reflexivity|].
  ll 51 true. apply runs_refl.
Qed.

(** Complete forward scan and backward shift. A successful decrement adds
    a zero register; it does not merely decrement one unary block. *)
Theorem decrement_scan_shift suffix m l tail :
  Runs (CR 47 (back_reg m (Cons false l)) (regs suffix (Cons false tail)))
       (CL 51 l (regs (m :: (suffix ++ [0])) tail)).
Proof.
  revert m l. induction suffix as [|n ns IH]; intros m l.
  - cbn [regs app]. unfold back_reg. rl 49 false. ll 51 true.
    apply decrement_shift_reg.
  - cbn [regs reg copies]. rr 44 true.
    eapply runs_trans; [apply (scan_R 44 true true n); reflexivity|].
    rewrite copies_snoc. rr 47 false.
    change (Runs (CR 47 (back_reg n (Cons false (copies (S m) true (Cons false l))))
                        (regs ns (Cons false tail)))
                 (CL 51 l (reg m (regs (n::(ns++[0])) tail)))).
    eapply runs_trans; [apply IH|apply decrement_shift_reg].
Qed.

Lemma shift_return_reg n l r :
  Runs (CL 51 (back_reg n l) r) (CL 16 l (reg n r)).
Proof.
  unfold back_reg, reg. ll 16 false. apply scan_L. reflexivity.
Qed.
Lemma shift_return_regs n ns l r :
  Runs (CL 51 (back (n::ns) l) r) (CL 16 l (regs (n::ns) r)).
Proof.
  revert n l r. induction ns as [|m ns IH]; intros n l r; cbn [back regs].
  - apply shift_return_reg.
  - eapply runs_trans; [apply (IH m)|apply return0_reg].
Qed.
Lemma shift_return_fence n ns l r :
  Runs (CL 51 (back (n::ns) (Cons false (Cons false l))) r)
       (CL 20 l (Cons false (Cons false (regs (n::ns) r)))).
Proof.
  eapply runs_trans; [apply shift_return_regs|]. ll 18 false.
  apply step_LL. reflexivity.
Qed.

Definition inc_chain n := nth n [12;10;7;98;142;138;134;128;122;116;111;143;347] 12.
Definition dec_chain n := nth n [38;36;34;93;106;99;89;100;107;112;105;125;382] 38.
Definition inc_entry n := nth n [4;88;196;172;132;144;150;157;104;139;330] 4.
Definition dec_entry n := nth n [32;85;167;170;82;90;101;108;96;118;364] 32.

Ltac finite_index n := do 13 (destruct n as [|n]; [cbn; try reflexivity; try lia|]); lia.
Lemma inc_chain_one n : n <= 12 -> edge (inc_chain n) true true R (inc_chain n).
Proof. intro H. finite_index n. Qed.
Lemma dec_chain_one n : 1 <= n -> n <= 12 -> edge (dec_chain n) true true R (dec_chain n).
Proof. intros H H'. finite_index n. Qed.
Lemma inc_chain_zero n : n < 12 -> edge (inc_chain (S n)) false false R (inc_chain n).
Proof. intro H. finite_index n. Qed.
Lemma dec_chain_zero n : n < 12 -> edge (dec_chain (S n)) false false R (dec_chain n).
Proof. intro H. finite_index n. Qed.
Lemma inc_entry_one n : n < 11 -> edge (inc_entry n) true false R (inc_chain (n+2)).
Proof. intro H. finite_index n. Qed.
Lemma dec_entry_one n : n < 11 -> edge (dec_entry n) true false R (dec_chain (n+2)).
Proof. intro H. finite_index n. Qed.

Section Select.
  Variable chain : nat -> nat.
  Hypothesis one : forall n, 1 <= n -> n <= 12 -> edge (chain n) true true R (chain n).
  Hypothesis zero : forall n, n < 12 -> edge (chain (S n)) false false R (chain n).
  Lemma select_prefix prefix l r : length prefix <= 11 ->
    Runs (CR (chain (S (length prefix))) l (Cons false (regs prefix r)))
         (CR (chain 0) (back prefix (Cons false l)) r).
  Proof.
    revert l. induction prefix as [|n ns IH]; intros l H.
    - cbn [length regs back]. apply step_RR, zero. lia.
    - cbn [length] in H |- *.
      eapply runs_trans; [apply step_RR, zero; lia|].
      cbn [regs reg].
      eapply runs_trans; [apply (scan_R _ true true (S n)); apply one; lia|].
      eapply runs_trans; [apply IH; lia|]. apply runs_refl.
  Qed.
End Select.

Lemma select_inc prefix l r : length prefix <= 11 ->
  Runs (CR (inc_chain (S (length prefix))) l (Cons false (regs prefix r)))
       (CR 12 (back prefix (Cons false l)) r).
Proof. apply select_prefix; intros; [apply inc_chain_one|apply inc_chain_zero]; lia. Qed.
Lemma select_dec prefix l r : length prefix <= 11 ->
  Runs (CR (dec_chain (S (length prefix))) l (Cons false (regs prefix r)))
       (CR 38 (back prefix (Cons false l)) r).
Proof. apply select_prefix; intros; [apply dec_chain_one|apply dec_chain_zero]; lia. Qed.

(** Pass two includes selection, mutation, all suffix shifts, and return
    to the PC fence. No bounds are placed on values or suffix length. *)
Theorem increment_pass2 before n after pad l tail : length before < 11 ->
  Runs (CR (inc_entry (length before)) l
           (Cons true (Cons false (regs ((pad::before) ++ n::after) (Cons false tail)))))
       (CL 20 l (Cons false (Cons false (regs ((pad::before) ++ (S n)::after) tail)))).
Proof.
  intro H. rewrite !regs_append.
  eapply runs_trans; [apply step_RR, inc_entry_one; exact H|].
  replace (length before + 2) with (S (length (pad::before))) by (simpl; lia).
  eapply runs_trans; [apply select_inc; simpl; lia|].
  cbn [regs]. unfold reg at 1.
  eapply runs_trans; [apply (scan_R 12 true true (S n)); reflexivity|].
  rr 14 true.
  eapply runs_trans; [apply (increment_shift after (S n))|].
  apply return0_fence.
Qed.

Theorem decrement_zero_pass2 before after pad l tail : length before < 11 ->
  Runs (CR (dec_entry (length before)) l
           (Cons true (Cons false (regs ((pad::before) ++ 0::after) (Cons false tail)))))
       (CL 46 l (Cons false (Cons false (regs ((pad::before) ++ 0::after) (Cons false tail))))).
Proof.
  intro H. rewrite !regs_append.
  eapply runs_trans; [apply step_RR, dec_entry_one; exact H|].
  replace (length before + 2) with (S (length (pad::before))) by (simpl; lia).
  eapply runs_trans; [apply select_dec; simpl; lia|].
  cbn [regs reg copies]. rr 41 false. rl 38 false. ll 40 true.
  apply return1_fence.
Qed.

Theorem decrement_positive_pass2 before n after pad l tail : length before < 11 ->
  Runs (CR (dec_entry (length before)) l
           (Cons true (Cons false (regs ((pad::before) ++ (S n)::after) (Cons false tail)))))
       (CL 20 l (Cons false (Cons false (regs ((pad::before) ++ n::(after++[0])) tail)))).
Proof.
  intro H. rewrite !regs_append.
  eapply runs_trans; [apply step_RR, dec_entry_one; exact H|].
  replace (length before + 2) with (S (length (pad::before))) by (simpl; lia).
  eapply runs_trans; [apply select_dec; simpl; lia|].
  cbn [regs reg copies]. rr 41 false. rr 44 true.
  eapply runs_trans; [apply (scan_R 44 true true n); reflexivity|].
  rewrite copies_snoc. rr 47 false.
  change (Runs (CR 47
    (back_reg n (Cons false (back (pad::before) (Cons false (Cons false l)))))
    (regs after (Cons false tail)))
    (CL 20 l (Cons false (Cons false (regs (pad::before) (regs (n::(after++[0])) tail)))))).
  eapply runs_trans; [apply decrement_scan_shift|]. apply shift_return_fence.
Qed.

Print Assumptions increment_pass2.
Print Assumptions decrement_zero_pass2.
Print Assumptions decrement_positive_pass2.
