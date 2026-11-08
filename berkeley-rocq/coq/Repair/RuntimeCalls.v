(** Composition of concrete microcode, PC update, cleanup, and redispatch. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl.
Import ListNotations.

Lemma break_pc_total k bits : k < zeros bits -> exists out n, break_pc k bits = Some(out,n).
Proof.
  revert k. induction bits as [|b bits IH]; intros k H; [simpl in H; lia|].
  destruct b; cbn [zeros break_pc] in *.
  - destruct (IH k H) as [out [n E]]. exists out,(S n). rewrite E. reflexivity.
  - destruct k as [|k]; [exists (true::bits),0; reflexivity|].
    destruct (IH k ltac:(lia)) as [out [n E]]. exists out,(S n). rewrite E. reflexivity.
Qed.
Lemma break_pc_zeros k bits out n : break_pc k bits = Some(out,n) ->
  zeros out + S k = zeros bits.
Proof.
  revert k out n. induction bits as [|b bits IH]; intros k out n E; [discriminate|].
  destruct b; cbn [break_pc zeros] in *.
  - destruct (break_pc k bits) as [[o z]|] eqn:F; [|discriminate].
    inversion E; subst. eapply IH; exact F.
  - destruct k as [|k].
    + inversion E; subst. cbn [zeros]. lia.
    + destruct (break_pc k bits) as [[o z]|] eqn:F; [|discriminate].
      pose proof (IH k o z F). inversion E; subst. lia.
Qed.
Lemma break_pc_length k bits out n : break_pc k bits = Some(out,n) ->
  length out + n = length bits.
Proof.
  revert k out n. induction bits as [|b bits IH]; intros k out n E; [discriminate|].
  destruct b; cbn [break_pc length] in *.
  - destruct (break_pc k bits) as [[o z]|] eqn:F; [|discriminate].
    pose proof (IH k o z F). inversion E; subst. lia.
  - destruct k as [|k].
    + inversion E; subst. cbn [length]. lia.
    + destruct (break_pc k bits) as [[o z]|] eqn:F; [|discriminate].
      pose proof (IH k o z F). inversion E; subst. lia.
Qed.
Lemma break_pc_root_shape k bits out n : break_pc k (bits++[false]) = Some(out,n) ->
  out = [true] \/ exists pre, out = pre++[false].
Proof.
  revert k out n. induction bits as [|b bits IH]; intros k out n E.
  - destruct k; cbn [app break_pc] in E; [inversion E; auto|discriminate].
  - destruct b; cbn [app break_pc] in E.
    + destruct (break_pc k (bits++[false])) as [[o z]|] eqn:F; [|discriminate].
      inversion E; subst. eapply IH; exact F.
    + destruct k as [|k].
      * inversion E; subst. right. exists (true::bits). reflexivity.
      * destruct (break_pc k (bits++[false])) as [[o z]|] eqn:F; [|discriminate].
        inversion E; subst. eapply IH; exact F.
Qed.

Definition return_word (out : list bool) := rev (removelast out).
Lemma return_word_bound k w out n : break_pc k (rev w++[false]) = Some(out,n) ->
  zeros (return_word out) <= zeros w /\ length (return_word out) + n = length w.
Proof.
  intro E. pose proof (break_pc_zeros _ _ _ _ E) as Z.
  pose proof (break_pc_length _ _ _ _ E) as L.
  rewrite zeros_app, zeros_rev in Z. rewrite app_length, rev_length in L.
  destruct (break_pc_root_shape _ _ _ _ E) as [F|[pre F]]; subst out.
  - cbn [return_word removelast rev zeros length] in *. lia.
  - unfold return_word. rewrite removelast_last, zeros_rev, rev_length.
    rewrite zeros_app in Z. rewrite app_length in L. simpl in *. lia.
Qed.

Theorem break_return_to_root k w out n z m r :
  k <= 2 -> zeros w <= 34 -> break_pc k (rev w++[false]) = Some(out,n) ->
  Runs (CL (break_state k) (left_of w) (copies z false (reg m r)))
       (root_cfg (return_word out) (copies (n+z+m) false (Cons true (Cons false r)))).
Proof.
  intros Hk Hw E.
  pose proof (break_pc_correct k (rev w++[false]) out n
    (Cons true (Cons true blank)) (copies z false (reg m r)) Hk E) as C.
  rewrite Str_app_assoc in C. cbn [Str_app] in C.
  eapply runs_trans; [exact C|]. rewrite <- copies_add.
  pose proof (return_word_bound _ _ _ _ E) as [Hz Hlen].
  destruct (break_pc_root_shape _ _ _ _ E) as [F|[pre F]]; subst out.
  - cbn [return_word removelast rev Str_app]. apply cleanup_root_exit.
  - unfold return_word. rewrite removelast_last.
    change (Runs (CR 22 (Str_app (pre++[false]) (Cons true (Cons true blank)))
                        (copies (n+z) false (reg m r)))
                 (root_cfg (rev pre) (copies (n+z+m) false (Cons true (Cons false r))))).
    rewrite Str_app_assoc. cbn [Str_app].
    unfold return_word in Hz. rewrite removelast_last in Hz.
    pose proof (cleanup_to_root (rev pre) (n+z) m r ltac:(lia)) as H.
    unfold left_of in H. rewrite rev_involutive in H. exact H.
Qed.

Theorem increment_call before v after pad w out n tail :
  length before < 11 -> zeros w <= 34 -> break_pc 0 (rev w++[false]) = Some(out,n) ->
  Runs (CR (inc_entry (length before)) (left_of w)
    (Cons true (Cons false (regs ((pad::before) ++ v::after) (Cons false tail)))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++S v::after) tail))))).
Proof.
  intros Hr Hw E. eapply runs_trans; [apply increment_pass2,Hr|].
  change (Runs (CL (break_state 0) (left_of w)
    (copies 2 false (reg pad (regs (before++S v::after) tail))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++S v::after) tail)))))).
  apply break_return_to_root; auto; lia.
Qed.
Theorem decrement_zero_call before after pad w out n tail :
  length before < 11 -> zeros w <= 34 -> break_pc 1 (rev w++[false]) = Some(out,n) ->
  Runs (CR (dec_entry (length before)) (left_of w)
    (Cons true (Cons false (regs ((pad::before) ++ 0::after) (Cons false tail)))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++0::after) (Cons false tail)))))).
Proof.
  intros Hr Hw E. eapply runs_trans; [apply decrement_zero_pass2,Hr|].
  change (Runs (CL (break_state 1) (left_of w)
    (copies 2 false (reg pad (regs (before++0::after) (Cons false tail)))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++0::after) (Cons false tail))))))).
  apply break_return_to_root; auto; lia.
Qed.
Theorem decrement_positive_call before v after pad w out n tail :
  length before < 11 -> zeros w <= 34 -> break_pc 0 (rev w++[false]) = Some(out,n) ->
  Runs (CR (dec_entry (length before)) (left_of w)
    (Cons true (Cons false (regs ((pad::before) ++ S v::after) (Cons false tail)))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++v::(after++[0])) tail))))).
Proof.
  intros Hr Hw E. eapply runs_trans; [apply decrement_positive_pass2,Hr|].
  change (Runs (CL (break_state 0) (left_of w)
    (copies 2 false (reg pad (regs (before++v::(after++[0])) tail))))
    (root_cfg (return_word out)
      (copies (n+2+pad) false (Cons true (Cons false (regs (before++v::(after++[0])) tail)))))).
  apply break_return_to_root; auto; lia.
Qed.

Theorem runs_preserve_halting a b : Runs a b ->
  (New.halts new_tm a <-> New.halts new_tm b).
Proof.
  intro H. destruct (New.with_counter H) as [n R]. split.
  - intros [k K]. exists (k-n). eapply New.preceeds_halt; [exact K|exact R|].
    eapply New.within_halt; [exact K|exact R].
  - intro Hh. eapply New.halts_multistep; eassumption.
Qed.

Print Assumptions increment_call.
Print Assumptions decrement_zero_call.
Print Assumptions decrement_positive_call.
Print Assumptions runs_preserve_halting.
