(** Program-counter return, marker preparation/cleanup, and control jumps. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters.
Import ListNotations.

Definition blank : side := const false.
Definition root_left := Cons false (Cons true (Cons true blank)).
Definition left_of (w : list bool) := Str_app (rev w) root_left.
Definition root_cfg w r := CR 72 root_left (Str_app w r).
Definition dispatch n := nth n
  [68;67;66;65;64;63;62;61;60;59;58;57;56;55;54;53;52;50;48;45;42;39;37;35;33;31;29;27;25;23;21;19;17;15;13] 68.
Fixpoint zeros (w : list bool) :=
  match w with [] => 0 | true::w => zeros w | false::w => S (zeros w) end.
Lemma zeros_app a b : zeros (a++b) = zeros a + zeros b.
Proof. induction a as [|[] a IH]; simpl; auto. Qed.
Lemma zeros_rev w : zeros (rev w) = zeros w.
Proof. induction w as [|[] w IH]; simpl; rewrite ?zeros_app, ?IH; simpl; lia. Qed.
Lemma zeros_repeat_true n : zeros (repeat true n) = 0.
Proof. induction n; simpl; auto. Qed.
Lemma prefix_repeat n b r : Str_app (repeat b n) r = copies n b r.
Proof. induction n; simpl; [reflexivity|now rewrite IHn]. Qed.
Lemma copies_blank n : copies n false blank = blank.
Proof. induction n; simpl; [reflexivity|rewrite IHn; symmetry; apply const_unfold]. Qed.
Lemma left_snoc w b : left_of (w++[b]) = Cons b (left_of w).
Proof. unfold left_of. rewrite rev_app_distr, Str_app_assoc. reflexivity. Qed.
Lemma left_repeat w b n : left_of (w++repeat b n) = copies n b (left_of w).
Proof. unfold left_of. rewrite rev_app_distr, rev_repeat, Str_app_assoc, prefix_repeat. reflexivity. Qed.

Lemma dispatch_one n : n <= 34 -> edge (dispatch n) true true L (dispatch n).
Proof. intro H. do 35 (destruct n as [|n]; [reflexivity|]); lia. Qed.
Lemma dispatch_zero n : n < 34 -> edge (dispatch (S n)) false false L (dispatch n).
Proof. intro H. do 35 (destruct n as [|n]; [try reflexivity; try lia|]); lia. Qed.

Lemma dispatch_word bits n l r : zeros bits <= n -> n <= 34 ->
  Runs (CL (dispatch n) (Str_app bits l) r)
       (CL (dispatch (n - zeros bits)) l (Str_app (rev bits) r)).
Proof.
  revert n r. induction bits as [|b bits IH]; intros n r H Hn.
  - cbn [Str_app zeros rev]. rewrite Nat.sub_0_r. apply runs_refl.
  - destruct b.
    + cbn [Str_app zeros rev] in *.
      eapply runs_trans; [apply step_LL, dispatch_one; exact Hn|].
      rewrite Str_app_assoc. cbn [Str_app]. apply IH; assumption.
    + cbn [Str_app zeros rev] in *. destruct n as [|n]; [lia|].
      eapply runs_trans; [apply step_LL, dispatch_zero; lia|].
      rewrite Str_app_assoc. cbn [Str_app]. apply IH; lia.
Qed.

(** Dispatch may move arbitrarily far left into blank tape. This induction
    proves it returns, with the entire finite PC word preserved. *)
Lemma dispatch_bounce_any n z b r : n <= 34 ->
  Runs (CL (dispatch n) blank (copies z false (Cons true (Cons true (Cons b r)))))
       (CR 72 root_left r).
Proof.
  revert z. induction n as [|n IH]; intros z H.
  - change (Runs (CL 68 (Cons false blank) (copies z false (Cons true (Cons true (Cons b r))))) (CR 72 root_left r)).
    ll 69 false.
    change (Runs (CR 69 blank (copies (S(S z)) false (Cons true (Cons true (Cons b r))))) (CR 72 root_left r)).
    eapply runs_trans; [apply (scan_R 69 false false (S(S z))); reflexivity|].
    rewrite copies_blank. rr 70 true. rr 71 true. eapply runs_trans; [apply step_RR; destruct b; reflexivity|]. apply runs_refl.
  - change (Runs (CL (dispatch (S n)) (Cons false blank)
                    (copies z false (Cons true (Cons true (Cons b r))))) (CR 72 root_left r)).
    eapply runs_trans; [apply step_LL, dispatch_zero; lia|].
    change (Runs (CL (dispatch n) blank (copies (S z) false (Cons true (Cons true (Cons b r))))) (CR 72 root_left r)).
    apply IH. lia.
Qed.

Lemma dispatch_bounce n z r : n <= 34 ->
  Runs (CL (dispatch n) blank (copies z false (Cons true (Cons true (Cons false r)))))
       (CR 72 root_left r).
Proof. apply dispatch_bounce_any. Qed.

Theorem dispatch_from_left bits n r : zeros bits < n -> n <= 34 ->
  Runs (CL (dispatch n) (Str_app bits root_left) r)
       (root_cfg (rev bits) r).
Proof.
  intros Hz Hn. eapply runs_trans; [apply dispatch_word; lia|].
  assert (Hrem : 1 <= n - zeros bits) by lia.
  remember (n-zeros bits) as k eqn:E. destruct k as [|k]; [lia|].
  unfold root_left at 1.
  eapply runs_trans; [apply step_LL, dispatch_zero; lia|].
  change (Runs (CL (dispatch k) (copies 2 true blank) (Cons false (Str_app (rev bits) r))) (root_cfg (rev bits) r)).
  eapply runs_trans; [apply (scan_L _ true true 2), dispatch_one; lia|].
  apply (dispatch_bounce k 0). lia.
Qed.

Lemma continue_left bits r : zeros bits <= 33 ->
  Runs (CL 11 (Str_app bits root_left) r) (root_cfg (rev bits) r).
Proof.
  revert r. induction bits as [|b bits IH]; intros r H.
  - change (Runs (CL 11 (Cons false (Cons true (Cons true blank))) r) (root_cfg [] r)).
    ll 11 false. ll 13 true. ll 13 true. apply (dispatch_bounce 34 0). lia.
  - destruct b; cbn [Str_app zeros rev] in *.
    + ll 13 true.
      unfold root_cfg. rewrite Str_app_assoc. cbn [Str_app].
      apply (dispatch_from_left bits 34). all: lia.
    + ll 11 false.
      unfold root_cfg. rewrite Str_app_assoc. cbn [Str_app]. apply IH. lia.
Qed.

Theorem continue_to_root w r : zeros w <= 33 ->
  Runs (CL 11 (left_of w) r) (root_cfg w r).
Proof.
  intro H. unfold left_of. rewrite <- (rev_involutive w) at 2.
  apply continue_left. rewrite zeros_rev. exact H.
Qed.

Lemma cleanup_to_continue l z m r :
  Runs (CR 22 l (copies z false (reg m r)))
       (CL 11 l (copies (z+m) false (Cons true (Cons false r)))).
Proof.
  eapply runs_trans; [apply (scan_R 22 false false z); reflexivity|].
  cbn [reg copies]. rr 24 false.
  eapply runs_trans; [apply (scan_R 24 true false m); reflexivity|].
  rewrite copies_snoc, <- copies_add.
  rl 26 false. ll 11 true.
  eapply runs_trans; [apply (scan_L 11 false false (m+z)); reflexivity|].
  replace (z+m) with (m+z) by lia. apply runs_refl.
Qed.

Theorem cleanup_to_root w z m r : zeros w <= 33 ->
  Runs (CR 22 (left_of w) (copies z false (reg m r)))
       (root_cfg w (copies (z+m) false (Cons true (Cons false r)))).
Proof.
  intro H. eapply runs_trans; [apply cleanup_to_continue|apply continue_to_root,H].
Qed.

Definition root_exited := Cons true (Cons true (Cons true blank)).
Lemma cleanup_root_exit z m r :
  Runs (CR 22 root_exited (copies z false (reg m r)))
       (root_cfg [] (copies (z+m) false (Cons true (Cons false r)))).
Proof.
  eapply runs_trans; [apply cleanup_to_continue|]. unfold root_exited.
  ll 13 true. ll 13 true. ll 13 true. apply (dispatch_bounce_any 34 0 true). lia.
Qed.

Theorem preparation_to_root q w m r : edge q false true R 6 -> zeros w <= 32 ->
  Runs (CR q (left_of w) (copies (S(S m)) false (Cons true (Cons false r))))
       (root_cfg w (Cons true (Cons false (reg m r)))).
Proof.
  intros E H. cbn [copies].
  eapply runs_trans; [apply step_RR; exact E|]. rr 8 false.
  eapply runs_trans; [apply (scan_R 8 false true m); reflexivity|]. rl 11 true.
  pose (w' := (w++[true;false]) ++ repeat true m).
  assert (EL : left_of w' = copies m true (Cons false (Cons true (left_of w)))).
  { unfold w'. rewrite left_repeat.
    replace (w++[true;false]) with ((w++[true])++[false]) by (rewrite <- app_assoc; reflexivity).
    now rewrite !left_snoc. }
  assert (Hz : zeros w' <= 33).
  { unfold w'. rewrite !zeros_app, zeros_repeat_true. simpl. lia. }
  pose proof (continue_to_root w' (Cons true (Cons false r)) Hz) as C.
  rewrite EL in C. eapply runs_trans; [exact C|].
  unfold root_cfg, w'. rewrite !Str_app_assoc, prefix_repeat.
  cbn [Str_app reg copies]. rewrite copies_snoc. apply runs_refl.
Qed.

Lemma break0_carry n l r :
  Runs (CL 20 (copies n true (Cons false l)) r)
       (CR 22 (Cons true l) (copies n false r)).
Proof.
  eapply runs_trans; [apply (scan_L 20 true false n); reflexivity|].
  apply step_LR. reflexivity.
Qed.
Lemma break1_carry n l r :
  Runs (CL 46 (copies n true (Cons false l)) r)
       (CL 20 l (copies (S n) false r)).
Proof.
  eapply runs_trans; [apply (scan_L 46 true false n); reflexivity|].
  apply step_LL. reflexivity.
Qed.
Lemma break2_carry n l r :
  Runs (CL 399 (copies n true (Cons false l)) r)
       (CL 46 l (copies (S n) false r)).
Proof.
  eapply runs_trans; [apply (scan_L 399 true false n); reflexivity|].
  apply step_LL. reflexivity.
Qed.

Definition break_state n := nth n [20;46;399] 20.
Fixpoint break_pc k bits : option (list bool * nat) :=
  match bits with
  | [] => None
  | true::xs => option_map (fun '(w,n) => (w,S n)) (break_pc k xs)
  | false::xs => match k with
    | 0 => Some (true::xs,0)
    | S k => option_map (fun '(w,n) => (w,S n)) (break_pc k xs)
    end
  end.
Lemma break_ones k : k <= 2 -> edge (break_state k) true false L (break_state k).
Proof. intro H. destruct k as [|[|[|k]]]; try reflexivity; lia. Qed.
Lemma break_zero k : k < 2 -> edge (break_state (S k)) false false L (break_state k).
Proof. intro H. destruct k as [|[|k]]; try reflexivity; lia. Qed.
Theorem break_pc_correct k bits out n l r : k <= 2 -> break_pc k bits = Some (out,n) ->
  Runs (CL (break_state k) (Str_app bits l) r)
       (CR 22 (Str_app out l) (copies n false r)).
Proof.
  revert k out n r. induction bits as [|b bits IH]; intros k out n r H E; [discriminate|].
  destruct b; cbn [break_pc] in E; cbn [Str_app].
  - destruct (break_pc k bits) as [[out' n']|] eqn:F; [|discriminate].
    inversion E; subst. eapply runs_trans; [apply step_LL, break_ones; exact H|].
    cbn [copies]. rewrite <- copies_snoc. apply IH; assumption.
  - destruct k as [|k].
    + inversion E; subst. apply step_LR. reflexivity.
    + destruct (break_pc k bits) as [[out' n']|] eqn:F; [|discriminate].
      inversion E; subst. eapply runs_trans; [apply step_LL, break_zero; lia|].
      cbn [copies]. rewrite <- copies_snoc. apply IH; [lia|exact F].
Qed.

Print Assumptions dispatch_from_left.
Print Assumptions cleanup_to_root.
Print Assumptions preparation_to_root.
Print Assumptions break_pc_correct.
