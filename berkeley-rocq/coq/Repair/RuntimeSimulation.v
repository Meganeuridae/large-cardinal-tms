(** Complete two-pass register calls, in the actual compiled decision program. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl RuntimeCalls RuntimeProgram.
Import ListNotations.

(** [width] is the reserved PC capacity, excluding two marker cells. *)
Definition normal width (w : list bool) rs := root_cfg w
  (copies (S(S(width-length w))) false (Cons true (Cons false (regs rs blank)))).

Lemma inc_entry_prepares i : i < 11 -> edge (inc_entry i) false true R 6.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma dec_entry_prepares i : i < 11 -> edge (dec_entry i) false true R 6.
Proof. intro H. do 11 (destruct i as [|i]; [reflexivity|]); lia. Qed.
Lemma root_read w q r : ReadPath 73 w q ->
  Runs (root_cfg w r) (CR q (left_of w) r).
Proof. intro P. apply read_path_semantics,P. Qed.

Theorem register_prepared width w q rs :
  ReadPath 73 w q -> edge q false true R 6 ->
  Runs (normal width w rs)
    (CR q (left_of w)
      (Cons true (Cons false (reg (width-length w) (regs rs blank))))).
Proof.
  intros P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz. unfold normal.
  eapply runs_trans; [apply root_read,P|].
  eapply runs_trans; [apply preparation_to_root; eassumption|].
  apply root_read,P.
Qed.

Lemma returned_capacity width k w out n : length w <= width ->
  break_pc k (rev w++[false]) = Some(out,n) ->
  length (return_word out) <= width /\
  n+2+(width-length w) = S(S(width-length(return_word out))).
Proof.
  intros Hw E. pose proof (return_word_bound _ _ _ _ E) as [_ H]. lia.
Qed.

Theorem increment_simulation width w before v after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (inc_entry (length before)) ->
  break_pc 0 (rev w++[false]) = Some(out,n) ->
  Runs (normal width w (before++v::after))
       (normal width (return_word out) (before++S v::after)).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply runs_trans; [apply register_prepared; [exact P|apply inc_entry_prepares,Hr]|].
  pose proof (increment_call before v after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.

Theorem decrement_zero_simulation width w before after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  break_pc 1 (rev w++[false]) = Some(out,n) ->
  Runs (normal width w (before++0::after))
       (normal width (return_word out) (before++0::after)).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply runs_trans; [apply register_prepared; [exact P|apply dec_entry_prepares,Hr]|].
  pose proof (decrement_zero_call before after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.

Theorem decrement_positive_simulation width w before v after out n :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  break_pc 0 (rev w++[false]) = Some(out,n) ->
  Runs (normal width w (before++S v::after))
       (normal width (return_word out) (before++v::(after++[0]))).
Proof.
  intros Hr Hw P E. pose proof (read_path_bounds _ _ _ P) as [_ Hz].
  change (zeros w <= 33) in Hz.
  eapply runs_trans; [apply register_prepared; [exact P|apply dec_entry_prepares,Hr]|].
  pose proof (decrement_positive_call before v after (width-length w) w out n blank Hr ltac:(lia) E) as C.
  assert (B : Cons false blank = blank) by (symmetry; apply const_unfold).
  rewrite B in C. destruct (returned_capacity _ _ _ _ _ Hw E) as [_ H].
  rewrite H in C. exact C.
Qed.

(** No extra assumption that the return search terminates: the literal
    decision graph certifies the needed PC zero. *)
Lemma register_return_exists w i k : i < 11 -> k <= 1 ->
  (ReadPath 73 w (inc_entry i) \/ ReadPath 73 w (dec_entry i)) ->
  exists out n, break_pc k (rev w++[false]) = Some(out,n).
Proof.
  intros Hi Hk P. apply break_pc_total. rewrite zeros_app, zeros_rev.
  pose proof (register_path_has_zero _ _ Hi P). simpl. lia.
Qed.

Theorem increment_total width w before v after :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (inc_entry (length before)) ->
  exists w', length w' <= width /\
    Runs (normal width w (before++v::after)) (normal width w' (before++S v::after)) /\
    (New.halts new_tm (normal width w (before++v::after)) <->
     New.halts new_tm (normal width w' (before++S v::after))).
Proof.
  intros Hr Hw P.
  destruct (register_return_exists w (length before) 0 Hr ltac:(lia) (or_introl P)) as [out [n E]].
  exists (return_word out). pose proof (increment_simulation width w before v after out n Hr Hw P E) as H.
  split; [exact (proj1 (returned_capacity _ _ _ _ _ Hw E))|]. split; [exact H|apply runs_preserve_halting,H].
Qed.
Theorem decrement_zero_total width w before after :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  exists w', length w' <= width /\
    Runs (normal width w (before++0::after)) (normal width w' (before++0::after)) /\
    (New.halts new_tm (normal width w (before++0::after)) <->
     New.halts new_tm (normal width w' (before++0::after))).
Proof.
  intros Hr Hw P.
  destruct (register_return_exists w (length before) 1 Hr ltac:(lia) (or_intror P)) as [out [n E]].
  exists (return_word out). pose proof (decrement_zero_simulation width w before after out n Hr Hw P E) as H.
  split; [exact (proj1 (returned_capacity _ _ _ _ _ Hw E))|]. split; [exact H|apply runs_preserve_halting,H].
Qed.
Theorem decrement_positive_total width w before v after :
  length before < 11 -> length w <= width ->
  ReadPath 73 w (dec_entry (length before)) ->
  exists w', length w' <= width /\
    Runs (normal width w (before++S v::after)) (normal width w' (before++v::(after++[0]))) /\
    (New.halts new_tm (normal width w (before++S v::after)) <->
     New.halts new_tm (normal width w' (before++v::(after++[0])))).
Proof.
  intros Hr Hw P.
  destruct (register_return_exists w (length before) 0 Hr ltac:(lia) (or_intror P)) as [out [n E]].
  exists (return_word out). pose proof (decrement_positive_simulation width w before v after out n Hr Hw P E) as H.
  split; [exact (proj1 (returned_capacity _ _ _ _ _ Hw E))|]. split; [exact H|apply runs_preserve_halting,H].
Qed.

Print Assumptions increment_total.
Print Assumptions decrement_zero_total.
Print Assumptions decrement_positive_total.
