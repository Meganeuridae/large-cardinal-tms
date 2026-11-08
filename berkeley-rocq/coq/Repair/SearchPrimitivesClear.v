(** Main's four actual register-clear loops preceding instruction decoding. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorControl ConstructorUnpair SearchPrimitivesDrain SourceExecution.
Import ListNotations.

Definition clear_cursor n := repeat true (1+n).
Definition clear_root n := nth n [632;633;634;635] 0.
Lemma clear_cursor_next n : clear_cursor n ++ [true] = clear_cursor (S n).
Proof.
  unfold clear_cursor. replace (1+S n) with ((1+n)+1) by lia.
  rewrite (repeat_app true (1+n) 1). reflexivity.
Qed.
Local Transparent source_graph unfold_root.
Lemma clear_field_path n : n<4 ->
  SourcePrefix source_graph source_root (clear_cursor n++[false]) (clear_root n).
Proof.
  intro H. do 4 (destruct n as [|n]; [apply source_prefix_find_sound; vm_compute; reflexivity|]). lia.
Qed.
Lemma clear_field_tree n : n<4 -> unfold_root (clear_root n) = Some (tree_drain (4+n)).
Proof. intro H. do 4 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.

Theorem source_clear_field_nonempty n rs value : n<4 -> 11<=length rs ->
  nth_error rs (4+n)=Some value ->
  exists mid, SourceProgramStep (clear_cursor n,rs) mid /\
    SourceProgramRuns mid (clear_cursor (S n),set_register (4+n) 0 rs ++ repeat 0 value).
Proof.
  intros H L N. destruct (source_drain_nonempty (clear_cursor n++[false]) (clear_root n) (4+n) rs value
    (clear_field_path n H) (clear_field_tree n H) ltac:(lia) L N) as [mid [First Rest]].
  rewrite constructor_loop_return_false, clear_cursor_next in Rest.
  exists mid. split; [eapply constructor_unpad_first_step with (pad:=1); exact First|exact Rest].
Qed.

Lemma clear_write_length i v rs : 11<=length rs ->
  11<=length (set_register i 0 rs ++ repeat 0 v).
Proof. intro L. rewrite app_length,repeat_length,set_register_length. lia. Qed.
Lemma clear_write_same i v rs : i<length rs ->
  nth_error (set_register i 0 rs ++ repeat 0 v) i = Some 0.
Proof.
  intro H. rewrite nth_error_app1 by (rewrite set_register_length; exact H).
  now apply nth_error_set_same.
Qed.
Lemma clear_write_other i j v rs : i<>j -> j<length rs ->
  nth_error (set_register i 0 rs ++ repeat 0 v) j = nth_error rs j.
Proof.
  intros D H. rewrite nth_error_app1 by (rewrite set_register_length; exact H).
  now apply nth_error_set_other.
Qed.

Theorem source_clear_suffix fuel n rs : n+fuel=4 -> 11<=length rs ->
  exists result, SourceProgramRuns (clear_cursor n,rs) (clear_cursor 4,result) /\
    11<=length result /\
    (forall k, n<=k -> k<4 -> nth_error result (4+k)=Some 0) /\
    (forall r, r<11 -> (r<4+n \/ 8<=r) -> nth_error result r=nth_error rs r).
Proof.
  revert n rs. induction fuel as [|fuel IH]; intros n rs Sum L.
  - assert (n=4) by lia. subst n. exists rs. repeat split; try constructor; try assumption; intros; lia.
  - assert (N : n<4) by lia.
    destruct (nth_error rs (4+n)) as [value|] eqn:V.
    2: { apply nth_error_None in V. lia. }
    set (r1:=set_register (4+n) 0 rs ++ repeat 0 value).
    pose proof (clear_write_length (4+n) value rs L) as L1. fold r1 in L1.
    destruct (source_clear_field_nonempty n rs value N L V) as [mid [Step Run]]. fold r1 in Run.
    destruct (IH (S n) r1 ltac:(lia) L1) as [result [Tail [Len [Zeros Frame]]]].
    exists result. repeat split; try assumption.
    + eapply source_program_next; [exact Step|]. eapply source_program_runs_trans; eassumption.
    + intros k K K4. destruct (Nat.eq_dec k n) as [->|D].
      * rewrite Frame by lia. unfold r1. apply clear_write_same. lia.
      * apply Zeros; lia.
    + intros r R FrameR. rewrite Frame by lia. unfold r1. apply clear_write_other; lia.
Qed.

Theorem source_clear_all_nonempty rs : 11<=length rs ->
  exists result mid, SourceProgramStep (clear_cursor 0,rs) mid /\
    SourceProgramRuns mid (clear_cursor 4,result) /\ 11<=length result /\
    nth_error result 4=Some 0 /\ nth_error result 5=Some 0 /\
    nth_error result 6=Some 0 /\ nth_error result 7=Some 0 /\
    (forall r, r<11 -> (r<4 \/ 8<=r) -> nth_error result r=nth_error rs r).
Proof.
  intro L. destruct (source_clear_suffix 4 0 rs ltac:(lia) L) as [result [Run [Len [Zeros Frame]]]].
  assert (Different : (clear_cursor 0,rs) <> (clear_cursor 4,result)).
  { intro E. apply (f_equal (fun z=>length (fst z))) in E. cbn [fst clear_cursor] in E. discriminate. }
  destruct (source_runs_nonempty_when_distinct _ _ Run Different) as [mid [Step Tail]].
  exists result,mid. repeat split; try assumption; try (apply Zeros; lia).
Qed.

Print Assumptions source_clear_suffix.
Print Assumptions source_clear_all_nonempty.
