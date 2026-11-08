(** Halting equivalence conditional only on the concrete source-iteration
    simulation contract. The contract is discharged separately. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import CompilerRegisters ProofSearchSyntax GenericSearch RepairedSearchProof.
From Repair Require Import RuntimeTraces Machine RuntimeTape RuntimeProgress RuntimeMacro RuntimeEquivalence CompilerExecution CompilerLoopBase SearchPrimitivesHalt SearchMachinePrefix SourceExecution.
Import ListNotations.
Local Notation SearchRuns := (GenericSearch.SearchRuns repaired_axiom).
Local Notation SearchHalts := (GenericSearch.SearchHalts repaired_axiom).

Definition SourceIterationContract := forall s rs, source_search_view s rs ->
  exists result mid, SourceProgramStep ([],rs) mid /\
    SourceProgramRuns mid (post_cursor,result) /\ source_search_view (repaired_search_step s) result.

Lemma source_search_view_append s rs pad : source_search_view s rs ->
  source_search_view s (rs++pad).
Proof.
  unfold source_search_view. intros [L [A [B [C [D [E [F G]]]]]]].
  split; [rewrite app_length; lia|].
  repeat split; rewrite nth_error_app1 by lia; assumption.
Qed.

Lemma source_step_run_progress width a mid b : 405<=width ->
  SourceProgramStep a mid -> SourceProgramRuns mid b ->
  Progress (encode width a) (encode width b).
Proof.
  intros W First Rest. eapply progress_then_runs with (b:=encode width mid).
  - eapply macro_progress; [exact W|now apply source_program_step_equivalence].
  - apply macro_trace_simulation; [exact W|now apply source_program_runs_equivalence].
Qed.

Lemma source_iteration_terminates s rs : SourceIterationContract -> source_search_view s rs ->
  fst (proof_stack (repaired_search_step s))=1 -> SourceProgramHalts ([],rs).
Proof.
  intros Contract V Halt. destruct (Contract s rs V) as [r1 [mid [First [Run Next]]]].
  unfold source_search_view in Next. destruct Next as [Len [_ [_ [Top _]]]]. rewrite Halt in Top.
  destruct (source_post_one_terminal_nonempty r1 Len Top) as [mid2 [Step2 [Run2 Terminal]]].
  exists (post_cursor++[true;true],set_register 2 0 r1++[0]). split; [|exact Terminal].
  eapply source_program_next; [exact First|]. eapply source_program_runs_trans; [exact Run|].
  eapply source_program_next; eassumption.
Qed.

Lemma source_iteration_continues s rs : SourceIterationContract -> source_search_view s rs ->
  fst (proof_stack (repaired_search_step s))<>1 ->
  exists result mid, SourceProgramStep ([],rs) mid /\ SourceProgramRuns mid ([],result) /\
    source_search_view (repaired_search_step s) result.
Proof.
  intros Contract V NotOne. destruct (Contract s rs V) as [r1 [mid [First [Run Next]]]].
  assert (Len : 11<=length r1) by exact (proj1 Next).
  assert (Top : nth_error r1 2=Some(fst (proof_stack (repaired_search_step s)))) by exact (proj1 (proj2 (proj2 (proj2 Next)))).
  destruct (fst (proof_stack (repaired_search_step s))) as [|[|n]] eqn:Value; [|contradiction|].
  - exists r1,mid. split; [exact First|]. split.
    + eapply source_program_runs_trans; [exact Run|]. eapply source_program_next; [apply source_post_zero_step; exact Top|constructor].
    + exact Next.
  - destruct (source_post_at_least_two_returns r1 n Len Top) as [mid2 [Step2 Run2]].
    exists (r1++[0;0]),mid. split; [exact First|]. split.
    + eapply source_program_runs_trans; [exact Run|]. eapply source_program_next; eassumption.
    + now apply source_search_view_append.
Qed.

Theorem abstract_run_implies_source_halting : SourceIterationContract ->
  forall s target, SearchRuns s target -> fst (proof_stack s)<>1 -> fst (proof_stack target)=1 ->
  forall rs, source_search_view s rs -> SourceProgramHalts ([],rs).
Proof.
  intros Contract s target Run. induction Run as [s|s target Run IH]; intros NotOne End rs V.
  - contradiction.
  - destruct (Nat.eq_dec (fst (proof_stack (repaired_search_step s))) 1) as [Halt|Next].
    + eapply source_iteration_terminates; eassumption.
    + destruct (source_iteration_continues _ _ Contract V Next) as [result [mid [Step [Trace V']]]].
      specialize (IH Next End result V'). destruct IH as [terminal [Tail Halt]].
      exists terminal. split; [|exact Halt]. eapply source_program_next; [exact Step|].
      eapply source_program_runs_trans; eassumption.
Qed.

Theorem tm_halting_implies_abstract_run width : 405<=width -> SourceIterationContract ->
  forall n s rs, source_search_view s rs -> New.halts_in new_tm (encode width ([],rs)) n ->
  exists target, SearchRuns s target /\ fst (proof_stack target)=1.
Proof.
  intros W Contract n. induction n using lt_wf_ind; intros s rs V Halt.
  destruct (Nat.eq_dec (fst (proof_stack (repaired_search_step s))) 1) as [Found|Continue].
  - exists (repaired_search_step s). split; [constructor; constructor|exact Found].
  - destruct (source_iteration_continues _ _ Contract V Continue) as [result [mid [Step [Run V']]]].
    pose proof (source_step_run_progress width _ _ _ W Step Run) as Progress.
    destruct (progress_counter _ _ Progress) as [k [Positive Multi]].
    assert (Bound : k<=n) by (eapply New.within_halt; eassumption).
    assert (Later : New.halts_in new_tm (encode width ([],result)) (n-k)) by
      (eapply New.preceeds_halt; eassumption).
    destruct (H (n-k) ltac:(lia) (repaired_search_step s) result V' Later) as [target [Trace End]].
    exists target. split; [now constructor|exact End].
Qed.

Lemma initial_source_search_view : source_search_view initial_search_state (repeat 0 1909).
Proof.
  unfold source_search_view. split; [rewrite repeat_length; lia|].
  vm_compute. repeat split; reflexivity.
Qed.

Theorem conditional_source_search_halting_iff : SourceIterationContract ->
  (SourceProgramHalts initial_register_state <-> SearchHalts).
Proof.
  intro Contract. split.
  - intro H. apply source_program_halting_equivalence in H.
    pose proof (macro_halting_implies_tm 3819 initial_register_state ltac:(lia) H) as M.
    destruct M as [n Halt]. unfold initial_register_state in Halt.
    destruct (tm_halting_implies_abstract_run 3819 ltac:(lia) Contract n
      initial_search_state (repeat 0 1909) initial_source_search_view Halt) as [target [Run End]].
    now exists target.
  - intros [target [Run End]]. unfold initial_register_state.
    eapply abstract_run_implies_source_halting; [exact Contract|exact Run| |exact End|exact initial_source_search_view].
    discriminate.
Qed.

Theorem conditional_blank_halts_iff_numeric_inconsistent : SourceIterationContract ->
  (New.halts new_tm New.c0 <-> (GenericInconsistent repaired_axiom)).
Proof.
  intro C. rewrite blank_halting_iff_source_program, conditional_source_search_halting_iff by exact C.
  apply abstract_search_halting_iff_numeric_inconsistent.
Qed.

Print Assumptions tm_halting_implies_abstract_run.
Print Assumptions conditional_source_search_halting_iff.
Print Assumptions conditional_blank_halts_iff_numeric_inconsistent.
