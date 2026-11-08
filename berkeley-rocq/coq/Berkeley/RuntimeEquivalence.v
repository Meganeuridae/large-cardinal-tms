(** Both directions of halting equivalence for the normalized register/PC
    machine, including the literal blank-tape bootstrap. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Data Machine RuntimeTape RuntimeControl RuntimeSimulation
  RuntimeTraces RuntimeProgress RuntimePC RuntimeMacro RuntimeEnabled BootstrapReplay.
Import ListNotations.

Theorem tm_halting_implies_macro width s : 404<=width -> WellFormed s ->
  New.halts new_tm (encode width s) -> MacroHalts s.
Proof.
  intros W WF [n Halt]. revert s WF Halt.
  induction n using lt_wf_ind; intros s WF Halt.
  destruct (macro_enabled s WF) as [T|[t S]].
  - exists s. split; [constructor|exact T].
  - pose proof (macro_progress width s t W S) as P.
    destruct (progress_counter _ _ P) as [k [K R]].
    assert (B : k<=n) by (eapply New.within_halt; eassumption).
    assert (Ht : New.halts_in new_tm (encode width t) (n-k)) by
      (eapply New.preceeds_halt; eassumption).
    assert (WT : WellFormed t) by (eapply macro_preserves_wellformed; eassumption).
    destruct (H (n-k) ltac:(lia) t WT Ht) as [u [Run End]].
    exists u. split; [eapply macro_next; eassumption|exact End].
Qed.

Theorem normalized_halting_equivalence width s : 404<=width -> WellFormed s ->
  (New.halts new_tm (encode width s) <-> MacroHalts s).
Proof.
  intros W WF. split; [apply tm_halting_implies_macro; assumption|
    apply macro_halting_implies_tm,W].
Qed.

Definition initial_register_state : ir_state := ([],repeat 0 1909).
Lemma initial_register_state_wellformed : WellFormed initial_register_state.
Proof.
  unfold initial_register_state,WellFormed; cbn [fst snd].
  split; [apply good_empty|rewrite repeat_length; lia].
Qed.
Theorem blank_halting_iff_normalized_program :
  New.halts new_tm New.c0 <-> MacroHalts initial_register_state.
Proof.
  rewrite bootstrap_halts_iff.
  change (New.halts new_tm (encode 3819 initial_register_state) <-> MacroHalts initial_register_state).
  apply normalized_halting_equivalence; [lia|apply initial_register_state_wellformed].
Qed.

Print Assumptions tm_halting_implies_macro.
Print Assumptions normalized_halting_equivalence.
Print Assumptions blank_halting_iff_normalized_program.
