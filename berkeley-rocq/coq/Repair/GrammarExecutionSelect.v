(** Actual select and break continuation following a selected axiom. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeTraces CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerInstance CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorControl GrammarExecutionBlocks GrammarExecutionDispatch SourceExecution.
Import ListNotations.

Definition axiom_select_context i := axiom_parent_pc i ++ [true;false].
Definition axiom_break_word i := axiom_parent_pc i ++ [true;true].
Definition axiom_break_level i := if i <? 24 then 1 else 0.
Definition axiom_follow_check i :=
  andb (match source_prefix_find source_graph source_root (axiom_select_context i) with
        | Some n => Nat.eqb n 680 | None => false end)
       (leaf_matches (axiom_break_word i) (SBreak (axiom_break_level i))).

Lemma axiom_follow_certificate : forallb axiom_follow_check (seq 0 24) = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque source_graph.

Theorem axiom_follow_paths i : i<24 ->
  SourcePrefix source_graph source_root (axiom_select_context i) 680 /\
  SourceSelect source_graph source_root (axiom_break_word i) (SBreak (axiom_break_level i)).
Proof.
  intro I. pose proof axiom_follow_certificate as C. rewrite forallb_forall in C.
  specialize (C i ltac:(apply in_seq; lia)). unfold axiom_follow_check in C.
  apply andb_true_iff in C as [P B].
  destruct (source_prefix_find source_graph source_root (axiom_select_context i)) as [n|] eqn:E;
    [|discriminate]. apply Nat.eqb_eq in P. subst n. split.
  - now apply source_prefix_find_sound.
  - now apply leaf_matches_sound.
Qed.

Lemma loop_return_repeat_true ctx n : loop_return (ctx++repeat true n) = loop_return ctx.
Proof.
  induction n as [|n IH].
  - cbn [repeat]. now rewrite app_nil_r.
  - replace (repeat true (S n)) with (repeat true n ++ [true]).
    + rewrite app_assoc. rewrite sequence_right_return. exact IH.
    + replace (S n) with (n+1) by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma switch_loop_return j : loop_return (switch_pc j) = loop_return main_switch_pc.
Proof. unfold switch_pc. apply loop_return_repeat_true. Qed.

Lemma regular_follow_break_return ctx out n :
  break_pc 0 (rev ctx++[false]) = Some(out,n) ->
  break_pc 1 (rev(ctx++[false;true;true;true])++[false]) = Some(out,S(S(S(S n)))).
Proof. intro H. rewrite rev_app_distr. cbn [rev app break_pc]. now rewrite H. Qed.
Lemma final_follow_break_return ctx out n :
  break_pc 0 (rev ctx++[false]) = Some(out,n) ->
  break_pc 0 (rev(ctx++[true;true;true])++[false]) = Some(out,S(S(S n))).
Proof. intro H. rewrite rev_app_distr. cbn [rev app break_pc]. now rewrite H. Qed.

Lemma source_program_break_step pre rs level out n :
  SourceSelect source_graph source_root (pre++[true]) (SBreak level) ->
  break_pc level (rev pre++[false]) = Some(out,n) ->
  SourceProgramStep (pre++[true],rs) (return_word out,rs).
Proof.
  intros S E. eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break; eassumption.
Qed.

Theorem axiom_follow_break i rs : i<24 ->
  SourceProgramStep (axiom_break_word i,rs) (loop_return main_switch_pc,rs).
Proof.
  intro I. destruct (axiom_follow_paths i I) as [_ Selection].
  unfold axiom_break_word, axiom_break_level, axiom_parent_pc in *.
  destruct (i <? 24) eqn:B.
  - set (ctx := switch_pc (3+i)).
    destruct (loop_return_spec ctx) as [out [n [E Ret]]].
    assert (Eq : return_word out = loop_return main_switch_pc).
    { rewrite <- Ret. unfold ctx. apply switch_loop_return. }
    rewrite <- Eq. replace ((ctx++[false;true;true])++[true;true]) with
      ((ctx++[false;true;true;true])++[true])
      by (repeat rewrite <- app_assoc; reflexivity).
    eapply source_program_break_step with (level:=1) (out:=out) (n:=S(S(S(S n)))).
    + unfold ctx. repeat rewrite <- app_assoc in Selection |- *.
      cbn [app] in Selection |- *. exact Selection.
    + now apply regular_follow_break_return.
  - apply Nat.ltb_ge in B. lia.
Qed.

Print Assumptions axiom_follow_paths.
Print Assumptions axiom_follow_break.
