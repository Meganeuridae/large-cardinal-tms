(** Statically checked control contexts for the extracted source select
    routine. Node 680 is the reconstructed post-cons source root. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorUnpairGenericTree ConstructorUnpairGenericFull ConstructorUnpairGenericInstances ConstructorPush ConstructorFrame SearchPrimitivesDrain SourceExecution.
Import ListNotations.

Definition select_tree :=
  CTSeq (tree_while1 2 8)
    (CTSeq (tree_unpair 3 2 9)
      (CTSeq (tree_while1 9 3)
        (CTSeq (CTSeq (CTDec 4) (CTSeq (tree_drain 2) (tree_while1 8 2)))
               (tree_drain 8)))).
Local Transparent source_graph unfold_root.
Theorem select_source_tree : unfold_root 680 = Some select_tree.
Proof. vm_compute. reflexivity. Qed.
Lemma select_top_move_tree : unfold_root 35 = Some(tree_while1 2 8).
Proof. vm_compute. reflexivity. Qed.
Lemma select_stack_restore_tree : unfold_root 30 = Some(tree_while1 9 3).
Proof. vm_compute. reflexivity. Qed.
Lemma select_top_drain_tree : unfold_root 675 = Some(tree_drain 2).
Proof. vm_compute. reflexivity. Qed.
Lemma select_scratch_move_tree : unfold_root 676 = Some(tree_while1 8 2).
Proof. vm_compute. reflexivity. Qed.
Lemma select_scratch_drain_tree : unfold_root 679 = Some(tree_drain 8).
Proof. vm_compute. reflexivity. Qed.

Theorem select_source_prefixes :
  SourcePrefix source_graph 680 [false] 35 /\
  SourcePrefix source_graph 680 [true;false] 674 /\
  SourcePrefix source_graph 680 [true;true;false] 30 /\
  SourcePrefix source_graph 680 [true;true;true;false] 678 /\
  SourcePrefix source_graph 680 [true;true;true;true] 679 /\
  SourcePrefix source_graph 678 [true;false] 675 /\
  SourcePrefix source_graph 678 [true;true] 676.
Proof. repeat split; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.
Lemma select_if_leaf : SourceSelect source_graph 678 [false] (SDec 4).
Proof. eapply select_leaf; [vm_compute; reflexivity|reflexivity|reflexivity]. Qed.

Lemma select_if_zero_step ctx rs : SourcePrefix source_graph source_root ctx 678 ->
  nth_error rs 4=Some 0 -> SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P select_if_leaf) as Sel.
  destruct (loop_return_spec ctx) as [out [n [E R]]]. rewrite R.
  eapply constructor_step_dec_zero with (pad:=1) (i:=4) (count:=S n).
  - exact Sel.
  - lia.
  - exact N.
  - now apply constructor_first_test_return.
Qed.
Lemma select_if_positive_step ctx rs n : SourcePrefix source_graph source_root ctx 678 ->
  nth_error rs 4=Some(S n) ->
  SourceProgramStep (ctx,rs) (ctx++[true],set_register 4 n rs++[0]).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P select_if_leaf) as Sel.
  destruct (loop_first_child_return ctx) as [E W]. rewrite <- W.
  eapply constructor_step_dec_positive with (pad:=1) (i:=4) (value:=n) (count:=0).
  - exact Sel.
  - lia.
  - exact N.
  - exact E.
Qed.
Print Assumptions select_source_tree.
Print Assumptions select_source_prefixes.
Print Assumptions select_if_zero_step.
Print Assumptions select_if_positive_step.
