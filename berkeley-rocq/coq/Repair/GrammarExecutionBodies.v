(** Checked sequential source contexts for modus ponens and generalization. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerRegisters ConstructorRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution ConstructorStreams ConstructorControl GrammarExecutionBlocks GrammarExecutionDispatch GrammarExecutionSelect SourceExecution.
Import ListNotations.

Definition special_body_roots op :=
  match op with
  | 1 => [650;652;51;17;44;653;656;20;670;680]
  | 2 => [650;17;51;61;680]
  | _ => []
  end.
Definition special_body_parent op := switch_pc op ++ [false;true;true].
Definition special_body_cursor op j := special_body_parent op ++ repeat true j.
Definition special_body_context op j := special_body_cursor op j ++ [false].
Definition special_body_path_check op j :=
  match source_prefix_find source_graph source_root (special_body_context op j),
        nth_error (special_body_roots op) j with
  | Some a,Some b => Nat.eqb a b
  | _,_ => false
  end.
Definition special_body_check op :=
  andb (forallb (special_body_path_check op) (seq 0 (length(special_body_roots op))))
       (leaf_matches (special_body_cursor op (length(special_body_roots op))) (SBreak 1)).
Lemma special_body_paths_certificate : andb (special_body_check 1) (special_body_check 2) = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque source_graph.

Lemma special_body_check_true op : (op=1 \/ op=2) -> special_body_check op = true.
Proof.
  intros [A|A]; subst op; pose proof special_body_paths_certificate as C;
    apply andb_true_iff in C as [C1 C2]; assumption.
Qed.

Theorem special_body_paths op j root : (op=1 \/ op=2) ->
  nth_error (special_body_roots op) j = Some root ->
  SourcePrefix source_graph source_root (special_body_context op j) root.
Proof.
  intros H R. pose proof (special_body_check_true op H) as Good.
  unfold special_body_check in Good. apply andb_true_iff in Good as [Good _].
  rewrite forallb_forall in Good.
  assert (I : In j (seq 0 (length (special_body_roots op)))).
  { apply in_seq. assert (K : j < length(special_body_roots op)).
    { apply nth_error_Some. rewrite R. discriminate. } lia. }
  specialize (Good j I). unfold special_body_path_check in Good. rewrite R in Good.
  destruct (source_prefix_find source_graph source_root (special_body_context op j)) as [n|] eqn:E;
    [|discriminate]. apply Nat.eqb_eq in Good. subst n. now apply source_prefix_find_sound.
Qed.

Theorem special_body_break_path op : (op=1 \/ op=2) ->
  SourceSelect source_graph source_root
    (special_body_cursor op (length(special_body_roots op))) (SBreak 1).
Proof.
  intro H. pose proof (special_body_check_true op H) as Good.
  unfold special_body_check in Good. apply andb_true_iff in Good as [_ Good].
  now apply leaf_matches_sound.
Qed.

Lemma special_body_cursor_succ op j :
  special_body_cursor op (S j) = special_body_cursor op j ++ [true].
Proof.
  unfold special_body_cursor. replace (S j) with (j+1) by lia.
  rewrite repeat_app. cbn [repeat]. now rewrite <- app_assoc.
Qed.
Lemma special_body_context_return op j :
  loop_return (special_body_context op j) = special_body_cursor op (S j).
Proof.
  unfold special_body_context. rewrite sequence_left_return. symmetry. apply special_body_cursor_succ.
Qed.

Section BodyBlocks.
Variable params : nat -> nat.
Variable View : constructor_registers -> list nat -> Prop.

Theorem special_body_block op j root tokens initial final rs :
  (op=1 \/ op=2) -> nth_error (special_body_roots op) j = Some root ->
  SourceBlock params View root tokens -> View initial rs ->
  run_tokens params tokens initial = Some final ->
  exists mid rs', SourceProgramStep (special_body_cursor op j,rs) mid /\
    SourceProgramRuns mid (special_body_cursor op (S j),rs') /\ View final rs'.
Proof.
  intros Op Root Block V Eval.
  pose proof (special_body_paths op j root Op Root) as Prefix.
  destruct (Block _ _ _ _ Prefix V Eval) as [mid [rs' [First [Tail Result]]]].
  rewrite special_body_context_return in Tail.
  exists mid,rs'. split; [|auto].
  eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact First.
Qed.
End BodyBlocks.

Lemma special_body_break_target op : (op=1 \/ op=2) ->
  exists out n,
    break_pc 1 (rev(special_body_cursor op (length(special_body_roots op)-1))++[false]) = Some(out,n) /\
    return_word out = loop_return main_switch_pc.
Proof.
  intros [H|H]; subst op; vm_compute; eexists; eexists; split; reflexivity.
Qed.

Local Opaque special_body_cursor special_body_roots main_switch_pc.
Theorem special_body_break op rs : (op=1 \/ op=2) ->
  SourceProgramStep (special_body_cursor op (length(special_body_roots op)),rs)
    (loop_return main_switch_pc,rs).
Proof.
  intro Op. pose proof (special_body_break_path op Op) as Sel.
  destruct (special_body_break_target op Op) as [out [n [E R]]]. rewrite <- R.
  assert (Index : length(special_body_roots op) = S(length(special_body_roots op)-1)).
  { destruct Op as [H|H]; subst op; reflexivity. }
  rewrite Index, special_body_cursor_succ in Sel |- *.
  eapply (source_program_break_step
    (special_body_cursor op (length(special_body_roots op)-1)) rs 1 out n);
    [exact Sel|exact E].
Qed.

Print Assumptions special_body_paths.
Print Assumptions special_body_block.
Print Assumptions special_body_break.
