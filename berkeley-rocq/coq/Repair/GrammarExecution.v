(** Generic execution of the checked compression grammar in the actual source
    program, parameterized by a source execution contract for each token. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters CompilerReverse.
From Repair Require Import SyntaxData Certificate CompilerData CompilerGrammar CompilerReverse CompilerContexts CompilerExecution ConstructorStreams GrammarExecutionBlocks GrammarExecutionRules SourceExecution.
Import ListNotations.
Local Opaque source_graph source_token_roots source_rule_roots rules residuals
  full_grammar_environment.

Lemma token_root_in tok root table : token_root tok table = Some root -> In (tok,root) table.
Proof.
  induction table as [|[code node] rest IH]; cbn [token_root]; [discriminate|].
  destruct (Nat.eqb tok code) eqn:E.
  - intro H. apply Nat.eqb_eq in E. inversion H; subst. now left.
  - intro H. right. now apply IH.
Qed.

Lemma reference_root_sound (states : list nat) limit i root :
  (if i <? limit then nth_error states i else None) = Some root ->
  i < limit /\ nth_error states i = Some root.
Proof.
  destruct (i <? limit) eqn:E; [|discriminate].
  intro H. split; [now apply Nat.ltb_lt|exact H].
Qed.

Section GrammarExecution.
Variable params : nat -> nat.
Variable View : constructor_registers -> list nat -> Prop.
Hypothesis token_blocks : forall tok root, In (tok,root) source_token_roots ->
  SourceBlock params View root [tok].

Definition RuleBlock i : Prop := forall root, nth_error source_rule_roots i = Some root ->
  SourceBlock params View root (nth i full_grammar_environment []).

Lemma source_symbol_block limit sym root : limit <= length rules ->
  (forall i, i < limit -> RuleBlock i) -> symbol_root limit sym = Some root ->
  SourceBlock params View root (expand_symbol full_grammar_environment sym).
Proof.
  intros Bound Previous S. destruct sym as [tok|i].
  - cbn [symbol_root] in S. cbn [expand_symbol]. apply token_blocks.
    now apply token_root_in in S.
  - change ((if i <? limit then nth_error source_rule_roots i else None) = Some root) in S.
    destruct (reference_root_sound _ _ _ _ S) as [B R].
    change (SourceBlock params View root (nth i full_grammar_environment [])).
    apply (Previous i B). exact R.
Qed.

Theorem source_grammar_rule_block i : i < length rules -> RuleBlock i.
Proof.
  induction i using lt_wf_ind. intros Bound root Root.
  assert (SomeRule : nth_error rules i <> None) by (apply nth_error_Some; exact Bound).
  destruct (nth_error rules i) as [[a b]|] eqn:Rule; [|contradiction].
  destruct (grammar_rule_is_source_pair _ _ _ Rule) as [r [left [right [R [A [B Pair]]]]]].
  rewrite Root in R. inversion R; subst r.
  rewrite (full_environment_rule_expansion _ _ _ Rule).
  eapply source_blocks_pair; [exact Pair| |].
  - eapply source_symbol_block with (limit:=i) (sym:=a); [lia| |exact A].
    intros j Hj. apply H; lia.
  - eapply source_symbol_block with (limit:=i) (sym:=b); [lia| |exact B].
    intros j Hj. apply H; lia.
Qed.

Lemma source_sequence_blocks root nodes chunks : SourceSequence root nodes ->
  Forall2 (SourceBlock params View) nodes chunks ->
  SourceBlock params View root (concat chunks).
Proof.
  intros Seq. revert chunks. induction Seq as [a|root a tail b rest Pair Seq IH]; intros chunks F.
  - inversion F as [|n chunk ns chunks0 Head Tail]; subst.
    inversion Tail; subst. cbn [concat]. now rewrite app_nil_r.
  - inversion F as [|n chunk ns chunks0 Head Tail]; subst.
    cbn [concat]. eapply source_blocks_pair; [exact Pair|exact Head|].
    now apply IH.
Qed.

Lemma source_word_blocks limit word nodes : limit <= length rules ->
  (forall i, i < limit -> RuleBlock i) -> word_roots limit word = Some nodes ->
  Forall2 (SourceBlock params View) nodes (map (expand_symbol full_grammar_environment) word).
Proof.
  intros Bound Previous. revert nodes.
  induction word as [|s word IH]; intros nodes W; cbn [word_roots] in W.
  - inversion W; subst. constructor.
  - destruct (symbol_root limit s) as [root|] eqn:R; [|discriminate].
    destruct (word_roots limit word) as [rest|] eqn:T; [|discriminate].
    inversion W; subst nodes. simpl. constructor.
    + eapply source_symbol_block; eassumption.
    + apply IH. reflexivity.
Qed.

Theorem source_grammar_residual_block i word root :
  nth_error residuals i = Some word -> nth_error source_residual_roots i = Some root ->
  SourceBlock params View root (expand_word full_grammar_environment word).
Proof.
  intros W Root.
  destruct (grammar_residual_is_source_sequence _ _ W) as [r [nodes [R [Words Seq]]]].
  rewrite Root in R. inversion R; subst r.
  unfold expand_word. rewrite flat_map_concat_map.
  eapply source_sequence_blocks; [exact Seq|].
  eapply source_word_blocks with (limit:=length rules); [lia| |exact Words].
  intros j Bound. now apply source_grammar_rule_block.
Qed.

(** Conditional only on the independently stated token-source execution
    contract. The stream/formula calculation is the existing proved numeric
    theorem; this conclusion is an actual normalized source execution. *)
Theorem source_residual_constructs_formula_conditional i f root ctx rs t s :
  nth_error candidate_axioms i = Some f -> nth_error source_residual_roots i = Some root ->
  SourcePrefix source_graph source_root ctx root -> View (CR t s 0 0) rs ->
  exists mid rs', SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,rs') /\
    View (CR (formula_code params f) (cantor t s) 0 0) rs'.
Proof.
  intros F Root Prefix V.
  assert (E : nth_error (map (expand_word full_grammar_environment) residuals) i = Some (emit f)).
  { assert (Fr : nth_error repair_axioms i = Some f).
    { rewrite repair_axioms_extend_original,nth_error_app1; [exact F|].
      apply nth_error_Some. rewrite F. discriminate. }
    rewrite full_grammar_environment_definition, grammar_emits_exact_axioms, nth_error_map, Fr. reflexivity. }
  rewrite nth_error_map in E.
  destruct (nth_error residuals i) as [word|] eqn:W; [|discriminate].
  cbn in E. inversion E as [Words].
  pose proof (grammar_stream_constructs_formula params i f
    (expand_word full_grammar_environment word) t s F) as Compute.
  assert (Stream : nth_error (map (expand_word (definitions rules [])) residuals) i =
    Some (expand_word full_grammar_environment word)).
  { rewrite nth_error_map, W, full_grammar_environment_definition. reflexivity. }
  specialize (Compute Stream).
  pose proof (source_grammar_residual_block _ _ _ W Root) as Block.
  exact (Block ctx rs _ _ Prefix V Compute).
Qed.
End GrammarExecution.

Print Assumptions source_grammar_rule_block.
Print Assumptions source_grammar_residual_block.
Print Assumptions source_residual_constructs_formula_conditional.
