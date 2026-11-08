(** Connect the semantic fresh-variable builder to the separately checked
    alpha-equivalence theorem for the literal Berkeley axiom. *)
From Stdlib Require Import Bool.Bool Lists.List.
From Berkeley Require Import Syntax SyntaxData ConstructorStreams ProofFormula ProofPresentation FormulaSemantics FormulaAlpha
  BerkeleySyntaxBase BerkeleySyntax BerkeleyAlpha BerkeleySyntaxInterpretation.
Import ListNotations.

Lemma plain_instantiate_projection params f : plain_formula f = true ->
  instantiate_formula params f = plain_projection f.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|n]; intro H;
    cbn [plain_formula] in H; cbn [instantiate_formula plain_projection].
  - destruct x,y; try discriminate. destruct b; reflexivity.
  - f_equal. now apply IH.
  - apply andb_true_iff in H as [Hp Hq]. now rewrite IH,JH by assumption.
  - destruct x as [x|x]; [|discriminate]. cbn in H.
    cbn [variable_value plain_var]. f_equal. now apply IH.
  - discriminate.
Qed.

Theorem builder_plain_semantics {D} (R:D->D->Prop) rho holes p n :
  plain_formula (fst(p n)) = true ->
  (b_holds R rho p n <-> SynHolds R holes (named_environment rho) (fst(p n))).
Proof.
  intro Plain. unfold b_holds. rewrite plain_instantiate_projection by exact Plain.
  symmetry. apply plain_semantics. exact Plain.
Qed.

Theorem candidate_berkeley_builder_semantics {D} (R:D->D->Prop) rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <->
  b_holds R rho b_berkeley_sentence 0.
Proof.
  rewrite candidate_berkeley_interpretation. symmetry.
  apply builder_plain_semantics. exact (proj1 berkeley_formulas_plain).
Qed.

Print Assumptions builder_plain_semantics.
Print Assumptions candidate_berkeley_builder_semantics.
