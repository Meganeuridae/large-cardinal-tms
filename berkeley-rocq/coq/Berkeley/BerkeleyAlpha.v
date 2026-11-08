(** The literal Berkeley axiom has the ordinary first-order meaning of the
    independent fresh-variable reconstruction. This does not yet identify
    that finite satisfaction assertion with the usual set-theoretic one. *)
From Stdlib Require Import Lists.List Bool.Bool.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics
  FormulaAlpha BerkeleySyntax.
Import ListNotations.

Lemma plain_projection_instance vars holes f : plain_formula f=true ->
  independent_instance vars holes f=plain_projection f.
Proof.
  induction f as [b x y|p IH|p IH q JH|x p IH|n]; intro H;
    cbn [plain_formula] in H; cbn [independent_instance plain_projection].
  - destruct x,y; try discriminate. destruct b; reflexivity.
  - f_equal. now apply IH.
  - apply andb_true_iff in H as [Hp Hq]. now rewrite IH,JH by assumption.
  - destruct x as [x|x]; [|discriminate]. cbn in H. cbn [independent_variable plain_var].
    f_equal. now apply IH.
  - discriminate.
Qed.
Lemma berkeley_formulas_plain :
  plain_formula reconstructed_berkeley=true /\
  plain_formula (nth 23 original_axioms (Hole 0))=true /\
  plain_formula (nth 23 candidate_axioms (Hole 0))=true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition named_environment {D : Type} (rho:nat->D) x :=
  match x with V n => rho n | P _ => rho 0 end.
Theorem candidate_berkeley_interpretation {D} (R:D->D->Prop) rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 candidate_axioms (Hole 0))) <->
  SynHolds R (fun _=>False) (named_environment rho) reconstructed_berkeley.
Proof.
  destruct berkeley_formulas_plain as [Plain [_ Candidate]].
  rewrite plain_projection_instance by exact Candidate.
  pose proof (plain_semantics R (fun _=>False) (nth 23 candidate_axioms (Hole 0))
    (named_environment rho) Candidate) as H.
  change ((SynHolds R (fun _=>False) (named_environment rho)
    (nth 23 candidate_axioms (Hole 0))) <->
    FolHolds R rho (plain_projection (nth 23 candidate_axioms (Hole 0)))) in H.
  rewrite <- H. symmetry. apply canonical_equality_sound,reconstructed_berkeley_is_candidate.
Qed.
Theorem original_berkeley_interpretation {D} (R:D->D->Prop) rho vars holes :
  FolHolds R rho (independent_instance vars holes (nth 23 original_axioms (Hole 0))) <->
  SynHolds R (fun _=>False) (named_environment rho) reconstructed_berkeley.
Proof.
  destruct berkeley_formulas_plain as [Plain [Original _]].
  rewrite plain_projection_instance by exact Original.
  pose proof (plain_semantics R (fun _=>False) (nth 23 original_axioms (Hole 0))
    (named_environment rho) Original) as H.
  change ((SynHolds R (fun _=>False) (named_environment rho)
    (nth 23 original_axioms (Hole 0))) <->
    FolHolds R rho (plain_projection (nth 23 original_axioms (Hole 0)))) in H.
  rewrite <- H. symmetry. apply canonical_equality_sound,reconstructed_berkeley_is_original.
Qed.
Print Assumptions berkeley_formulas_plain.
Print Assumptions candidate_berkeley_interpretation.
Print Assumptions original_berkeley_interpretation.
