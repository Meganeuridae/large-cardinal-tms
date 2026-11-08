(** Exact model-level identification of the nonlogical candidate axioms with
    the first-order ZF prefix plus canonical internal Berkeley elementarity. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics LogicSemantics BerkeleySyntaxZFBase
  BerkeleySyntaxUniform BerkeleySyntaxSetupFinal.
Import ListNotations.

Lemma candidate_axioms_exact_length : length candidate_axioms=24.
Proof. vm_compute. reflexivity. Qed.

Section Models.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable seed : D.

Theorem candidate_model_iff_zf_uniform_berkeley :
  satisfies_nonlogical_schemas R <-> (satisfies_zf_prefix R /\ RelUniformBerkeley R).
Proof.
  split.
  - intro Model. assert (ZF : satisfies_zf_prefix R).
    { intros i f vars holes rho Bounds N. exact (Model i f vars holes rho ltac:(lia) N). }
    split; [exact ZF|].
    set (rho := fun _ : nat => seed). set (vars := fun n:nat => n). set (holes := fun _ : nat => FEqual 0 0).
    apply (proj1 (candidate_axiom_iff_uniform_berkeley R EM ZF rho vars holes)).
    eapply (Model 23 (nth 23 candidate_axioms (Hole 0)) vars holes rho); [lia|reflexivity].
  - intros [ZF Berkeley] i f vars holes rho Lower N.
    assert (Bound : i<24).
    { rewrite <- candidate_axioms_exact_length. apply nth_error_Some. rewrite N. discriminate. }
    destruct (Nat.eq_dec i 23) as [Eq|Ne].
    + subst i. change (Some (nth 23 candidate_axioms (Hole 0))=Some f) in N. inversion N; subst f.
      apply (proj2 (candidate_axiom_iff_uniform_berkeley R EM ZF rho vars holes)). exact Berkeley.
    + exact (ZF i f vars holes rho ltac:(lia) N).
Qed.
End Models.

Print Assumptions candidate_axioms_exact_length.
Print Assumptions candidate_model_iff_zf_uniform_berkeley.
