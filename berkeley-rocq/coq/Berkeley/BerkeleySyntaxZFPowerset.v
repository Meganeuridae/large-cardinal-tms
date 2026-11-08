(** Powerset from the actual first-order ZF prefix. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxInterpretation BerkeleySyntaxSets BerkeleySyntaxZFBase.
Import ListNotations.

Definition RelPowerset {D} (R:D->D->Prop) p a := forall z, R z p <-> RelSubset R z a.

Section Powerset.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_powerset_exists : forall a, exists p, RelPowerset R p a.
Proof.
  intro a. set (rho := fun _ : nat => a).
  pose proof (Model 18 (nth 18 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (b_holds R rho (b_ex (fun p => b_all (fun z => b_iff (b_mem z p) (b_subset z 0)))) 1) in H.
  rewrite (b_holds_ex EM) in H. destruct H as [p H]. exists p. intro z.
  rewrite b_holds_all in H. specialize (H z). rewrite (b_holds_iff EM),b_holds_mem in H.
  replace (b_next (b_mem 2 1) 3) with 3 in H by reflexivity. rewrite subset_builder_holds in H by lia.
  cbv [rho update_variable Nat.eqb] in H. exact H.
Qed.
End Powerset.

Print Assumptions zf_prefix_powerset_exists.
