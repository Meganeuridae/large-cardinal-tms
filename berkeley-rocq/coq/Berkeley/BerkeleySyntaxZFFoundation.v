(** Foundation and irreflexivity from the actual first-order ZF prefix. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxPairs
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition RelFoundation {D} (R:D->D->Prop) := forall s,
  (exists x, R x s) -> exists y, R y s /\ forall z, R z y -> ~R z s.

Section Foundation.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_foundation : RelFoundation R.
Proof.
  intros s Nonempty. set (rho := fun _ : nat => s).
  pose proof (Model 22 (nth 22 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (FolHolds R rho (FAll 0 (FImp (f_ex 1 (FMember 1 0))
    (f_ex 1 (f_and (FMember 1 0) (FAll 2 (FImp (FMember 2 1) (FNeg (FMember 2 0))))))))) in H.
  change (forall x, FolHolds R (update_variable rho 0 x) (f_ex 1 (FMember 1 0)) ->
    FolHolds R (update_variable rho 0 x)
      (f_ex 1 (f_and (FMember 1 0) (FAll 2 (FImp (FMember 2 1) (FNeg (FMember 2 0))))))) in H.
  specialize (H s). assert (Ante : FolHolds R (update_variable rho 0 s) (f_ex 1 (FMember 1 0))).
  { rewrite (holds_f_ex R EM). destruct Nonempty as [x X]. exists x. cbn [FolHolds update_variable]. exact X. }
  specialize (H Ante). rewrite (holds_f_ex R EM) in H. destruct H as [y H].
  rewrite (holds_f_and R EM) in H. cbn [FolHolds] in H.
  change (R y s /\ forall z, R z y -> ~R z s) in H. now exists y.
Qed.

Theorem zf_prefix_membership_irreflexive : forall a, ~R a a.
Proof.
  intros a Self. destruct (zf_prefix_singleton_exists R EM Model a) as [s S].
  assert (As : R a s) by (apply (proj2 (S a)); reflexivity).
  destruct (zf_prefix_foundation s ltac:(now exists a)) as [y [Y Min]].
  apply (proj1 (S y)) in Y. subst y. apply (Min a Self),As.
Qed.
End Foundation.

Print Assumptions zf_prefix_foundation.
Print Assumptions zf_prefix_membership_irreflexive.
