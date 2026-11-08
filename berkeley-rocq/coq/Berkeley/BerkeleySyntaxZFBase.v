(** Semantic consequences of the actual finite ZF prefix. The model notion
    quantifies only over first-order formula instances of the listed schemas;
    it does not postulate separation or replacement for arbitrary predicates. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics
  BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs BerkeleySyntaxRepresentations.
Import ListNotations.

Definition satisfies_zf_prefix {D} (R:D->D->Prop) :=
  forall i f vars holes rho, 14 <= i < 23 -> nth_error candidate_axioms i=Some f ->
    FolHolds R rho (independent_instance vars holes f).

Section Axioms.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_extensional : RelExtensional R.
Proof.
  intros a b Same. set (rho := fun n => if Nat.eqb n 0 then a else b).
  pose proof (Model 14 (nth 14 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (b_holds R rho (b_imp (b_all (fun z => b_iff (b_mem z 0) (b_mem z 1))) (b_eq 0 1)) 2) in H.
  rewrite b_holds_imp,b_holds_eq in H. cbn [rho] in H. apply H. rewrite b_holds_all. intro z.
  rewrite (b_holds_iff EM),!b_holds_mem. cbn [b_next b_mem].
  rewrite !update_variable_eq. repeat rewrite update_variable_neq by lia. exact (Same z).
Qed.

Theorem zf_prefix_doubleton_exists : forall a b, exists p, RelDoubleton R p a b.
Proof.
  intros a b. set (rho := fun n => if Nat.eqb n 0 then a else b).
  pose proof (Model 16 (nth 16 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (b_holds R rho (b_ex (fun p => b_doubleton p 0 1)) 2) in H.
  rewrite (b_holds_ex EM) in H. destruct H as [p H].
  rewrite (doubleton_builder_holds EM) in H by lia.
  rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia.
  exists p. exact H.
Qed.

Theorem zf_prefix_singleton_exists : forall a, exists p, RelSingleton R p a.
Proof.
  intro a. destruct (zf_prefix_doubleton_exists a a) as [p P]. exists p. intro z. specialize (P z). tauto.
Qed.

Theorem zf_prefix_kuratowski_pair_exists : forall a b, exists p, RelPair R p a b.
Proof.
  intros a b. destruct (zf_prefix_singleton_exists a) as [u U].
  destruct (zf_prefix_doubleton_exists a b) as [v V].
  destruct (zf_prefix_doubleton_exists u v) as [p P]. exists p,u,v. tauto.
Qed.
End Axioms.

Print Assumptions zf_prefix_extensional.
Print Assumptions zf_prefix_doubleton_exists.
Print Assumptions zf_prefix_kuratowski_pair_exists.
