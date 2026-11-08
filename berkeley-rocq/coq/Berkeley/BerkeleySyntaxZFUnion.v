(** Union and binary union from the actual first-order ZF prefix. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxInterpretation BerkeleySyntaxPairs BerkeleySyntaxZFBase.

Definition RelUnion {D} (R:D->D->Prop) u a := forall z, R z u <-> exists t, R t a /\ R z t.
Definition RelBinaryUnion {D} (R:D->D->Prop) u a b := forall z, R z u <-> R z a \/ R z b.

Section Union.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_union_exists : forall a, exists u, RelUnion R u a.
Proof.
  intro a. set (rho := fun _ : nat => a).
  pose proof (Model 17 (nth 17 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (b_holds R rho (b_ex (fun u => b_all (fun z => b_iff (b_mem z u)
    (b_ein 0 (fun t => b_mem z t))))) 1) in H.
  rewrite (b_holds_ex EM) in H. destruct H as [u H]. exists u. intro z.
  rewrite b_holds_all in H. specialize (H z). rewrite (b_holds_iff EM),b_holds_mem in H.
  replace (b_next (b_mem 2 1) 3) with 3 in H by reflexivity.
  rewrite (b_holds_ein EM) in H by lia. cbn [rho] in H.
  rewrite !update_variable_eq in H. repeat rewrite update_variable_neq in H by lia.
  setoid_rewrite b_holds_mem in H.
  split.
  - intros A. destruct (proj1 H A) as [t [T Z]]. exists t. split; [exact T|].
    rewrite update_variable_eq in Z. rewrite update_variable_neq in Z by lia. exact Z.
  - intros [t [T Z]]. apply (proj2 H). exists t. split; [exact T|].
    rewrite update_variable_eq,update_variable_neq by lia. exact Z.
Qed.
Theorem zf_prefix_binary_union_exists : forall a b, exists u, RelBinaryUnion R u a b.
Proof.
  intros a b. destruct (zf_prefix_doubleton_exists R EM Model a b) as [p P].
  destruct (zf_prefix_union_exists p) as [u U]. exists u. intro z. rewrite (U z). split.
  - intros [t [T Z]]. apply (proj1 (P t)) in T. destruct T as [T|T]; subst; auto.
  - intros [Z|Z]; [exists a|exists b]; split; auto; apply (proj2 (P _)); auto.
Qed.
End Union.

Print Assumptions zf_prefix_union_exists.
Print Assumptions zf_prefix_binary_union_exists.
