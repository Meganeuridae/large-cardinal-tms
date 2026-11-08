(** First-order definability of the atomic clauses of partial truth. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs
  BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxGuardedQuantifiers.
Import ListNotations.

Definition partial_atomic_builder (member:bool) s h g w m tag := b_ain g (fun p =>
  b_ain w (fun u => b_ain w (fun v => b_ain m (fun x => b_ain m (fun y =>
    atomic_core_builder member s h tag u v x y p))))).
Definition RelPartialAtomic {D} (R:D->D->Prop) (member:bool) s h g w m tag :=
  forall p u v x y, R p g -> R u w -> R v w -> R x m -> R y m ->
    RelGraph R s u x -> RelGraph R s v y -> RelNode2 R p tag u v ->
    (RelGraph R h p s <-> atom_truth R member x y).

Section PartialAtomicFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_atomic_builder_holds member rho s h g w m tag n :
  s<n -> h<n -> g<n -> w<n -> m<n -> tag<n ->
  (b_holds R rho (partial_atomic_builder member s h g w m tag) n <->
   RelPartialAtomic R member (rho s) (rho h) (rho g) (rho w) (rho m) (rho tag)).
Proof.
  intros S0 H0 G W M Tag. unfold partial_atomic_builder,RelPartialAtomic.
  rewrite b_holds_ain5 by lia. split.
  - intros H p u v x y Pg U V X Y G1 G2 Node.
    specialize (H p u v x y Pg U V X Y). rewrite (atomic_core_builder_holds EM) in H by lia.
    destruct (@push_environment_five D rho n p u v x y) as [Old [P0 [U0 [V0 [X0 Y0]]]]].
    rewrite (Old s S0),(Old h H0),(Old tag Tag),P0,U0,V0,X0,Y0 in H. now apply H.
  - intros H p u v x y Pg U V X Y. rewrite (atomic_core_builder_holds EM) by lia.
    destruct (@push_environment_five D rho n p u v x y) as [Old [P0 [U0 [V0 [X0 Y0]]]]].
    rewrite (Old s S0),(Old h H0),(Old tag Tag),P0,U0,V0,X0,Y0. intros [[G1 G2] Node].
    now apply H with (u:=u) (v:=v).
Qed.
End PartialAtomicFormula.

Print Assumptions partial_atomic_builder_holds.
