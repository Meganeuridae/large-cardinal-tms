(** First-order definability of the logical clauses of partial truth. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs BerkeleySyntaxEnvironment
  BerkeleySyntaxSatisfactionLogical BerkeleySyntaxSatisfactionAll BerkeleySyntaxGuardedQuantifiers.
Import ListNotations.

Definition partial_neg_builder s h g f tag := b_ain g (fun r => b_ain f (fun p => neg_core_builder s h tag p r)).
Definition partial_imp_builder s h g f tag := b_ain g (fun r => b_ain f (fun p => b_ain f (fun q => imp_core_builder s h tag p q r))).
Definition partial_all_builder s h g e f w m tag := b_ain g (fun r => b_ain w (fun u => b_ain f (fun p => all_core_builder s h e w m tag u p r))).
Definition RelPartialNeg {D} (R:D->D->Prop) s h g f tag := forall r p, R r g -> R p f -> RelPair R r tag p ->
  (RelGraph R h r s <-> ~RelGraph R h p s).
Definition RelPartialImp {D} (R:D->D->Prop) s h g f tag := forall r p q, R r g -> R p f -> R q f -> RelNode2 R r tag p q ->
  (RelGraph R h r s <-> (RelGraph R h p s -> RelGraph R h q s)).
Definition RelPartialAll {D} (R:D->D->Prop) s h g e f w m tag := forall r u p, R r g -> R u w -> R p f -> RelNode2 R r tag u p ->
  (RelGraph R h r s <-> forall t, R t e -> RelUpdate R s t u w m -> RelGraph R h p t).

Section PartialLogicalFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_neg_builder_holds rho s h g f tag n : s<n -> h<n -> g<n -> f<n -> tag<n ->
  (b_holds R rho (partial_neg_builder s h g f tag) n <-> RelPartialNeg R (rho s) (rho h) (rho g) (rho f) (rho tag)).
Proof.
  intros S0 H G F Tag. unfold partial_neg_builder,RelPartialNeg. rewrite b_holds_ain2 by lia. split.
  - intros B r p Rg Pf Pair. specialize (B r p Rg Pf). rewrite (neg_core_builder_holds EM) in B by lia.
    destruct (@push_environment_two D rho n r p) as [Old [R0 P0]].
    rewrite (Old s S0),(Old h H),(Old tag Tag),R0,P0 in B. now apply B.
  - intros B r p Rg Pf. rewrite (neg_core_builder_holds EM) by lia.
    destruct (@push_environment_two D rho n r p) as [Old [R0 P0]].
    rewrite (Old s S0),(Old h H),(Old tag Tag),R0,P0. now apply B.
Qed.

Lemma partial_imp_builder_holds rho s h g f tag n : s<n -> h<n -> g<n -> f<n -> tag<n ->
  (b_holds R rho (partial_imp_builder s h g f tag) n <-> RelPartialImp R (rho s) (rho h) (rho g) (rho f) (rho tag)).
Proof.
  intros S0 H G F Tag. unfold partial_imp_builder,RelPartialImp. rewrite b_holds_ain3 by lia. split.
  - intros B r p q Rg Pf Qf Node. specialize (B r p q Rg Pf Qf). rewrite (imp_core_builder_holds EM) in B by lia.
    destruct (@push_environment_three D rho n r p q) as [Old [R0 [P0 Q0]]].
    rewrite (Old s S0),(Old h H),(Old tag Tag),R0,P0,Q0 in B. now apply B.
  - intros B r p q Rg Pf Qf. rewrite (imp_core_builder_holds EM) by lia.
    destruct (@push_environment_three D rho n r p q) as [Old [R0 [P0 Q0]]].
    rewrite (Old s S0),(Old h H),(Old tag Tag),R0,P0,Q0. now apply B.
Qed.

Lemma partial_all_builder_holds rho s h g e f w m tag n :
  s<n -> h<n -> g<n -> e<n -> f<n -> w<n -> m<n -> tag<n ->
  (b_holds R rho (partial_all_builder s h g e f w m tag) n <->
   RelPartialAll R (rho s) (rho h) (rho g) (rho e) (rho f) (rho w) (rho m) (rho tag)).
Proof.
  intros S0 H G E F W M Tag. unfold partial_all_builder,RelPartialAll. rewrite b_holds_ain3 by lia. split.
  - intros B r u p Rg Uw Pf Node. specialize (B r u p Rg Uw Pf). rewrite (all_core_builder_holds EM) in B by lia.
    destruct (@push_environment_three D rho n r u p) as [Old [R0 [U0 P0]]].
    rewrite (Old s S0),(Old h H),(Old e E),(Old w W),(Old m M),(Old tag Tag),R0,U0,P0 in B. now apply B.
  - intros B r u p Rg Uw Pf. rewrite (all_core_builder_holds EM) by lia.
    destruct (@push_environment_three D rho n r u p) as [Old [R0 [U0 P0]]].
    rewrite (Old s S0),(Old h H),(Old e E),(Old w W),(Old m M),(Old tag Tag),R0,U0,P0. now apply B.
Qed.
End PartialLogicalFormula.

Print Assumptions partial_neg_builder_holds.
Print Assumptions partial_imp_builder_holds.
Print Assumptions partial_all_builder_holds.
