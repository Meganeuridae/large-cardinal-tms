(** First-order builders for downward closure and truth-graph support. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxPairs BerkeleySyntaxFunction
  BerkeleySyntaxFormulaSet BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion BerkeleySyntaxGuardedQuantifiers.
Import ListNotations.

Definition down_neg_core p q g tn := b_imp (b_pair p tn q) (b_mem q g).
Definition down_imp_core p q r g ti := b_imp (b_node2 p ti q r) (b_and (b_mem q g) (b_mem r g)).
Definition down_all_core p x q g ta := b_imp (b_node2 p ta x q) (b_mem q g).
Definition down_neg_builder g f tn := b_ain g (fun p=>b_ain f (fun q=>down_neg_core p q g tn)).
Definition down_imp_builder g f ti := b_ain g (fun p=>b_ain f (fun q=>b_ain f (fun r=>down_imp_core p q r g ti))).
Definition down_all_builder g f ta := b_ain g (fun p=>b_all (fun x=>b_ain f (fun q=>down_all_core p x q g ta))).
Definition partial_down_builder g f tn ti ta := b_and3 (down_neg_builder g f tn) (down_imp_builder g f ti) (down_all_builder g f ta).
Definition graph_bound_core h g e p s := b_imp (b_rel h p s) (b_and (b_mem p g) (b_mem s e)).
Definition graph_bound_builder h g e := b_all (fun p=>b_all (fun s=>graph_bound_core h g e p s)).

Lemma b_good_down_neg_core p q g tn : b_good (down_neg_core p q g tn).
Proof. unfold down_neg_core,b_imp. apply b_good_binary; [apply b_good_pair|apply b_good_mem]. Qed.
Lemma b_good_down_imp_core p q r g ti : b_good (down_imp_core p q r g ti).
Proof. unfold down_imp_core,b_imp. apply b_good_binary; [apply b_good_node2|apply b_good_and; apply b_good_mem]. Qed.
Lemma b_good_down_all_core p x q g ta : b_good (down_all_core p x q g ta).
Proof. unfold down_all_core,b_imp. apply b_good_binary; [apply b_good_node2|apply b_good_mem]. Qed.
Lemma b_good_down_neg g f tn : b_good (down_neg_builder g f tn).
Proof. unfold down_neg_builder. apply b_good_ain. intro p. apply b_good_ain. intro q. apply b_good_down_neg_core. Qed.
Lemma b_good_down_imp g f ti : b_good (down_imp_builder g f ti).
Proof. unfold down_imp_builder. apply b_good_ain. intro p. apply b_good_ain. intro q. apply b_good_ain. intro r. apply b_good_down_imp_core. Qed.
Lemma b_good_down_all g f ta : b_good (down_all_builder g f ta).
Proof. unfold down_all_builder. apply b_good_ain. intro p. apply b_good_all. intro x. apply b_good_ain. intro q. apply b_good_down_all_core. Qed.
Lemma b_good_partial_down g f tn ti ta : b_good (partial_down_builder g f tn ti ta).
Proof.
  unfold partial_down_builder,b_and3. apply b_good_and; [apply b_good_and; [apply b_good_down_neg|apply b_good_down_imp]|apply b_good_down_all].
Qed.
Lemma b_good_graph_bound h g e : b_good (graph_bound_builder h g e).
Proof.
  unfold graph_bound_builder. apply b_good_all. intro p. apply b_good_all. intro s. unfold graph_bound_core,b_imp.
  apply b_good_binary; [apply b_good_rel|apply b_good_and; apply b_good_mem].
Qed.

Section PartialDownFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma down_neg_core_holds rho p q g tn n : p<n -> q<n -> g<n -> tn<n ->
  (b_holds R rho (down_neg_core p q g tn) n <-> (RelPair R (rho p) (rho tn) (rho q) -> R (rho q) (rho g))).
Proof.
  intros P Q G T. unfold down_neg_core. rewrite b_holds_imp.
  assert (K : n <= b_next (b_pair p tn q) n) by apply b_good_pair.
  rewrite (pair_builder_holds EM),b_holds_mem by lia. reflexivity.
Qed.
Lemma down_imp_core_holds rho p q r g ti n : p<n -> q<n -> r<n -> g<n -> ti<n ->
  (b_holds R rho (down_imp_core p q r g ti) n <->
   (RelNode2 R (rho p) (rho ti) (rho q) (rho r) -> R (rho q) (rho g) /\ R (rho r) (rho g))).
Proof.
  intros P Q R0 G T. unfold down_imp_core. rewrite b_holds_imp,(b_holds_and EM),!b_holds_mem.
  assert (K : n <= b_next (b_node2 p ti q r) n) by apply b_good_node2.
  rewrite (node2_builder_holds EM) by lia. reflexivity.
Qed.
Lemma down_all_core_holds rho p x q g ta n : p<n -> x<n -> q<n -> g<n -> ta<n ->
  (b_holds R rho (down_all_core p x q g ta) n <-> (RelNode2 R (rho p) (rho ta) (rho x) (rho q) -> R (rho q) (rho g))).
Proof.
  intros P X Q G T. unfold down_all_core. rewrite b_holds_imp.
  assert (K : n <= b_next (b_node2 p ta x q) n) by apply b_good_node2.
  rewrite (node2_builder_holds EM),b_holds_mem by lia. reflexivity.
Qed.

Lemma down_neg_builder_holds rho g f tn n : g<n -> f<n -> tn<n ->
  (b_holds R rho (down_neg_builder g f tn) n <->
    forall p q, R p (rho g) -> R q (rho f) -> RelPair R p (rho tn) q -> R q (rho g)).
Proof.
  intros G F T. unfold down_neg_builder. rewrite b_holds_ain2 by lia. split.
  - intros H p q P Q Pair. specialize (H p q P Q). rewrite down_neg_core_holds in H by lia.
    destruct (@push_environment_two D rho n p q) as [Old [P0 Q0]].
    rewrite (Old g G),(Old tn T),P0,Q0 in H. now apply H.
  - intros H p q P Q. rewrite down_neg_core_holds by lia.
    destruct (@push_environment_two D rho n p q) as [Old [P0 Q0]].
    rewrite (Old g G),(Old tn T),P0,Q0. now apply H.
Qed.
Lemma down_imp_builder_holds rho g f ti n : g<n -> f<n -> ti<n ->
  (b_holds R rho (down_imp_builder g f ti) n <-> forall p q r,
    R p (rho g) -> R q (rho f) -> R r (rho f) -> RelNode2 R p (rho ti) q r -> R q (rho g) /\ R r (rho g)).
Proof.
  intros G F T. unfold down_imp_builder. rewrite b_holds_ain3 by lia. split.
  - intros H p q r P Q R0 Node. specialize (H p q r P Q R0). rewrite down_imp_core_holds in H by lia.
    destruct (@push_environment_three D rho n p q r) as [Old [P0 [Q0 R1]]].
    rewrite (Old g G),(Old ti T),P0,Q0,R1 in H. now apply H.
  - intros H p q r P Q R0. rewrite down_imp_core_holds by lia.
    destruct (@push_environment_three D rho n p q r) as [Old [P0 [Q0 R1]]].
    rewrite (Old g G),(Old ti T),P0,Q0,R1. now apply H.
Qed.
Lemma down_all_builder_holds rho g f ta n : g<n -> f<n -> ta<n ->
  (b_holds R rho (down_all_builder g f ta) n <-> forall p x q,
    R p (rho g) -> R q (rho f) -> RelNode2 R p (rho ta) x q -> R q (rho g)).
Proof.
  intros G F T. unfold down_all_builder. rewrite b_holds_ain_all_ain3 by lia. split.
  - intros H p x q P Q Node. specialize (H p x q P Q). rewrite down_all_core_holds in H by lia.
    destruct (@push_environment_three D rho n p x q) as [Old [P0 [X0 Q0]]].
    rewrite (Old g G),(Old ta T),P0,X0,Q0 in H. now apply H.
  - intros H p x q P Q. rewrite down_all_core_holds by lia.
    destruct (@push_environment_three D rho n p x q) as [Old [P0 [X0 Q0]]].
    rewrite (Old g G),(Old ta T),P0,X0,Q0. now apply H.
Qed.
Theorem partial_down_builder_holds rho g f tn ti ta n : g<n -> f<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_down_builder g f tn ti ta) n <-> RelPartialDownward R (rho g) (rho f) (rho tn) (rho ti) (rho ta)).
Proof.
  intros G F N I A. unfold partial_down_builder,RelPartialDownward,b_and3. rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (down_neg_builder g f tn) n) by apply b_good_down_neg.
  assert (K2 : n <= b_next (b_and (down_neg_builder g f tn) (down_imp_builder g f ti)) n)
    by (apply b_good_and; [apply b_good_down_neg|apply b_good_down_imp]).
  rewrite down_neg_builder_holds,down_imp_builder_holds,down_all_builder_holds by lia. tauto.
Qed.

Lemma graph_bound_core_holds rho h g e p s n : h<n -> g<n -> e<n -> p<n -> s<n ->
  (b_holds R rho (graph_bound_core h g e p s) n <-> (RelGraph R (rho h) (rho p) (rho s) -> R (rho p) (rho g) /\ R (rho s) (rho e))).
Proof.
  intros H G E P S0. unfold graph_bound_core. rewrite b_holds_imp,(b_holds_and EM),!b_holds_mem.
  assert (K : n <= b_next (b_rel h p s) n) by apply b_good_rel. rewrite (relation_builder_holds EM) by lia. reflexivity.
Qed.
Theorem graph_bound_builder_holds rho h g e n : h<n -> g<n -> e<n ->
  (b_holds R rho (graph_bound_builder h g e) n <-> RelTruthGraphBound R (rho h) (rho g) (rho e)).
Proof.
  intros H G E. unfold graph_bound_builder,RelTruthGraphBound. rewrite b_holds_all2. split.
  - intros B p s Pair. specialize (B p s). rewrite graph_bound_core_holds in B by lia.
    destruct (@push_environment_two D rho n p s) as [Old [P0 S0]].
    rewrite (Old h H),(Old g G),(Old e E),P0,S0 in B. now apply B.
  - intros B p s. rewrite graph_bound_core_holds by lia.
    destruct (@push_environment_two D rho n p s) as [Old [P0 S0]].
    rewrite (Old h H),(Old g G),(Old e E),P0,S0. now apply B.
Qed.
End PartialDownFormula.

Print Assumptions partial_down_builder_holds.
Print Assumptions graph_bound_builder_holds.
