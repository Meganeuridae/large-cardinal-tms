(** First-order builder for the complete restricted Tarski recursion. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxFormulaSet
  BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxSatisfactionLogical BerkeleySyntaxSatisfactionAll
  BerkeleySyntaxPartialTruth BerkeleySyntaxPartialAtomicFormula BerkeleySyntaxPartialLogicalFormula.
Import ListNotations.

Definition partial_truth_clauses_builder s h g e f w m te tm tn ti ta := b_and5
  (partial_atomic_builder false s h g w m te) (partial_atomic_builder true s h g w m tm)
  (partial_neg_builder s h g f tn) (partial_imp_builder s h g f ti) (partial_all_builder s h g e f w m ta).
Definition partial_truth_builder h g e f w m te tm tn ti ta :=
  b_ain e (fun s => partial_truth_clauses_builder s h g e f w m te tm tn ti ta).
Definition RelPartialTruthClauses {D} (R:D->D->Prop) s h g e f w m te tm tn ti ta :=
  RelPartialAtomic R false s h g w m te /\ RelPartialAtomic R true s h g w m tm /\
  RelPartialNeg R s h g f tn /\ RelPartialImp R s h g f ti /\ RelPartialAll R s h g e f w m ta.

Lemma b_good_partial_atomic member s h g w m tag : b_good (partial_atomic_builder member s h g w m tag).
Proof.
  unfold partial_atomic_builder. apply b_good_ain. intro p. apply b_good_ain. intro u. apply b_good_ain. intro v.
  apply b_good_ain. intro x. apply b_good_ain. intro y. apply b_good_atomic_core.
Qed.
Lemma b_good_partial_neg s h g f tag : b_good (partial_neg_builder s h g f tag).
Proof. unfold partial_neg_builder. apply b_good_ain. intro r. apply b_good_ain. intro p. apply b_good_neg_core. Qed.
Lemma b_good_partial_imp s h g f tag : b_good (partial_imp_builder s h g f tag).
Proof.
  unfold partial_imp_builder. apply b_good_ain. intro r. apply b_good_ain. intro p. apply b_good_ain. intro q. apply b_good_imp_core.
Qed.
Lemma b_good_partial_all s h g e f w m tag : b_good (partial_all_builder s h g e f w m tag).
Proof.
  unfold partial_all_builder. apply b_good_ain. intro r. apply b_good_ain. intro u. apply b_good_ain. intro p. apply b_good_all_core.
Qed.
Lemma b_good_partial_truth_clauses s h g e f w m te tm tn ti ta :
  b_good (partial_truth_clauses_builder s h g e f w m te tm tn ti ta).
Proof.
  unfold partial_truth_clauses_builder,b_and5,b_and4,b_and3.
  apply b_good_and; [|apply b_good_partial_all]. apply b_good_and; [|apply b_good_partial_imp].
  apply b_good_and; [|apply b_good_partial_neg]. apply b_good_and; apply b_good_partial_atomic.
Qed.
Lemma b_good_partial_truth h g e f w m te tm tn ti ta : b_good (partial_truth_builder h g e f w m te tm tn ti ta).
Proof. unfold partial_truth_builder. apply b_good_ain. intro s. apply b_good_partial_truth_clauses. Qed.

Lemma partial_clauses_reorder {D} (R:D->D->Prop) s h g e f w m te tm tn ti ta :
  RelPartialTruthClauses R s h g e f w m te tm tn ti ta <->
  (forall u v x y p, R p g -> R u w -> R v w -> R x m -> R y m ->
    BerkeleySyntaxPairs.RelGraph R s u x -> BerkeleySyntaxPairs.RelGraph R s v y -> BerkeleySyntaxPairs.RelNode2 R p te u v ->
    (BerkeleySyntaxPairs.RelGraph R h p s <-> x=y)) /\
  (forall u v x y p, R p g -> R u w -> R v w -> R x m -> R y m ->
    BerkeleySyntaxPairs.RelGraph R s u x -> BerkeleySyntaxPairs.RelGraph R s v y -> BerkeleySyntaxPairs.RelNode2 R p tm u v ->
    (BerkeleySyntaxPairs.RelGraph R h p s <-> R x y)) /\
  (forall p q, R q g -> R p f -> BerkeleySyntaxPairs.RelPair R q tn p ->
    (BerkeleySyntaxPairs.RelGraph R h q s <-> ~BerkeleySyntaxPairs.RelGraph R h p s)) /\
  (forall p q r, R r g -> R p f -> R q f -> BerkeleySyntaxPairs.RelNode2 R r ti p q ->
    (BerkeleySyntaxPairs.RelGraph R h r s <-> (BerkeleySyntaxPairs.RelGraph R h p s -> BerkeleySyntaxPairs.RelGraph R h q s))) /\
  (forall u p q, R q g -> R u w -> R p f -> BerkeleySyntaxPairs.RelNode2 R q ta u p ->
    (BerkeleySyntaxPairs.RelGraph R h q s <-> forall t, R t e -> BerkeleySyntaxEnvironment.RelUpdate R s t u w m -> BerkeleySyntaxPairs.RelGraph R h p t)).
Proof.
  unfold RelPartialTruthClauses,RelPartialAtomic,RelPartialNeg,RelPartialImp,RelPartialAll. cbn [atom_truth].
  split; intros [E [M [N [I A]]]].
  - split; [intros u v x y p Pg U V X Y Gu Gv Node; exact (E p u v x y Pg U V X Y Gu Gv Node)|].
    split; [intros u v x y p Pg U V X Y Gu Gv Node; exact (M p u v x y Pg U V X Y Gu Gv Node)|].
    split; [intros p q Q P Pair; exact (N q p Q P Pair)|].
    split; [intros p q r R0 P Q Node; exact (I r p q R0 P Q Node)|].
    intros u p q Q U P Node. exact (A q u p Q U P Node).
  - split; [intros p u v x y Pg U V X Y Gu Gv Node; exact (E u v x y p Pg U V X Y Gu Gv Node)|].
    split; [intros p u v x y Pg U V X Y Gu Gv Node; exact (M u v x y p Pg U V X Y Gu Gv Node)|].
    split; [intros q p Q P Pair; exact (N p q Q P Pair)|].
    split; [intros r p q R0 P Q Node; exact (I p q r R0 P Q Node)|].
    intros q u p Q U P Node. exact (A u p q Q U P Node).
Qed.

Section PartialTruthFormula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.

Lemma partial_truth_clauses_builder_holds rho s h g e f w m te tm tn ti ta n :
  s<n -> h<n -> g<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_truth_clauses_builder s h g e f w m te tm tn ti ta) n <->
   RelPartialTruthClauses R (rho s) (rho h) (rho g) (rho e) (rho f) (rho w) (rho m)
     (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros S0 H G E F W M Te Tm Tn Ti Ta. unfold partial_truth_clauses_builder,RelPartialTruthClauses,b_and5,b_and4,b_and3.
  rewrite !(b_holds_and EM).
  assert (K1 : n <= b_next (partial_atomic_builder false s h g w m te) n) by apply b_good_partial_atomic.
  assert (K2 : n <= b_next (b_and (partial_atomic_builder false s h g w m te) (partial_atomic_builder true s h g w m tm)) n)
    by (apply b_good_and; apply b_good_partial_atomic).
  assert (K3 : n <= b_next (b_and (b_and (partial_atomic_builder false s h g w m te)
    (partial_atomic_builder true s h g w m tm)) (partial_neg_builder s h g f tn)) n)
    by (apply b_good_and; [apply b_good_and; apply b_good_partial_atomic|apply b_good_partial_neg]).
  assert (K4 : n <= b_next (b_and (b_and (b_and (partial_atomic_builder false s h g w m te)
    (partial_atomic_builder true s h g w m tm)) (partial_neg_builder s h g f tn)) (partial_imp_builder s h g f ti)) n)
    by (apply b_good_and; [apply b_good_and; [apply b_good_and; apply b_good_partial_atomic|apply b_good_partial_neg]|apply b_good_partial_imp]).
  rewrite !(@partial_atomic_builder_holds D R EM),(@partial_neg_builder_holds D R EM),(@partial_imp_builder_holds D R EM),(@partial_all_builder_holds D R EM) by lia. tauto.
Qed.

Theorem partial_truth_builder_holds rho h g e f w m te tm tn ti ta n :
  h<n -> g<n -> e<n -> f<n -> w<n -> m<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (partial_truth_builder h g e f w m te tm tn ti ta) n <->
   RelPartialTruth R (rho h) (rho g) (rho e) (rho f) (rho w) (rho m) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros H G E F W M Te Tm Tn Ti Ta. unfold partial_truth_builder,RelPartialTruth. rewrite b_holds_ain by exact E.
  split; intros B s S; specialize (B s S).
  - rewrite partial_truth_clauses_builder_holds in B by lia.
    rewrite update_variable_eq in B. repeat rewrite update_variable_neq in B by lia.
    now apply partial_clauses_reorder.
  - rewrite partial_truth_clauses_builder_holds by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia.
    now apply partial_clauses_reorder.
Qed.
End PartialTruthFormula.

Print Assumptions partial_clauses_reorder.
Print Assumptions partial_truth_builder_holds.
