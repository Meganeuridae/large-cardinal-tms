(** A first-order-definable successor stage for finite pair closure. This is
    a local stage contract; it does not yet assert an internal omega-iteration
    or existence of a pair-closed bound. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxZFPowerset
  BerkeleySyntaxZFSeparation.
Import ListNotations.
Definition RelPairStage {D} (R:D->D->Prop) a b :=
  exists p q, RelPowerset R p a /\ RelPowerset R q p /\ RelBinaryUnion R b a q.
Definition b_powerset p a := b_all (fun z => b_iff (b_mem z p) (b_subset z a)).
Definition b_binary_union u a b := b_all (fun z => b_iff (b_mem z u) (b_or (b_mem z a) (b_mem z b))).
Definition b_pair_stage a b := b_ex (fun p => b_ex (fun q =>
  b_and3 (b_powerset p a) (b_powerset q p) (b_binary_union b a q))).
Definition pair_stage_formula := instantiate_formula (fun _=>0) (fst (b_pair_stage 3 2 4)).
Lemma pair_stage_formula_output_fresh : fol_free 1 pair_stage_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma good_subset a b : b_good (b_subset a b).
Proof. unfold b_subset. apply b_good_ain. intro z. apply b_good_mem. Qed.
Lemma good_powerset p a : b_good (b_powerset p a).
Proof.
  unfold b_powerset. apply b_good_all. intro z. unfold b_iff.
  apply b_good_binary; [apply b_good_mem|apply good_subset].
Qed.
Lemma good_binary_union u a b : b_good (b_binary_union u a b).
Proof.
  unfold b_binary_union. apply b_good_all. intro z. unfold b_iff,b_or.
  apply b_good_binary; [apply b_good_mem|apply b_good_binary; apply b_good_mem].
Qed.
Section Stages.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem powerset_builder_holds rho p a n : p<n -> a<n ->
  (b_holds R rho (b_powerset p a) n <-> RelPowerset R (rho p) (rho a)).
Proof.
  intros P A. unfold b_powerset,RelPowerset. rewrite b_holds_all. split; intros H z; specialize (H z).
  - rewrite (b_holds_iff EM),b_holds_mem in H. cbn [b_next b_mem] in H.
    replace (b_next (b_mem n p) (S n)) with (S n) in H by reflexivity.
    rewrite subset_builder_holds in H by lia. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite (b_holds_iff EM),b_holds_mem. cbn [b_next b_mem].
    replace (b_next (b_mem n p) (S n)) with (S n) by reflexivity.
    rewrite subset_builder_holds by lia. rewrite update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.
Theorem binary_union_builder_holds rho u a b n : u<n -> a<n -> b<n ->
  (b_holds R rho (b_binary_union u a b) n <-> RelBinaryUnion R (rho u) (rho a) (rho b)).
Proof.
  intros U A B. unfold b_binary_union,RelBinaryUnion. rewrite b_holds_all. split; intros H z; specialize (H z).
  - rewrite (b_holds_iff EM),b_holds_mem, (b_holds_or EM),!b_holds_mem in H.
    cbn [b_next b_mem] in H. rewrite !update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite (b_holds_iff EM),b_holds_mem, (b_holds_or EM),!b_holds_mem.
    cbn [b_next b_mem]. rewrite !update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
Lemma pair_stage_body_holds sigma a b p q n : a<n -> b<n -> p<n -> q<n ->
  (b_holds R sigma (b_and3 (b_powerset p a) (b_powerset q p) (b_binary_union b a q)) n <->
   RelPowerset R (sigma p) (sigma a) /\ RelPowerset R (sigma q) (sigma p) /\
   RelBinaryUnion R (sigma b) (sigma a) (sigma q)).
Proof.
  intros A B P Q. unfold b_and3. rewrite !b_holds_and by exact EM.
  assert (K1 : n<=b_next (b_powerset p a) n) by apply good_powerset.
  assert (K2 : b_next (b_powerset p a) n <=
    b_next (b_powerset q p) (b_next (b_powerset p a) n)) by apply good_powerset.
  rewrite powerset_builder_holds by lia. rewrite powerset_builder_holds by lia.
  replace (b_next (b_and (b_powerset p a) (b_powerset q p)) n)
    with (b_next (b_powerset q p) (b_next (b_powerset p a) n)) by reflexivity.
  rewrite binary_union_builder_holds by lia. tauto.
Qed.
Theorem pair_stage_builder_holds rho a b n : a<n -> b<n ->
  (b_holds R rho (b_pair_stage a b) n <-> RelPairStage R (rho a) (rho b)).
Proof.
  intros A B. unfold b_pair_stage,RelPairStage. rewrite (b_holds_ex EM). split.
  - intros [p H]. apply (proj1 (b_holds_ex EM _ _ _ _)) in H. destruct H as [q H].
    set (sigma:=update_variable (update_variable rho n p) (S n) q) in *.
    apply (proj1 (pair_stage_body_holds sigma a b n (S n) (S(S n)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) in H.
    assert (Sp:sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sq:sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    assert (Sa:sigma a=rho a) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sb:sigma b=rho b) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    rewrite Sp,Sq,Sa,Sb in H. now exists p,q.
  - intros [p [q [P [Q U]]]]. exists p. apply (proj2 (b_holds_ex EM _ _ _ _)). exists q.
    set (sigma:=update_variable (update_variable rho n p) (S n) q).
    change (b_holds R sigma (b_and3 (b_powerset n a) (b_powerset (S n) n) (b_binary_union b a (S n))) (S(S n))).
    apply (proj2 (pair_stage_body_holds sigma a b n (S n) (S(S n)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    assert (Sp:sigma n=p) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sq:sigma (S n)=q) by (unfold sigma; apply update_variable_eq).
    assert (Sa:sigma a=rho a) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sb:sigma b=rho b) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    now rewrite Sp,Sq,Sa,Sb.
Qed.
Theorem pair_stage_formula_holds rho : FolHolds R rho pair_stage_formula <-> RelPairStage R (rho 3) (rho 2).
Proof. change (b_holds R rho (b_pair_stage 3 2) 4 <-> RelPairStage R (rho 3) (rho 2)). apply pair_stage_builder_holds; lia. Qed.
Theorem zf_pair_stage_exists_unique a : exists b, RelPairStage R a b /\ forall c, RelPairStage R a c -> c=b.
Proof.
  destruct (zf_prefix_powerset_exists R EM Model a) as [p P].
  destruct (zf_prefix_powerset_exists R EM Model p) as [q Q].
  destruct (zf_prefix_binary_union_exists R EM Model a q) as [b B]. exists b. split; [now exists p,q|].
  intros c [p' [q' [P' [Q' C]]]].
  pose proof (zf_prefix_extensional R EM Model) as Ext.
  assert (p'=p) by (apply Ext; intro z; rewrite (P' z),(P z);tauto). subst p'.
  assert (q'=q) by (apply Ext; intro z; rewrite (Q' z),(Q z);tauto). subst q'.
  apply Ext. intro z. rewrite (C z),(B z). tauto.
Qed.
Theorem pair_stage_monotone a b : RelPairStage R a b -> RelSubset R a b.
Proof. intros [p [q [P [Q U]]]] x X. apply (proj2 (U x)). now left. Qed.
Theorem pair_stage_contains_pair a b x y r : RelPairStage R a b -> R x a -> R y a -> RelPair R r x y -> R r b.
Proof.
  intros [p [q [P [Q U]]]] X Y [s [t [S [T V]]]].
  apply (proj2 (U r)). right. apply (proj2 (Q r)). intros v Vv.
  apply (proj1 (V v)) in Vv. destruct Vv as [E|E]; subst v.
  - apply (proj2 (P s)). intros u Us. apply (proj1 (S u)) in Us. now subst u.
  - apply (proj2 (P t)). intros u Ut. apply (proj1 (T u)) in Ut. destruct Ut as [E|E]; now subst u.
Qed.
End Stages.
Print Assumptions pair_stage_formula_output_fresh.
Print Assumptions pair_stage_formula_holds.
Print Assumptions zf_pair_stage_exists_unique.
Print Assumptions pair_stage_monotone.
Print Assumptions pair_stage_contains_pair.
