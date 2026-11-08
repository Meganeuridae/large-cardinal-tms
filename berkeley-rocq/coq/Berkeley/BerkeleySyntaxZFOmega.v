(** Internal omega and first-order induction, derived from the literal
    Infinity and Separation schemas. No external standardness is assumed. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation
  FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxRepresentations
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation.
Import ListNotations.

Definition omega_intersection_builder := b_all (fun g => b_imp (b_inductive g) (b_mem 2 g)).
Definition omega_intersection_formula := instantiate_formula (fun _=>0)
  (fst (omega_intersection_builder 3)).
Lemma omega_intersection_fresh : fol_free 1 omega_intersection_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section InternalOmega.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma zf_empty_unique a b : RelEmpty R a -> RelEmpty R b -> a=b.
Proof. intros A B. apply (zf_prefix_extensional R EM Model). intro z. specialize (A z). specialize (B z). tauto. Qed.
Lemma zf_successor_unique a b x : RelSuccessor R a x -> RelSuccessor R b x -> a=b.
Proof. intros A B. apply (zf_prefix_extensional R EM Model). intro z. rewrite (A z),(B z). reflexivity. Qed.

Theorem zf_prefix_inductive_exists (seed:D) : exists a, RelInductive R a.
Proof.
  set (rho := fun _ : nat => seed).
  pose proof (Model 19 (nth 19 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (FolHolds R rho (f_ex 0 (f_and
    (f_ex 1 (f_and (FMember 1 0) (FAll 2 (FNeg (FMember 2 1)))))
    (FAll 1 (FImp (FMember 1 0) (f_ex 2 (f_and (FMember 2 0)
      (FAll 3 (f_iff (FMember 3 2) (FImp (FNeg (FMember 3 1)) (FEqual 3 1))))))))))) in H.
  rewrite (holds_f_ex R EM) in H. destruct H as [a H].
  rewrite (holds_f_and R EM) in H. destruct H as [Zero Succ].
  exists a. split.
  - rewrite (holds_f_ex R EM) in Zero. destruct Zero as [e Zero].
    rewrite (holds_f_and R EM) in Zero. change (R e a /\ forall z, ~R z e) in Zero.
    now exists e.
  - intros x X. change (forall x, R x a -> FolHolds R (update_variable (update_variable rho 0 a) 1 x)
      (f_ex 2 (f_and (FMember 2 0)
        (FAll 3 (f_iff (FMember 3 2) (FImp (FNeg (FMember 3 1)) (FEqual 3 1))))))) in Succ.
    specialize (Succ x X). rewrite (holds_f_ex R EM) in Succ. destruct Succ as [y Succ].
    rewrite (holds_f_and R EM) in Succ. destruct Succ as [Y S]. exists y. split; [exact Y|].
    intro z. specialize (S z). rewrite (holds_f_iff R EM) in S.
    change (R z y <-> (~ R z x -> z=x)) in S.
    destruct (EM (R z x)); tauto.
Qed.

Lemma omega_intersection_holds rho : FolHolds R rho omega_intersection_formula <->
  forall g, RelInductive R g -> R (rho 2) g.
Proof.
  change (FolHolds R rho omega_intersection_formula) with (b_holds R rho omega_intersection_builder 3).
  unfold omega_intersection_builder. rewrite b_holds_all.
  setoid_rewrite b_holds_imp.
  setoid_rewrite (inductive_builder_holds EM D R) at 1.
  all: try lia.
  setoid_rewrite b_holds_mem. cbv [update_variable Nat.eqb]. reflexivity.
Qed.

Theorem zf_prefix_omega_exists (seed:D) : exists w, RelOmega R w.
Proof.
  destruct (zf_prefix_inductive_exists seed) as [a Ind].
  destruct (zf_prefix_formula_separation R EM Model omega_intersection_formula (fun _=>a)
    omega_intersection_fresh) as [w W].
  assert (Spec : forall z, R z w <-> R z a /\ forall g, RelInductive R g -> R z g).
  { intro z. specialize (W z). rewrite omega_intersection_holds in W.
    cbv [update_variable Nat.eqb] in W. exact W. }
  assert (Sub : forall g, RelInductive R g -> RelSubset R w g).
  { intros g G z Z. exact (proj2 (proj1 (Spec z) Z) g G). }
  destruct Ind as [[e [E Empty]] Succ]. exists w. split; [split|exact Sub].
  - exists e. split; [|exact Empty]. apply (proj2 (Spec e)). split; [exact E|].
    intros g [[e' [E' Empty']] _].
    assert (e=e') by (now apply zf_empty_unique). now subst e'.
  - intros x X. destruct (Succ x (proj1 (proj1 (Spec x) X))) as [y [Y Sy]].
    exists y. split; [|exact Sy]. apply (proj2 (Spec y)). split; [exact Y|].
    intros g G. pose proof (Sub g G x X) as GX. destruct G as [_ GS].
    destruct (GS x GX) as [y' [Y' Sy']].
    assert (y=y') by (eapply zf_successor_unique; eassumption). now subst y'.
Qed.

Theorem zf_prefix_omega_unique a b : RelOmega R a -> RelOmega R b -> a=b.
Proof.
  intros [A MA] [B MB]. apply (zf_prefix_extensional R EM Model). intro z.
  split; [apply MA|apply MB]; assumption.
Qed.

Theorem zf_internal_omega_induction w p rho :
  RelOmega R w -> fol_free 1 p=false -> rho 0=w ->
  (forall e, RelEmpty R e -> FolHolds R (update_variable rho 2 e) p) ->
  (forall x y, R x w -> RelSuccessor R y x ->
    FolHolds R (update_variable rho 2 x) p -> FolHolds R (update_variable rho 2 y) p) ->
  forall x, R x w -> FolHolds R (update_variable rho 2 x) p.
Proof.
  intros [[Zero Succ] Least] Fresh At Base Step.
  destruct (zf_prefix_formula_separation R EM Model p rho Fresh) as [good G].
  rewrite At in G.
  assert (Ind : RelInductive R good).
  { split.
    - destruct Zero as [e [E Empty]]. exists e. split; [|exact Empty].
      apply (proj2 (G e)). split; [exact E|now apply Base].
    - intros x X. destruct (proj1 (G x) X) as [WX PX].
      destruct (Succ x WX) as [y [WY Sy]]. exists y. split; [|exact Sy].
      apply (proj2 (G y)). split; [exact WY|exact (Step x y WX Sy PX)]. }
  intros x X. exact (proj2 (proj1 (G x) (Least good Ind x X))).
Qed.
End InternalOmega.

Print Assumptions zf_prefix_inductive_exists.
Print Assumptions zf_prefix_omega_exists.
Print Assumptions zf_prefix_omega_unique.
Print Assumptions zf_internal_omega_induction.
