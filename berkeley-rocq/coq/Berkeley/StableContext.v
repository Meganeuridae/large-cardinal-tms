(** Contextual deduction for injective-renaming-stable formulas. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import ProofFormula ProofPresentation LogicBridge TheoryIrreflexiveND StableLogic.
Import ListNotations.

Inductive StableContext (ctx : list fol_formula) : fol_formula -> Prop :=
| sc_hyp p : In p ctx -> StableContext ctx p
| sc_theorem p : RenameStable p -> StableContext ctx p
| sc_mp p q : StableContext ctx (FImp p q) -> StableContext ctx p -> StableContext ctx q.

Lemma sc_weaken Γ Δ p : (forall q, In q Γ -> In q Δ) -> StableContext Γ p -> StableContext Δ p.
Proof. intros Inc H. induction H; [apply sc_hyp,Inc;assumption|apply sc_theorem;assumption|eapply sc_mp; eassumption]. Qed.

Lemma sc_logical Γ p : LogicalProvable p -> StableContext Γ p.
Proof. intro H. apply sc_theorem,stable_logical,H. Qed.

Theorem sc_deduction Γ p q : StableContext (p::Γ) q -> StableContext Γ (FImp p q).
Proof.
  intro H. remember (p::Γ) as ctx eqn:E. induction H as [f Member|f Global|a b Major IHm Minor IHn]; subst ctx.
  - cbn in Member. destruct Member as [Eq|Member].
    + subst f. apply sc_logical,logical_identity.
    + eapply sc_mp; [apply sc_logical,logical_b1|now apply sc_hyp].
  - eapply sc_mp; [apply sc_logical,logical_b1|now apply sc_theorem].
  - eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_b2|apply IHm; reflexivity]|apply IHn; reflexivity].
Qed.

Lemma sc_finish p : StableContext [] p -> RenameStable p.
Proof. intro H. induction H; [contradiction|assumption|eapply stable_mp; eassumption]. Qed.

Lemma sc_true Γ : StableContext Γ nd_true.
Proof. unfold nd_true. apply sc_logical,logical_identity. Qed.
Lemma sc_explosion Γ p q : StableContext Γ p -> StableContext Γ (FNeg p) -> StableContext Γ q.
Proof.
  intros A B. eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_explosion|exact A]|exact B].
Qed.
Lemma sc_classical Γ p : StableContext (FNeg p::Γ) nd_false -> StableContext Γ p.
Proof.
  intro H. apply sc_deduction in H. unfold nd_false in H.
  eapply sc_mp; [eapply sc_mp; [apply sc_logical,logical_b3|exact H]|apply sc_true].
Qed.
Lemma sc_double_neg_elim Γ p : StableContext Γ (FNeg (FNeg p)) -> StableContext Γ p.
Proof.
  intro H. apply sc_classical.
  eapply sc_explosion with (p:=FNeg p).
  - apply sc_hyp. now left.
  - eapply sc_weaken; [|exact H]. intros q Q. now right.
Qed.
Lemma sc_neg_intro Γ p : StableContext (p::Γ) nd_false -> StableContext Γ (FNeg p).
Proof.
  intro H. apply sc_deduction in H. apply sc_classical.
  eapply sc_mp.
  - eapply sc_weaken; [|exact H]. intros q Q. now right.
  - apply sc_double_neg_elim. apply sc_hyp. now left.
Qed.
Lemma sc_double_neg_intro Γ p : StableContext Γ p -> StableContext Γ (FNeg (FNeg p)).
Proof.
  intro H. apply sc_neg_intro. eapply sc_explosion with (p:=p).
  - eapply sc_weaken; [|exact H]. intros q Q. now right.
  - apply sc_hyp. now left.
Qed.

Lemma sc_and_intro Γ p q : StableContext Γ p -> StableContext Γ q -> StableContext Γ (nd_and p q).
Proof.
  intros P Q. unfold nd_and. apply sc_neg_intro.
  assert (P' : StableContext (FImp p (FNeg q)::Γ) p) by (eapply sc_weaken; [|exact P]; intros x X; now right).
  assert (Q' : StableContext (FImp p (FNeg q)::Γ) q) by (eapply sc_weaken; [|exact Q]; intros x X; now right).
  eapply sc_explosion with (p:=q); [exact Q'|].
  eapply sc_mp; [apply sc_hyp; now left|exact P'].
Qed.
Lemma sc_and_left Γ p q : StableContext Γ (nd_and p q) -> StableContext Γ p.
Proof.
  intro H. apply sc_classical.
  assert (H' : StableContext (FNeg p::Γ) (nd_and p q)) by (eapply sc_weaken; [|exact H]; intros x X; now right).
  eapply sc_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply sc_deduction. eapply sc_explosion with (p:=p).
  - apply sc_hyp. now left.
  - apply sc_hyp. cbn. auto.
Qed.
Lemma sc_and_right Γ p q : StableContext Γ (nd_and p q) -> StableContext Γ q.
Proof.
  intro H. apply sc_classical.
  assert (H' : StableContext (FNeg q::Γ) (nd_and p q)) by (eapply sc_weaken; [|exact H]; intros x X; now right).
  eapply sc_explosion with (p:=FImp p (FNeg q)); [|exact H'].
  apply sc_deduction. apply sc_hyp. cbn. auto.
Qed.
Lemma sc_or_left Γ p q : StableContext Γ p -> StableContext Γ (nd_or p q).
Proof.
  intro H. unfold nd_or. apply sc_deduction. eapply sc_explosion with (p:=p).
  - eapply sc_weaken; [|exact H]. intros x X. now right.
  - apply sc_hyp. now left.
Qed.
Lemma sc_or_elim Γ p q r : StableContext Γ (nd_or p q) -> StableContext (p::Γ) r ->
  StableContext (q::Γ) r -> StableContext Γ r.
Proof.
  intros H P Q. apply sc_deduction in P. apply sc_deduction in Q. apply sc_classical.
  assert (P' : StableContext (FNeg r::Γ) (FImp p r)) by (eapply sc_weaken; [|exact P]; intros x X; now right).
  assert (Q' : StableContext (FNeg r::Γ) (FImp q r)) by (eapply sc_weaken; [|exact Q]; intros x X; now right).
  assert (H' : StableContext (FNeg r::Γ) (nd_or p q)) by (eapply sc_weaken; [|exact H]; intros x X; now right).
  assert (NP : StableContext (FNeg r::Γ) (FNeg p)).
  { apply sc_neg_intro. eapply sc_explosion with (p:=r).
    - eapply sc_mp; [eapply sc_weaken; [|exact P']; intros x X; now right|apply sc_hyp; now left].
    - apply sc_hyp. cbn. auto. }
  assert (Q0 : StableContext (FNeg r::Γ) q) by (unfold nd_or in H'; eapply sc_mp; eassumption).
  eapply sc_explosion with (p:=r).
  - eapply sc_mp; eassumption.
  - apply sc_hyp. now left.
Qed.

Print Assumptions sc_deduction.
Print Assumptions sc_finish.
Print Assumptions sc_classical.
Print Assumptions sc_neg_intro.
Print Assumptions sc_double_neg_elim.
Print Assumptions sc_and_intro.
Print Assumptions sc_and_left.
Print Assumptions sc_and_right.
Print Assumptions sc_or_left.
Print Assumptions sc_or_elim.
