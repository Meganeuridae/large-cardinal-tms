(** A finite first-order natural-deduction certificate for Foundation's
    irreflexivity consequence.  [ND] is an independently defined certificate
    system; its translation to PresentedProvable is a separate obligation. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation.
Import ListNotations.

Definition nd_and p q := FNeg (FImp p (FNeg q)).
Definition nd_or p q := FImp (FNeg p) q.
Definition nd_iff p q := nd_and (FImp p q) (FImp q p).
Definition nd_ex x p := FNeg (FAll x (FNeg p)).
Definition nd_true := FImp (FEqual 0 0) (FEqual 0 0).
Definition nd_false := FNeg nd_true.

Fixpoint nd_free x p :=
  match p with
  | FEqual y z | FMember y z => Nat.eqb x y || Nat.eqb x z
  | FNeg p => nd_free x p
  | FImp p q => nd_free x p || nd_free x q
  | FAll y p => if Nat.eqb x y then false else nd_free x p
  end.
Fixpoint nd_not_bound y p :=
  match p with
  | FEqual _ _ | FMember _ _ => true
  | FNeg p => nd_not_bound y p
  | FImp p q => nd_not_bound y p && nd_not_bound y q
  | FAll x p => negb (Nat.eqb x y) && nd_not_bound y p
  end.
Fixpoint nd_subst x y p :=
  let v z := if Nat.eqb z x then y else z in
  match p with
  | FEqual a b => FEqual (v a) (v b)
  | FMember a b => FMember (v a) (v b)
  | FNeg p => FNeg (nd_subst x y p)
  | FImp p q => FImp (nd_subst x y p) (nd_subst x y q)
  | FAll z p => if Nat.eqb z x then FAll z p else FAll z (nd_subst x y p)
  end.
Definition nd_fresh x (ctx : list fol_formula) := forall p, In p ctx -> nd_free x p=false.

(** The connective and equality rules below are displayed explicitly so the
    future Hilbert translation cannot be mistaken for an existing proof. *)
Inductive ND (ctx : list fol_formula) : fol_formula -> Prop :=
| nd_hyp p : In p ctx -> ND ctx p
| nd_presented p : PresentedProvable p -> ND ctx p
| nd_imp_intro p q : ND (p::ctx) q -> ND ctx (FImp p q)
| nd_imp_elim p q : ND ctx (FImp p q) -> ND ctx p -> ND ctx q
| nd_neg_intro p : ND (p::ctx) nd_false -> ND ctx (FNeg p)
| nd_exfalso p q : ND ctx p -> ND ctx (FNeg p) -> ND ctx q
| nd_and_intro p q : ND ctx p -> ND ctx q -> ND ctx (nd_and p q)
| nd_and_left p q : ND ctx (nd_and p q) -> ND ctx p
| nd_and_right p q : ND ctx (nd_and p q) -> ND ctx q
| nd_or_left p q : ND ctx p -> ND ctx (nd_or p q)
| nd_or_elim p q r : ND ctx (nd_or p q) -> ND (p::ctx) r -> ND (q::ctx) r -> ND ctx r
| nd_iff_left p q : ND ctx (nd_iff p q) -> ND ctx p -> ND ctx q
| nd_iff_right p q : ND ctx (nd_iff p q) -> ND ctx q -> ND ctx p
| nd_all_intro x p : nd_fresh x ctx -> ND ctx p -> ND ctx (FAll x p)
| nd_all_elim x y p : nd_not_bound y p=true -> ND ctx (FAll x p) -> ND ctx (nd_subst x y p)
| nd_ex_intro x y p : nd_not_bound y p=true -> ND ctx (nd_subst x y p) -> ND ctx (nd_ex x p)
| nd_ex_elim x y p q : nd_not_bound y p=true -> nd_free y p=false -> nd_fresh y ctx -> nd_free y q=false ->
    ND ctx (nd_ex x p) -> ND (nd_subst x y p::ctx) q -> ND ctx q
| nd_eq_refl x : ND ctx (FEqual x x)
| nd_eq_sym x y : ND ctx (FEqual x y) -> ND ctx (FEqual y x)
| nd_mem_right x y z : ND ctx (FEqual x y) -> ND ctx (FMember z x) -> ND ctx (FMember z y).

Definition pair_axiom := nd_ex 2 (FAll 3 (nd_iff (FMember 3 2)
  (nd_or (FEqual 3 0) (FEqual 3 1)))).
Definition foundation_body := FImp (nd_ex 1 (FMember 1 0))
  (nd_ex 1 (nd_and (FMember 1 0) (FAll 2 (FImp (FMember 2 1) (FNeg (FMember 2 0)))))).
Definition foundation_axiom := FAll 0 foundation_body.

Lemma pair_axiom_presented : PresentedProvable pair_axiom.
Proof.
  change (PresentedProvable (independent_instance (fun n=>n) (fun _=>FEqual 0 0)
    (nth 16 candidate_axioms (Hole 0)))).
  eapply presented_axiom with (i:=16). reflexivity.
Qed.
Lemma foundation_axiom_presented : PresentedProvable foundation_axiom.
Proof.
  change (PresentedProvable (independent_instance (fun n=>n) (fun _=>FEqual 0 0)
    (nth 22 candidate_axioms (Hole 0)))).
  eapply presented_axiom with (i:=22). reflexivity.
Qed.

Definition singleton_body := FAll 3 (nd_iff (FMember 3 2)
  (nd_or (FEqual 3 0) (FEqual 3 0))).
Definition singleton4 := FAll 3 (nd_iff (FMember 3 4)
  (nd_or (FEqual 3 0) (FEqual 3 0))).
Definition foundation_witness := nd_and (FMember 1 4)
  (FAll 2 (FImp (FMember 2 1) (FNeg (FMember 2 4)))).
Definition witness5 := nd_and (FMember 5 4)
  (FAll 2 (FImp (FMember 2 5) (FNeg (FMember 2 4)))).

Lemma nd_pair_singleton ctx : nd_fresh 1 ctx -> ND ctx (nd_ex 2 singleton_body).
Proof.
  intro Fresh. change (ND ctx (nd_subst 1 0 pair_axiom)).
  eapply nd_all_elim with (x:=1) (p:=pair_axiom); [reflexivity|].
  apply nd_all_intro; [exact Fresh|]. apply nd_presented,pair_axiom_presented.
Qed.

Lemma nd_foundation4 ctx :
  ND ctx (FImp (nd_ex 1 (FMember 1 4)) (nd_ex 1 foundation_witness)).
Proof.
  change (ND ctx (nd_subst 0 4 foundation_body)).
  eapply nd_all_elim with (x:=0) (p:=foundation_body); [reflexivity|].
  apply nd_presented,foundation_axiom_presented.
Qed.

Lemma nd_singleton_contains_zero ctx : ND ctx singleton4 -> ND ctx (FMember 0 4).
Proof.
  intro H. eapply nd_iff_right with (q:=nd_or (FEqual 0 0) (FEqual 0 0)).
  - change (ND ctx (nd_subst 3 0 (nd_iff (FMember 3 4)
      (nd_or (FEqual 3 0) (FEqual 3 0))))).
    eapply nd_all_elim with (x:=3); [reflexivity|exact H].
  - apply nd_or_left,nd_eq_refl.
Qed.

Lemma nd_singleton_member5_eq ctx : ND ctx singleton4 -> ND ctx (FMember 5 4) -> ND ctx (FEqual 5 0).
Proof.
  intros H Mem. eapply nd_or_elim with (p:=FEqual 5 0) (q:=FEqual 5 0).
  - eapply nd_iff_left with (p:=FMember 5 4).
    + change (ND ctx (nd_subst 3 5 (nd_iff (FMember 3 4)
        (nd_or (FEqual 3 0) (FEqual 3 0))))).
      eapply nd_all_elim with (x:=3); [reflexivity|exact H].
    + exact Mem.
  - apply nd_hyp. now left.
  - apply nd_hyp. now left.
Qed.

Theorem natural_deduction_irreflexive : ND [] (FNeg (FMember 0 0)).
Proof.
  apply nd_neg_intro.
  eapply nd_ex_elim with (x:=2) (y:=4) (p:=singleton_body).
  - reflexivity.
  - reflexivity.
  - unfold nd_fresh. intros p H. cbn in H. destruct H as [E|[]]. subst p. reflexivity.
  - reflexivity.
  - apply nd_pair_singleton. unfold nd_fresh. intros p H. cbn in H. destruct H as [E|[]]. subst p. reflexivity.
  - change (ND [singleton4; FMember 0 0] nd_false).
    eapply nd_ex_elim with (x:=1) (y:=5) (p:=foundation_witness).
    + reflexivity.
    + reflexivity.
    + unfold nd_fresh. intros p H. cbn in H. destruct H as [E|[E|[]]]; subst p; reflexivity.
    + reflexivity.
    + eapply nd_imp_elim; [apply nd_foundation4|].
      eapply nd_ex_intro with (x:=1) (y:=0) (p:=FMember 1 4); [reflexivity|].
      apply nd_singleton_contains_zero,nd_hyp. now left.
    + change (ND [witness5; singleton4; FMember 0 0] nd_false).
      assert (Sing : ND [witness5;singleton4;FMember 0 0] singleton4) by (apply nd_hyp; cbn; auto).
      assert (Witness : ND [witness5;singleton4;FMember 0 0] witness5) by (apply nd_hyp; now left).
      assert (Mem5 : ND [witness5;singleton4;FMember 0 0] (FMember 5 4)).
      { eapply nd_and_left. exact Witness. }
      assert (Eq50 : ND [witness5;singleton4;FMember 0 0] (FEqual 5 0)) by (eapply nd_singleton_member5_eq; eassumption).
      assert (Self : ND [witness5;singleton4;FMember 0 0] (FMember 0 0)) by (apply nd_hyp; cbn; auto).
      assert (Mem05 : ND [witness5;singleton4;FMember 0 0] (FMember 0 5)).
      { eapply nd_mem_right; [apply nd_eq_sym,Eq50|exact Self]. }
      assert (Disjoint : ND [witness5;singleton4;FMember 0 0]
        (FAll 2 (FImp (FMember 2 5) (FNeg (FMember 2 4))))) by (eapply nd_and_right; exact Witness).
      assert (NotIn : ND [witness5;singleton4;FMember 0 0] (FNeg (FMember 0 4))).
      { eapply nd_imp_elim; [|exact Mem05].
        change (ND [witness5;singleton4;FMember 0 0] (nd_subst 2 0
          (FImp (FMember 2 5) (FNeg (FMember 2 4))))).
        eapply nd_all_elim with (x:=2); [reflexivity|exact Disjoint]. }
      eapply nd_exfalso; [apply nd_singleton_contains_zero,Sing|exact NotIn].
Qed.

Print Assumptions pair_axiom_presented.
Print Assumptions foundation_axiom_presented.
Print Assumptions natural_deduction_irreflexive.
