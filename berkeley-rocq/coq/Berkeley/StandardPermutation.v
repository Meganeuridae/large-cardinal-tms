(** Simultaneous finite variable permutations preserve closed theorems. *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
From Berkeley Require Import ProofFormula LogicBridge FormulaRenaming TheoryIrreflexiveND
  AugmentedLogic StandardND StandardAugEquivalence NatPermutations ZFPermuteFree
  StableLogic StableCongruence StableAlpha StableBinderElimination.
Import ListNotations.

Lemma swap_self a n : swap_nat a a n=n.
Proof. destruct (Nat.eq_dec n a) as [E|E]; [subst;apply swap_left|now apply swap_other]. Qed.
Theorem standard_theorem_swap a b p :
  StandardND [] p -> StandardND [] (rename_formula (swap_nat a b) p).
Proof.
  intro H. destruct (Nat.eq_dec a b) as [E|E].
  - subst b. rewrite (rename_ext (swap_nat a a) (fun n=>n) p (swap_self a)),rename_identity. exact H.
  - destruct (stable_eliminate_two_binders a b p) as [q [[PQ QP] [A B]]].
    assert (Q : StandardND [] q).
    { eapply std_imp_elim; [apply augmented_theorem_to_standard,stable_extract,PQ|exact H]. }
    pose proof (standard_theorem_swap_without_bound a b q E A B Q) as SWQ.
    specialize (QP (swap_nat a b) (swap_injective a b)).
    apply augmented_theorem_to_standard in QP. cbn [rename_formula] in QP.
    eapply std_imp_elim; [exact QP|exact SWQ].
Qed.

Theorem standard_theorem_update_perm pi a v p :
  (forall q, StandardND [] q -> StandardND [] (rename_formula pi q)) ->
  StandardND [] p -> StandardND [] (rename_formula (update_perm pi a v) p).
Proof.
  intros P H. unfold update_perm. rewrite <- rename_composition.
  apply standard_theorem_swap,P,H.
Qed.
Theorem standard_theorem_perm4 x y z w p :
  StandardND [] p -> StandardND [] (rename_formula (perm4 x y z w) p).
Proof.
  unfold perm4,perm3,perm2,perm1.
  intro H. apply standard_theorem_update_perm; [|exact H].
  intros q Hq. apply standard_theorem_update_perm; [|exact Hq].
  intros r Hr. apply standard_theorem_update_perm; [|exact Hr].
  intros s Hs. apply standard_theorem_update_perm; [|exact Hs].
  intros t Ht. now rewrite rename_identity.
Qed.
Fixpoint finite_swaps (swaps:list (nat*nat)) (n:nat) : nat :=
  match swaps with
  | [] => n
  | (a,b)::rest => swap_nat a b (finite_swaps rest n)
  end.
Theorem standard_theorem_finite_swaps swaps p :
  StandardND [] p -> StandardND [] (rename_formula (finite_swaps swaps) p).
Proof.
  induction swaps as [|[a b] rest IH]; intro H; cbn [finite_swaps].
  - now rewrite rename_identity.
  - rewrite <- rename_composition. apply standard_theorem_swap,IH,H.
Qed.
Print Assumptions standard_theorem_finite_swaps.
Print Assumptions standard_theorem_swap.
Print Assumptions standard_theorem_perm4.
