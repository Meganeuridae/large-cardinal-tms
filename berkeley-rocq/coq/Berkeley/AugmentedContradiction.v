(** Contradiction target for the separate augmented presentation. *)
From Berkeley Require Import ProofFormula LogicBridge AugmentedLogic AugmentedIrreflexive.
Definition AugInconsistent := exists p, AugProvable p /\ AugProvable (FNeg p).
Theorem augmented_target_iff_internal_inconsistency :
  AugProvable (FMember 0 0) <-> AugInconsistent.
Proof.
  split.
  - intro H. exists (FMember 0 0). split; [exact H|apply augmented_irreflexive].
  - intros [p [P N]]. eapply aug_mp.
    + eapply aug_mp; [apply aug_logical,logical_explosion|exact P].
    + exact N.
Qed.
Print Assumptions augmented_target_iff_internal_inconsistency.
