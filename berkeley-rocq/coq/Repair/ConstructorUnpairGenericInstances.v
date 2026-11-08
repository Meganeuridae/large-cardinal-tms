(** Concrete source unpair roots used by proof-list decoding and selection. *)
From Repair Require Import CompilerData ConstructorGraph SourceExecution.
Local Transparent source_graph unfold_root.

Theorem source_unpair_prooflist_tree : unfold_root 636 = Some (tree_unpair 0 8 9).
Proof. vm_compute. reflexivity. Qed.

Theorem source_unpair_select_tree : unfold_root 674 = Some (tree_unpair 3 2 9).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions source_unpair_prooflist_tree.
Print Assumptions source_unpair_select_tree.
