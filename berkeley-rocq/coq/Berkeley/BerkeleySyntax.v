(** Independent compositional reconstruction of the finite Berkeley sentence.
    This is a syntax identity, not a semantic proof about Berkeley cardinals. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax SyntaxData BerkeleySyntaxBase BerkeleySyntaxSatisfaction.
Import ListNotations.

Definition b_critical j k d eta := b_and4
  (b_mem k d) (b_mem eta k) (b_not (b_rel j k k))
  (b_ain k (fun a => b_rel j a a)).

Definition b_berkeley_witnesses d m e f w sat :=
  b_ain d (fun eta => b_ex (fun j => b_ex (fun k =>
    b_and (b_critical j k d eta) (b_elementary j m e f w sat)))).

Definition b_berkeley_local d m f w te tm tn ti ta :=
  b_ex (fun e => b_ex (fun sat => b_and3
    (b_environments e w m)
    (b_satisfaction sat e f w m te tm tn ti ta)
    (b_berkeley_witnesses d m e f w sat))).

Definition b_berkeley_cardinal f w te tm tn ti ta :=
  b_ex (fun d => b_and3 (b_cardinal d) (b_mem w d)
    (b_all (fun m => b_imp (b_and (b_transitive m) (b_mem d m))
      (b_berkeley_local d m f w te tm tn ti ta)))).

Definition b_berkeley_sentence : builder :=
  b_ex (fun w => b_ex (fun z0 => b_ex (fun z1 => b_ex (fun z2 =>
  b_ex (fun z3 => b_ex (fun z4 => b_ex (fun f =>
    b_and
      (b_and
        (b_and
          (b_and
            (b_and
              (b_and
                (b_and (b_omega w) (b_empty z0))
                (b_successor z1 z0))
              (b_successor z2 z1))
            (b_successor z3 z2))
          (b_successor z4 z3))
        (b_formulas f w z0 z1 z2 z3 z4))
      (b_berkeley_cardinal f w z0 z1 z2 z3 z4)))))))).

Definition reconstructed_berkeley : formula := fst (b_berkeley_sentence 0).

Definition db_bound_variable v := match v with Bound _ => true | Free _ => false end.
Fixpoint db_sentence (p : db_formula) : bool :=
  match p with
  | DBAtom _ x y => andb (db_bound_variable x) (db_bound_variable y)
  | DBNeg p => db_sentence p
  | DBImp p q => andb (db_sentence p) (db_sentence q)
  | DBAll p => db_sentence p
  | DBHole _ => false
  end.

Theorem reconstructed_berkeley_is_closed : db_sentence (canonical reconstructed_berkeley []) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem reconstructed_berkeley_is_original :
  canonical reconstructed_berkeley [] = canonical (nth 23 original_axioms (Hole 0)) [].
Proof. vm_compute. reflexivity. Qed.

Theorem reconstructed_berkeley_is_candidate :
  canonical reconstructed_berkeley [] = canonical (nth 23 candidate_axioms (Hole 0)) [].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions reconstructed_berkeley_is_original.
Print Assumptions reconstructed_berkeley_is_candidate.
Print Assumptions reconstructed_berkeley_is_closed.
