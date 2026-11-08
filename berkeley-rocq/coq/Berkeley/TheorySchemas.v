(** Independently written logical and ZF schemes, checked against the first
    23 source axioms. These are primitive first-order formulas, not semantic
    assumptions about the ambient Rocq universe. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData.
Import ListNotations.

Definition SEqual := Atom false.
Definition SMember := Atom true.
Definition SEx x p := Neg (All x (Neg p)).
Definition SAnd p q := Neg (Imp p (Neg q)).
Definition SOr p q := Imp (Neg p) q.
Definition SIff p q := SAnd (Imp p q) (Imp q p).

Definition logical_schemas : list formula :=
  let p:=Hole 1 in let q:=Hole 2 in let r:=Hole 3 in
  let x:=P 1 in let y:=P 2 in let z:=P 3 in
  [ Imp p (Imp q p);
    Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r));
    Imp (Imp (Neg p) (Neg q)) (Imp q p);
    Imp (All x (Imp (All x q) r)) (Imp (All x q) (All x r));
    Imp (All x q) q;
    Imp (All x (All y r)) (All y (All x r));
    Imp (Neg q) (All x (Neg (All x q)));
    Imp (SEqual x y) (Imp (SEqual x z) (SEqual y z));
    Imp (Neg (All x (SEqual x y)))
      (Imp (Neg (All x (SEqual x z))) (Imp (SEqual y z) (All x (SEqual y z))));
    Imp (All x (Imp (SEqual x y) (All x r))) r;
    Imp (All x (SEqual x y)) (Imp (All x r) (All y r));
    Imp (SEqual x y) (Imp (SMember x z) (SMember y z));
    Imp (SEqual x y) (Imp (SMember z x) (SMember z y));
    Imp (Neg (All x (SEqual x y)))
      (Imp (Neg (All x (SEqual x z))) (Imp (SMember y z) (All x (SMember y z)))) ].

Definition zf_schemas : list formula :=
  let x:=V 0 in let y:=V 1 in let z:=V 2 in let w:=V 3 in
  let protected:=All y (Hole 1) in
  [ (* Extensionality, Empty, Pairing, Union, Power *)
    Imp (All z (SIff (SMember z x) (SMember z y))) (SEqual x y);
    SEx x (All y (Neg (SMember y x)));
    SEx z (All w (SIff (SMember w z) (SOr (SEqual w x) (SEqual w y))));
    SEx y (All z (SIff (SMember z y) (SEx w (SAnd (SMember w x) (SMember z w)))));
    SEx y (All z (SIff (SMember z y) (All w (Imp (SMember w z) (SMember w x)))));
    (* Infinity, including the empty element and successor closure *)
    SEx x (SAnd
      (SEx y (SAnd (SMember y x) (All z (Neg (SMember z y)))))
      (All y (Imp (SMember y x)
        (SEx z (SAnd (SMember z x)
          (All w (SIff (SMember w z) (SOr (SMember w y) (SEqual w y)))))))));
    (* Separation and Replacement with the protected output variable *)
    SEx y (All z (SIff (SMember z y) (SAnd (SMember z x) protected)));
    Imp (All w (SEx y (All z (Imp protected (SEqual z y)))))
      (SEx y (All z (SIff (SMember z y) (SEx w (SAnd (SMember w x) protected)))));
    (* Foundation *)
    All x (Imp (SEx y (SMember y x))
      (SEx y (SAnd (SMember y x) (All z (Imp (SMember z y) (Neg (SMember z x))))))) ].

Theorem candidate_standard_prefix : firstn 23 candidate_axioms = logical_schemas ++ zf_schemas.
Proof. vm_compute. reflexivity. Qed.
Theorem candidate_logical_prefix : firstn 14 candidate_axioms = logical_schemas.
Proof. vm_compute. reflexivity. Qed.
Lemma nth_error_firstn_lt {A : Type} (xs : list A) i n : i<n ->
  nth_error (firstn n xs) i=nth_error xs i.
Proof. revert xs i. induction n; intros xs i H; [lia|].
  destruct xs,i; cbn; auto. apply IHn. lia. Qed.
Lemma candidate_logical_index i f : nth_error logical_schemas i=Some f ->
  nth_error candidate_axioms i=Some f.
Proof.
  intro E. assert (B : i<14).
  { change 14 with (length logical_schemas). apply nth_error_Some. rewrite E. discriminate. }
  rewrite <- (nth_error_firstn_lt candidate_axioms i 14 B),candidate_logical_prefix. exact E.
Qed.

Print Assumptions candidate_standard_prefix.
Print Assumptions candidate_logical_prefix.
Print Assumptions candidate_logical_index.
