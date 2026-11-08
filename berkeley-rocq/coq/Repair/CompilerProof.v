(** Check the builder's binary source DAG against the literal quotient table. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine CompilerSyntax.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl RuntimeProgram RuntimeJumps.
Import ListNotations.
Local Opaque Repair.Data.new_table.

(** These are the branch-specific rules in TMBuilder.generate.  In the
    generated program all control leaves are on the one branch.  The source
    continue level counts that branch itself; the machine has already erased
    it, hence the predecessor in the target. *)
Definition compiled_transition (states : list nat) (b : bool) (a : source_atom)
    : option transition :=
  match a with
  | SNode j => option_map (fun q => (b,R,q)) (nth_error states j)
  | SInc i => if i <? 11 then Some(b,R,inc_entry i) else None
  | SDec i => if i <? 11 then Some(b,R,dec_entry i) else None
  | SHalt => Some(b,R,1399)
  | SBreak k => if andb b (k <=? 2) then Some(false,L,break_state k) else None
  | SContinue k => if andb b (andb (0 <? k) (k <=? 4))
                   then Some(false,L,continue_state (Nat.pred k)) else None
  end.

Definition compiler_edge_check states q b a :=
  match compiled_transition states b a with
  | None => false
  | Some t => option_eqb (lookup new_table q b) (Some t)
  end.
Definition compiler_pair_check states (entry : nat * source_pair) :=
  let '(q,(a,b)) := entry in
  andb (andb (node q) (compiler_edge_check states q false a))
    (compiler_edge_check states q true b).
Definition compiler_check program states :=
  andb (Nat.eqb (length program) (length states))
    (forallb (compiler_pair_check states) (combine states program)).

Lemma nth_error_combine_some {A B} (xs : list A) (ys : list B) i a b :
  nth_error xs i = Some a -> nth_error ys i = Some b ->
  nth_error (combine xs ys) i = Some (a,b).
Proof.
  revert xs ys. induction i as [|i IH]; intros [|x xs] [|y ys] X Y;
    cbn in *; try discriminate.
  - now inversion X; inversion Y.
  - apply IH; assumption.
Qed.

Lemma compiler_pair_checked program states i pair q :
  compiler_check program states = true ->
  nth_error program i = Some pair -> nth_error states i = Some q ->
  node q = true /\ forall b, compiler_edge_check states q b (select_branch pair b) = true.
Proof.
  intros Check P Q. unfold compiler_check in Check.
  apply andb_true_iff in Check as [_ Check].
  rewrite forallb_forall in Check.
  specialize (Check (q,pair)).
  assert (H : In (q,pair) (combine states program)).
  { apply nth_error_In with (n:=i). eapply nth_error_combine_some; eassumption. }
  specialize (Check H). destruct pair as [a0 a1].
  cbn [compiler_pair_check] in Check.
  apply andb_true_iff in Check as [K C1].
  apply andb_true_iff in K as [N C0]. split; [exact N|].
  intros []; cbn [select_branch]; assumption.
Qed.

Lemma compiler_edge_checked states q b a : compiler_edge_check states q b a = true ->
  exists t, compiled_transition states b a = Some t /\ lookup new_table q b = Some t.
Proof.
  unfold compiler_edge_check. destruct (compiled_transition states b a) as [t|] eqn:E;
    [|discriminate]. intro H. exists t. split; [reflexivity|].
  apply option_eqb_sound, H.
Qed.

(** The consequences use the existing read-only traversal relation and the
    runtime's explicit return operations, but do not define source selection
    in terms of the machine table. *)
Definition realizes q bits a : Prop :=
  match a with
  | SNode _ => False
  | SInc i => i < 11 /\ ReadPath q bits (inc_entry i)
  | SDec i => i < 11 /\ ReadPath q bits (dec_entry i)
  | SHalt => ReadPath q bits 1399
  | SBreak k => k <= 2 /\ exists pre t,
      bits = pre ++ [true] /\ ReadPath q pre t /\
      lookup new_table t true = Some(false,L,break_state k)
  | SContinue k => 1 <= k /\ k <= 4 /\ exists pre t,
      bits = pre ++ [true] /\ ReadPath q pre t /\
      lookup new_table t true = Some(false,L,continue_state (Nat.pred k))
  end.

Lemma realizes_prepend q t b bits a : node q = true ->
  lookup new_table q b = Some(b,R,t) -> realizes t bits a -> realizes q (b::bits) a.
Proof.
  intros N E H. destruct a as [j|i|i| |k|k]; cbn [realizes] in *.
  - contradiction.
  - destruct H as [Hi P]. split; [exact Hi|]. econstructor; eauto.
  - destruct H as [Hi P]. split; [exact Hi|]. econstructor; eauto.
  - econstructor; eauto.
  - destruct H as [Hk [pre [u [B [P T]]]]].
    split; [exact Hk|]. exists (b::pre),u. subst bits. simpl. repeat split; eauto.
    econstructor; eauto.
  - destruct H as [H1 [Hk [pre [u [B [P T]]]]]].
    repeat split; try assumption. exists (b::pre),u. subst bits. simpl.
    repeat split; eauto. econstructor; eauto.
Qed.

Theorem source_selection_compiles program states i q bits a :
  compiler_check program states = true -> nth_error states i = Some q ->
  SourceSelect program i bits a -> realizes q bits a.
Proof.
  intros C Q S. revert q Q. induction S as
    [i pair b leaf P B Leaf | i pair b j bits leaf P B S IH]; intros q Q.
  - destruct (compiler_pair_checked _ _ _ _ _ C P Q) as [N V].
    specialize (V b). rewrite B in V.
    destruct (compiler_edge_checked _ _ _ _ V) as [tr [E T]].
    destruct leaf as [j|ri|ri| |k|k]; cbn [is_leaf] in Leaf; try discriminate;
      cbn [compiled_transition] in E; cbn [realizes].
    + destruct (ri <? 11) eqn:Hi; [|discriminate].
      inversion E; subst tr. split; [now apply Nat.ltb_lt|].
      econstructor; [exact N|exact T|constructor].
    + destruct (ri <? 11) eqn:Hi; [|discriminate].
      inversion E; subst tr. split; [now apply Nat.ltb_lt|].
      econstructor; [exact N|exact T|constructor].
    + inversion E; subst tr. econstructor; [exact N|exact T|constructor].
    + destruct b; cbn in E; [|discriminate].
      destruct (k <=? 2) eqn:Hk; [|discriminate].
      inversion E; subst tr. apply Nat.leb_le in Hk. split; [exact Hk|].
      exists ([] : list bool),q. repeat split; try reflexivity; [constructor|exact T].
    + destruct b; cbn in E; [|discriminate].
      destruct k as [|k]; cbn in E; [discriminate|].
      destruct (k <=? 3) eqn:Hk; cbn in E; [|discriminate].
      inversion E; subst tr. apply Nat.leb_le in Hk.
      repeat split; try lia. exists ([] : list bool),q.
      repeat split; try reflexivity; [constructor|exact T].
  - destruct (compiler_pair_checked _ _ _ _ _ C P Q) as [N V].
    specialize (V b). rewrite B in V.
    destruct (compiler_edge_checked _ _ _ _ V) as [tr [E T]].
    cbn [compiled_transition] in E.
    destruct (nth_error states j) as [u|] eqn:U; cbn in E; [|discriminate].
    inversion E; subst tr. eapply realizes_prepend; [exact N|exact T|].
    apply IH; reflexivity.
Qed.

Print Assumptions source_selection_compiles.
