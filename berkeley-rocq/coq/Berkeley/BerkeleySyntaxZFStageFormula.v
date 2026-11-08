(** First-order coding of finite pair-stage histories. In particular the
    internal induction predicate is a specific formula with a verified free
    variable bound, not an arbitrary external subset of omega. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxFunctionFacts BerkeleySyntaxBijection
  BerkeleySyntaxOmega BerkeleySyntaxFormulaSet BerkeleySyntaxZFSeparation BerkeleySyntaxZFPairStage
  BerkeleySyntaxZFFiniteGraph BerkeleySyntaxZFStageRun.
Import ListNotations.
Definition b_run_zero h seed := b_all (fun zero => b_imp (b_empty zero) (b_rel h zero seed)).
Definition b_run_edge_core h i j a b := b_and3 (b_rel h i a) (b_rel h j b) (b_pair_stage a b).
Definition b_run_edge h i j := b_ex (fun a => b_ex (fun b => b_run_edge_core h i j a b)).
Definition b_run_steps h dom := b_ain dom (fun i => b_ain dom (fun j =>
  b_imp (b_successor j i) (b_run_edge h i j))).
Definition b_run_domain h n seed dom := b_and4 (b_successor dom n) (b_partial_function h dom)
  (b_run_zero h seed) (b_run_steps h dom).
Definition b_stage_run h n seed := b_ex (fun dom => b_run_domain h n seed dom).
Definition b_run_exists n seed := b_ex (fun h => b_stage_run h n seed).
Definition pair_run_formula := instantiate_formula (fun _=>0) (fst (b_run_exists 2 3 4)).
Lemma pair_run_formula_output_fresh : fol_free 1 pair_run_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma b_good_partial_function s dom : b_good (b_partial_function s dom).
Proof. unfold b_partial_function. apply b_good_ex. intro cod. apply b_good_function. Qed.
Lemma b_good_pair_stage a b : b_good (b_pair_stage a b).
Proof.
  unfold b_pair_stage. apply b_good_ex. intro p. apply b_good_ex. intro q. unfold b_and3.
  repeat apply b_good_and; try apply good_powerset; apply good_binary_union.
Qed.
Lemma b_good_run_zero h seed : b_good (b_run_zero h seed).
Proof.
  unfold b_run_zero. apply b_good_all. intro z. unfold b_imp.
  apply b_good_binary; [apply b_good_empty|apply b_good_rel].
Qed.
Lemma b_good_run_edge_core h i j a b : b_good (b_run_edge_core h i j a b).
Proof.
  unfold b_run_edge_core,b_and3. repeat apply b_good_and; try apply b_good_rel. apply b_good_pair_stage.
Qed.
Lemma b_good_run_edge h i j : b_good (b_run_edge h i j).
Proof. unfold b_run_edge. apply b_good_ex. intro a. apply b_good_ex. intro b. apply b_good_run_edge_core. Qed.
Lemma b_good_run_steps h dom : b_good (b_run_steps h dom).
Proof.
  unfold b_run_steps. apply b_good_ain. intro i. apply b_good_ain. intro j. unfold b_imp.
  apply b_good_binary; [apply b_good_successor|apply b_good_run_edge].
Qed.
Section Formula.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Theorem run_edge_core_holds rho h i j a b n : h<n -> i<n -> j<n -> a<n -> b<n ->
  (b_holds R rho (b_run_edge_core h i j a b) n <->
   RelGraph R (rho h) (rho i) (rho a) /\ RelGraph R (rho h) (rho j) (rho b) /\
   RelPairStage R (rho a) (rho b)).
Proof.
  intros H I J A B. unfold b_run_edge_core,b_and3. rewrite !(b_holds_and EM).
  assert (K1:n<=b_next (b_rel h i a) n) by apply b_good_rel.
  assert (K2:n<=b_next (b_and (b_rel h i a) (b_rel h j b)) n)
    by (apply b_good_and; apply b_good_rel).
  rewrite !(relation_builder_holds EM) by lia.
  rewrite (pair_stage_builder_holds R EM) by lia. tauto.
Qed.
Theorem run_edge_holds rho h i j n : h<n -> i<n -> j<n ->
  (b_holds R rho (b_run_edge h i j) n <-> exists a b,
   RelGraph R (rho h) (rho i) a /\ RelGraph R (rho h) (rho j) b /\ RelPairStage R a b).
Proof.
  intros H I J. unfold b_run_edge. rewrite (b_holds_ex EM). split.
  - intros [a T]. rewrite (b_holds_ex EM) in T. destruct T as [b T]. rewrite run_edge_core_holds in T by lia.
    set (sigma:=update_variable (update_variable rho n a) (S n) b) in T.
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma i=rho i) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sj:sigma j=rho j) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma n=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S n)=b) by (unfold sigma;apply update_variable_eq).
    rewrite Sh,Si,Sj,Sa,Sb in T. now exists a,b.
  - intros [a [b T]]. exists a. rewrite (b_holds_ex EM). exists b. rewrite run_edge_core_holds by lia.
    set (sigma:=update_variable (update_variable rho n a) (S n) b).
    change (RelGraph R (sigma h) (sigma i) (sigma n) /\ RelGraph R (sigma h) (sigma j) (sigma (S n)) /\
      RelPairStage R (sigma n) (sigma (S n))).
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma i=rho i) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sj:sigma j=rho j) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Sa:sigma n=a) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sb:sigma (S n)=b) by (unfold sigma;apply update_variable_eq).
    now rewrite Sh,Si,Sj,Sa,Sb.
Qed.
Theorem run_zero_holds rho h seed n : h<n -> seed<n ->
  (b_holds R rho (b_run_zero h seed) n <->
   forall zero, RelEmpty R zero -> RelGraph R (rho h) zero (rho seed)).
Proof.
  intros H Seed. unfold b_run_zero. rewrite b_holds_all. split; intros T zero; specialize (T zero).
  - rewrite b_holds_imp,empty_builder_holds in T by lia.
    assert (K:S n<=b_next (b_empty n) (S n)) by apply b_good_empty.
    rewrite (relation_builder_holds EM) in T by lia.
    rewrite update_variable_eq in T. repeat rewrite update_variable_neq in T by lia. exact T.
  - rewrite b_holds_imp,empty_builder_holds by lia.
    assert (K:S n<=b_next (b_empty n) (S n)) by apply b_good_empty.
    rewrite (relation_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact T.
Qed.
Theorem run_steps_holds rho h dom n : h<n -> dom<n ->
  (b_holds R rho (b_run_steps h dom) n <->
   forall i j, R i (rho dom) -> R j (rho dom) -> RelSuccessor R j i ->
     exists a b, RelGraph R (rho h) i a /\ RelGraph R (rho h) j b /\ RelPairStage R a b).
Proof.
  intros H Dom. unfold b_run_steps. rewrite b_holds_ain by exact Dom. split.
  - intros T i j I J. specialize (T i I). rewrite b_holds_ain in T by lia.
    specialize (T j). rewrite update_variable_neq in T by lia. specialize (T J).
    rewrite b_holds_imp in T. rewrite (successor_builder_holds D R EM) in T by lia.
    assert (K:S(S n)<=b_next (b_successor (S n) n) (S(S n))) by apply b_good_successor.
    rewrite run_edge_holds in T by lia.
    set (sigma:=update_variable (update_variable rho n i) (S n) j) in T.
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma n=i) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sj:sigma (S n)=j) by (unfold sigma;apply update_variable_eq).
    now rewrite Sh,Si,Sj in T.
  - intros T i I. rewrite b_holds_ain by lia. intros j J.
    rewrite update_variable_neq in J by lia. rewrite b_holds_imp.
    rewrite (successor_builder_holds D R EM) by lia.
    assert (K:S(S n)<=b_next (b_successor (S n) n) (S(S n))) by apply b_good_successor.
    rewrite run_edge_holds by lia.
    set (sigma:=update_variable (update_variable rho n i) (S n) j).
    change (RelSuccessor R (sigma (S n)) (sigma n) -> exists a b,
      RelGraph R (sigma h) (sigma n) a /\ RelGraph R (sigma h) (sigma (S n)) b /\ RelPairStage R a b).
    assert (Sh:sigma h=rho h) by (unfold sigma;repeat rewrite update_variable_neq by lia;reflexivity).
    assert (Si:sigma n=i) by (unfold sigma;rewrite update_variable_neq by lia;apply update_variable_eq).
    assert (Sj:sigma (S n)=j) by (unfold sigma;apply update_variable_eq).
    rewrite Sh,Si,Sj. now apply T.
Qed.
Definition RelRunEdgesExists h dom := forall i j, R i dom -> R j dom -> RelSuccessor R j i ->
  exists a b, RelGraph R h i a /\ RelGraph R h j b /\ RelPairStage R a b.
Lemma run_edges_exists_iff h dom : RelPartialFunction R h dom ->
  (RelRunEdgesExists h dom <-> forall i j a b, R i dom -> R j dom -> RelSuccessor R j i ->
    RelGraph R h i a -> RelGraph R h j b -> RelPairStage R a b).
Proof.
  intros [cod F]. split.
  - intros Edges i j a b I J S Ai Bj. destruct (Edges i j I J S) as [a' [b' [Ai' [Bj' Stage]]]].
    assert (a'=a) by (eapply relational_function_graph_unique; eassumption).
    assert (b'=b) by (eapply relational_function_graph_unique; eassumption). now subst a' b'.
  - intros Edges i j I J S. destruct F as [Graph Total].
    destruct (Total i I) as [a [A [Ai U]]]. destruct (Total j J) as [b [B [Bj V]]].
    exists a,b. split; [exact Ai|]. split; [exact Bj|]. exact (Edges i j a b I J S Ai Bj).
Qed.
Theorem run_domain_holds rho h n seed dom k : h<k -> n<k -> seed<k -> dom<k ->
  (b_holds R rho (b_run_domain h n seed dom) k <->
   RelSuccessor R (rho dom) (rho n) /\ RelPartialFunction R (rho h) (rho dom) /\
   (forall zero, RelEmpty R zero -> RelGraph R (rho h) zero (rho seed)) /\
   RelRunEdgesExists (rho h) (rho dom)).
Proof.
  intros H N Seed Dom. unfold b_run_domain,b_and4,b_and3. rewrite !(b_holds_and EM).
  assert (K1:k<=b_next (b_successor dom n) k) by apply b_good_successor.
  assert (K2:k<=b_next (b_and (b_successor dom n) (b_partial_function h dom)) k)
    by (apply b_good_and; [apply b_good_successor|apply b_good_partial_function]).
  assert (K3:k<=b_next (b_and (b_and (b_successor dom n) (b_partial_function h dom)) (b_run_zero h seed)) k)
    by (repeat apply b_good_and; try apply b_good_successor; try apply b_good_partial_function; apply b_good_run_zero).
  rewrite (successor_builder_holds D R EM) by lia.
  rewrite (partial_function_builder_holds R EM) by lia.
  rewrite run_zero_holds by lia.
  rewrite run_steps_holds by lia.
  unfold RelRunEdgesExists. tauto.
Qed.
Theorem stage_run_builder_holds rho h n seed k : h<k -> n<k -> seed<k ->
  (b_holds R rho (b_stage_run h n seed) k <-> RelPairStageRun R (rho h) (rho n) (rho seed)).
Proof.
  intros H N Seed. unfold b_stage_run,RelPairStageRun. rewrite (b_holds_ex EM). split.
  - intros [dom T]. rewrite run_domain_holds in T by lia.
    set (sigma:=update_variable rho k dom) in T.
    assert (Sh:sigma h=rho h) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Sn:sigma n=rho n) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Ss:sigma seed=rho seed) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Sd:sigma k=dom) by (unfold sigma;apply update_variable_eq).
    rewrite Sh,Sn,Ss,Sd in T. destruct T as [S [P [Z E]]]. exists dom.
    split; [exact S|]. split; [exact P|]. split; [exact Z|].
    now apply (proj1 (run_edges_exists_iff _ _ P)).
  - intros [dom [S [P [Z E]]]]. exists dom. rewrite run_domain_holds by lia.
    set (sigma:=update_variable rho k dom).
    assert (Sh:sigma h=rho h) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Sn:sigma n=rho n) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Ss:sigma seed=rho seed) by (unfold sigma;rewrite update_variable_neq by lia;reflexivity).
    assert (Sd:sigma k=dom) by (unfold sigma;apply update_variable_eq).
    rewrite Sh,Sn,Ss,Sd. split; [exact S|]. split; [exact P|]. split; [exact Z|].
    now apply (proj2 (run_edges_exists_iff _ _ P)).
Qed.
Theorem pair_run_formula_holds rho : FolHolds R rho pair_run_formula <-> exists h, RelPairStageRun R h (rho 2) (rho 3).
Proof.
  change (b_holds R rho (b_run_exists 2 3) 4 <-> exists h, RelPairStageRun R h (rho 2) (rho 3)).
  unfold b_run_exists. rewrite (b_holds_ex EM). split.
  - intros [h H]. rewrite stage_run_builder_holds in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. now exists h.
  - intros [h H]. exists h. rewrite stage_run_builder_holds by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
End Formula.
Print Assumptions pair_run_formula_holds.
Print Assumptions run_zero_holds.
Print Assumptions run_steps_holds.
Print Assumptions pair_run_formula_output_fresh.
Print Assumptions run_edge_holds.
