(** Finite syntax for formula trees, environments, Tarski recursion, and
    elementarity of a set-sized membership structure. *)
From Berkeley Require Import BerkeleySyntaxBase.

Definition b_closed_formulas f w te tm tn ti ta := b_and5
  (b_ain w (fun u => b_ain w (fun v => b_ein f (fun p => b_node2 p te u v))))
  (b_ain w (fun u => b_ain w (fun v => b_ein f (fun p => b_node2 p tm u v))))
  (b_ain f (fun p => b_ein f (fun q => b_pair q tn p)))
  (b_ain f (fun p => b_ain f (fun q => b_ein f (fun r => b_node2 r ti p q))))
  (b_ain w (fun u => b_ain f (fun p => b_ein f (fun q => b_node2 q ta u p)))).

Definition b_formulas f w te tm tn ti ta := b_and
  (b_closed_formulas f w te tm tn ti ta)
  (b_all (fun g => b_imp (b_closed_formulas g w te tm tn ti ta) (b_subset f g))).

Definition b_environments e w m := b_all (fun s => b_iff (b_mem s e) (b_function s w m)).
Definition b_update s t u w m :=
  b_ain w (fun v => b_or (b_eq v u)
    (b_ain m (fun x => b_iff (b_rel s v x) (b_rel t v x)))).

Definition b_satisfaction sat e f w m te tm tn ti ta := b_ain e (fun s => b_and5
  (b_ain w (fun u => b_ain w (fun v => b_ain m (fun x => b_ain m (fun y => b_all (fun p =>
    b_imp (b_and3 (b_rel s u x) (b_rel s v y) (b_node2 p te u v))
      (b_iff (b_rel sat p s) (b_eq x y))))))))
  (b_ain w (fun u => b_ain w (fun v => b_ain m (fun x => b_ain m (fun y => b_all (fun p =>
    b_imp (b_and3 (b_rel s u x) (b_rel s v y) (b_node2 p tm u v))
      (b_iff (b_rel sat p s) (b_mem x y))))))))
  (b_ain f (fun p => b_all (fun q => b_imp (b_pair q tn p)
    (b_iff (b_rel sat q s) (b_not (b_rel sat p s))))))
  (b_ain f (fun p => b_ain f (fun q => b_all (fun r => b_imp (b_node2 r ti p q)
    (b_iff (b_rel sat r s) (b_imp (b_rel sat p s) (b_rel sat q s)))))))
  (b_ain w (fun u => b_ain f (fun p => b_all (fun q => b_imp (b_node2 q ta u p)
    (b_iff (b_rel sat q s) (b_ain e (fun t => b_imp (b_update s t u w m) (b_rel sat p t))))))))).

Definition b_image_environment j s t w m :=
  b_ain w (fun u => b_ain m (fun x => b_ain m (fun y =>
    b_imp (b_and (b_rel s u x) (b_rel j x y)) (b_rel t u y)))).

Definition b_elementary j m e f w sat := b_and (b_function j m m)
  (b_ain f (fun p => b_ain e (fun s => b_ain e (fun t =>
    b_imp (b_image_environment j s t w m)
      (b_iff (b_rel sat p s) (b_rel sat p t)))))).
