Add LoadPath "~/fcf/src".
Require Import Program FCF.FCF CpdtTactics.


Lemma sumList_single : forall {A : Set} (x:A) (f : A -> Rat), sumList (x :: nil) f == f x.
  unfold sumList; unfold fold_left; simpl.
  intros;
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  Qed.

Lemma unfold_repeat_true : forall {A : Set} (P : A -> bool) (C : Comp A) x, (P x) = true -> evalDist (Repeat C P) x == (evalDist C x) * ratInverse (sumList (filter P (getSupport C)) (evalDist C)).
  intros.
  crush.
  unfold indicator.
  crush.
  rewrite ratMult_comm.
  apply ratMult_eqRat_compat.
  apply eqRat_refl.
  rewrite ratMult_1_l.
  apply eqRat_refl.
Qed.

Lemma unfold_repeat_false : forall {A : Set} (P : A -> bool) (C : Comp A) x, (P x) = false -> evalDist (Repeat C P) x == 0.
  intros.
  crush; unfold indicator; crush;
    repeat rewrite ratMult_0_l; apply eqRat_refl.
  Qed.
 
Lemma repeat_in_support : forall {A : Set} (P : A -> bool) (C : Comp A) x, In x (getSupport (Repeat C P)) -> (P x) = true.
  intros.
  simpl in H.
  apply filter_In in H.
  crush.
Qed.


Definition negP {A : Set} (P : A -> bool) := fun x => negb (P x).

Definition cond_prob {A : Set} (C : Comp A) (P : A -> bool) := sumList (filter P (getSupport C)) (evalDist C).

Lemma cond_prob_Pr {A : Set} (C : Comp A) (P : A -> bool) : (cond_prob C P) == Pr [x <-$ C; ret ((P x) ?= true)].
  admit. (*calculation about filter *)
Admitted.


Lemma ratMult_comm_assoc_r : forall a b c, a * (b * c) == a * (c * b).
  intros;
  apply ratMult_eqRat_compat;
  [apply eqRat_refl |
  apply ratMult_comm].
Qed.

Lemma ratMult_comm_assoc_l : forall a b c, (a * b) * c == (b * a) * c.
  intros; apply ratMult_eqRat_compat;
  [apply ratMult_comm | apply eqRat_refl].
Qed.
                                                                     
Lemma repeat_split : forall {A : Set} (P : A -> bool) (C : Comp A), well_formed_comp (Repeat C P) -> well_formed_comp (Repeat C (negP P)) -> forall x, evalDist C x == (cond_prob C P) * (evalDist (Repeat C P) x) + (cond_prob C (negP P)) * (evalDist (Repeat C (negP P)) x).
  intros.
  crush.
  unfold indicator, negP, negb, cond_prob.
  destruct (P x);
  repeat rewrite ratMult_0_l;
  repeat rewrite ratMult_0_r;
  try rewrite <- ratAdd_0_r.
  rewrite ratMult_1_l.
  rewrite <- ratMult_assoc.
  rewrite ratMult_comm.
  rewrite ratMult_comm_assoc_r.
  rewrite ratInverse_prod_1.
  rewrite ratMult_1_r; apply eqRat_refl.
  admit. (* due to well formedness *)
  rewrite <- ratAdd_0_l.
  rewrite ratMult_1_l.
  rewrite <- ratMult_assoc.
  rewrite ratMult_comm.
  rewrite ratMult_comm_assoc_r.
  rewrite ratInverse_prod_1.
  rewrite ratMult_1_r; apply eqRat_refl.
  admit. (* due to well-formedness *)
Admitted.

Lemma filter_exists {A : Set} (l : list A) (P : A -> bool) : {l = nil} + {filter P l <> nil /\ ((filter (negP P) l) = nil)} + { filter P l = nil /\  (filter (negP P) l) <> nil } + {filter P l <> nil /\  (filter (negP P) l) <> nil}.
  induction l.
  left; left; left.
  auto.
  rewrite filter_cons.
  remember (P a) as b.
  assert (negP P a = negb b).
  unfold negP; rewrite Heqb; auto.
  unfold negb in H.
  rewrite filter_cons; rewrite H.


  destruct IHl.
  destruct s.
  destruct s.
  destruct b; subst.
  left; left; right; crush.
  unfold filter.
  left; right; crush.
  destruct b; subst.
  left; left; right; crush.
  right; crush.
  destruct b; subst.
  right; crush.
  left; right; crush.
  destruct b; subst.
  right; crush.
  right; crush.
Qed.



Lemma if_repeat_decomp_ {A B : Set} `{EqDec A} `{EqDec B} (C : Comp A) (C1 C2 : A -> Comp B) (P : A -> bool) : (forall x, well_formed_comp (C1 x)) -> (forall x, well_formed_comp (C2 x)) -> well_formed_comp (Repeat C P) -> well_formed_comp (Repeat C (fun n => negb (P n))) -> forall a a', evalDist (x <-$ C; y <-$ (if (P x) then C1 x else C2 x); ret (x,y)) (a, a') == (Pr [x <-$ C; ret (P x)]) * (evalDist (x <-$ Repeat C P; y <-$ C1 x; ret (x,y)) (a, a')) + (Pr [x <-$ C; ret (negb (P x))]) * (evalDist (x <-$ Repeat C (fun n => negb (P n)); y <-$ C2 x; ret (x,y)) (a, a')).
  intros.
  rewrite (repeat_split (fun p => (P (fst p)))).
  remember (P a) as b.
  destruct b.
  apply ratAdd_eqRat_compat.
  apply ratMult_eqRat_compat.
  rewrite cond_prob_Pr.
  fcf_inline leftc.
  comp_skip.
  fcf_inline leftc.
  remember (P x) as b; destruct b; subst.
  fcf_irr_l.
  simpl.
  admit.
  fcf_irr_l.
  simpl.
  admit.
  admit.

  apply ratMult_eqRat_compat.
  rewrite cond_prob_Pr.
  admit. (* similar *)

  admit.
  apply ratAdd_eqRat_compat.
  apply ratMult_eqRat_compat.
  admit.
  admit.
  apply ratMult_eqRat_compat.
  admit.
  admit.
  admit. (* from H1 and H2 *)
  admit. (* from H1 and H2 *)
Admitted.


Lemma if_repeat_decomp_both {A B : Set} `{EqDec A} `{EqDec B} (C : Comp A) (C1 C2 : A -> Comp B) (P : A -> bool) : (forall x, well_formed_comp (C1 x)) -> (forall x, well_formed_comp (C2 x)) -> well_formed_comp (Repeat C P) -> well_formed_comp (Repeat C (fun n => negb (P n))) -> forall a, evalDist (x <-$ C; (if (P x) then C1 x else C2 x)) a == (Pr [x <-$ C; ret (P x)]) * (evalDist (x <-$ Repeat C P; C1 x) a) + (Pr [x <-$ C; ret (negb (P x))]) * (evalDist (x <-$ Repeat C (fun n => negb (P n)); C2 x) a).
  admit. (* follows from above *)
Admitted.

Lemma if_repeat_decomp_l {A B : Set} `{EqDec A} `{EqDec B} (C : Comp A) (C1 C2 : A -> Comp B) (P : A -> bool) : (forall x, well_formed_comp (C1 x)) -> well_formed_comp (Repeat C P) -> (cond_prob C (negP P)) == 0 -> forall a, evalDist (x <-$ C; (if (P x) then C1 x else C2 x)) a == (evalDist (x <-$ Repeat C P; C1 x) a) .
  admit.
  (* using unfold_repeat_true / false *)
Admitted.

Lemma if_repeat_decomp_r {A B : Set} `{EqDec A} `{EqDec B} (C : Comp A) (C1 C2 : A -> Comp B) (P : A -> bool) : (forall x, well_formed_comp (C1 x)) -> well_formed_comp (Repeat C (negP P)) -> (cond_prob C P) == 0 -> forall a, evalDist (x <-$ C; (if (P x) then C1 x else C2 x)) a == (evalDist (x <-$ Repeat C (negP P); C2 x) a) .
  admit.
Admitted.