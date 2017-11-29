Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import CpdtTactics.
Require Import String.

Lemma sumList_single : forall {A : Set} (f : A -> Rat) (x : A), sumList (x :: nil) f == f x.
  unfold sumList; crush.
  rewrite <- ratAdd_0_l.
  crush.
  Qed.

Lemma sumList_nil : forall {A : Set} (f : A -> Rat), @sumList A nil f == 0.


  unfold sumList.
  crush.
  Qed.


Lemma sumList_swap : forall {A B : Set} (xs : list A) (ys : list B) f,
    sumList xs (fun x => sumList ys (fun y => f x y)) == sumList ys (fun y => sumList xs (fun x => f x y)).
  induction xs.
  induction ys.
  unfold sumList; crush.
  intros; repeat rewrite sumList_cons.
  repeat rewrite sumList_nil.
  rewrite <- ratAdd_0_l.
  apply eqRat_symm.
  apply sumList_0.
  intros; rewrite sumList_nil; crush.
  intros.
  induction ys.
  rewrite sumList_cons.
  rewrite IHxs.
  repeat rewrite sumList_nil.
  rattac.

  repeat rewrite sumList_cons.
  rewrite IHxs.
  repeat rewrite sumList_cons.
  rewrite <- IHys.
  repeat rewrite sumList_cons.
  generalize (f a a0) (sumList ys (fun y => f a y)) (sumList xs (fun x => f x a0)).
  intros.
  rewrite IHxs.
  generalize (sumList ys (fun y => sumList xs (fun x => f x y))).
  intros.
  rewrite ratAdd_assoc.
  rewrite ratAdd_assoc.
  apply ratAdd_eqRat_compat.
  crush.
  rewrite ratAdd_comm.
  rewrite ratAdd_assoc.
  apply ratAdd_eqRat_compat.
  crush.
  apply ratAdd_comm.
Qed.

Lemma getUnique_eq : forall {A : Set} (ls1 ls2 : list A) e1 e2, ls1 = ls2 -> getUnique ls1 e1 = getUnique ls2 e2.
  intros.
  subst.
  induction ls2.
  crush.
  simpl.

  destruct (in_dec e1 a (getUnique ls2 e1)).
  destruct (in_dec e2 a (getUnique ls2 e2)).
  auto.
  symmetry.
  pose proof (in_getUnique).
  apply in_getUnique_if in i.
  eapply in_getUnique in i.
  exfalso; apply (n i).
  destruct (in_dec e2 a (getUnique ls2 e2)).
  apply in_getUnique_if in i.
  eapply in_getUnique in i.
  exfalso; apply (n i).
  rewrite IHls2.
  auto.
Qed.

Lemma repeat_In : forall {A} (c : Comp A) (x : A) (p : A -> bool), In x (getSupport (Repeat c p)) -> p x = true.
  intros.
  simpl in H.
  pose proof (filter_In p x (getSupport c)).
  apply H0 in H.
  destruct H; auto.
Qed.

Instance string_EqDec : EqDec string.
apply dec_EqDec.
unfold eq_dec.
apply string_dec.
Qed.
