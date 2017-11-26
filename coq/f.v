(* NOTE: the issue with the below proofs is that the original bexp's are being evaluated *before* running all commands, and the sym exec bexp's are being evaluated *after* running all commands. For commands which shadow, or evaluate to defaults, this will cause a discrepancy. I want to actually capture statements about states which are stable after forward execution. 

This means I will have to modify the semantics of bexp's and so on to return error if variable is not found. Variables will not be able to be overwritten.

*)


Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import Bool Arith String List CpdtTactics Program.
Open Scope string_scope.
Require FcfLems.

Ltac inv e := remember e as p; destruct p; subst.

Ltac uf e := unfold e; fold e.

Ltac destruct_eq Y Z := match goal with
                    | [ |- context[EqDec_dec ?X Y Z]] => edestruct (EqDec_dec _ Y Z)
                    end.

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.


Definition state := list (var * nat).


Fixpoint get (x:var) (s:state) : option nat :=
  match s with
  | nil => None
  | (x', v)::s' => match string_dec x x' with
                   | left _ => Some v
                   | right _ => get x s'
                   end
  end.

Definition in_state (x : var) (s : state) :=
  match (get x s) with
  | Some _ => true
  | None => false
  end.


(* set does not overwrite variables. *)
Fixpoint set (x:var) (n:nat) (s:state) : state :=
  match s with
    | nil => (x,n) :: nil
    | (x', n') :: s' => if string_dec x x' then (x',n') :: s' else (x',n') :: (set x n s')
  end.


Lemma get_set : forall x s v v', get x s = Some v -> set x v' s = s.
induction s.
crush.
simpl.
destruct a.
intros.
destruct (string_dec x v).
auto.
rewrite (IHs v0 v' H).
auto.
Qed.

(* We map binary operator expressions to underlying Coq
   operators on nat. *)

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
  end.

(* The implementations of eval_aexp and eval_bexp are
   recursive translations into Coq terms. *)

Fixpoint eval_aexp (e:aexp) (s:state) : option nat := 
  match e with 
    | Const n => Some n
    | Var x => match (get x s) with
               | Some v => Some v
               | None => None
               end
    | Binop e1 b e2 =>
      match (eval_aexp e1 s, eval_aexp e2 s) with
      | (Some x, Some y) => Some (eval_binop b x y)
      | _ => None
      end
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : option bool := 
  match b with 
    | Tt => Some true
    | Ff => Some false
    | Eq e1 e2 =>
      match (eval_aexp e1 s, eval_aexp e2 s) with
      | (Some x, Some y) => Some (Nat.eqb x y)
      | _ => None
      end
    | Lt e1 e2 => 
      match (eval_aexp e1 s, eval_aexp e2 s) with
      | (Some x, Some y) => Some (Nat.ltb x y)
      | _ => None
      end
    | And b1 b2 => 
      match (eval_bexp b1 s, eval_bexp b2 s) with
      | (Some x, Some y) => Some (andb x y)
      | _ => None
      end
    | Or b1 b2 => 
      match (eval_bexp b1 s, eval_bexp b2 s) with
      | (Some x, Some y) => Some (orb x y)
      | _ => None
      end
    | Not b => 
                    match (eval_bexp b s) with
                    | Some x => Some (negb x)
                    | _ => None
                    end
  end.

Lemma eval_aexp_set_stable : forall a s x v n, eval_aexp a s = Some n -> eval_aexp a (set x v s) = Some n.
  induction a; uf eval_aexp.
  crush.
  intros.
  remember (get v s) as p; destruct p.
  symmetry in Heqp.
  induction s.
  crush.
  simpl.
  destruct a.
  destruct (string_dec x v1); crush.
  destruct (string_dec v v1); crush.
  inversion H.

  intros.
  remember (eval_aexp a1 s) as p1; destruct p1.
  remember (eval_aexp a2 s) as p2; destruct p2.
  erewrite IHa1.
  erewrite IHa2.
  apply H.
  crush.
  crush.
  inversion H.
  inversion H.
Qed.

Lemma eval_bexp_set_stable : forall b s x v b', eval_bexp b s = Some b' -> eval_bexp b (set x v s) = Some b'.
  induction b.
  crush.
  crush.
  uf eval_bexp.
  intros.
  remember (eval_aexp a s) as p; destruct p.
  remember (eval_aexp a0 s) as p'; destruct p'.
  erewrite eval_aexp_set_stable.
  erewrite eval_aexp_set_stable.
  crush.
  crush.
  crush.
  crush.
  crush.

  uf eval_bexp.
  intros.
  remember (eval_aexp a s) as p; destruct p.
  remember (eval_aexp a0 s) as p'; destruct p'.
  erewrite eval_aexp_set_stable.
  erewrite eval_aexp_set_stable.
  crush.
  crush.
  crush.
  crush.
  crush.

  uf eval_bexp.
  intros.
  remember (eval_bexp b1 s) as p; destruct p.
  remember (eval_bexp b2 s) as p'; destruct p'.
  erewrite IHb1.
  erewrite IHb2.
  crush.
  crush.
  crush.
  crush.
  crush.

  uf eval_bexp.
  intros.
  remember (eval_bexp b1 s) as p; destruct p.
  remember (eval_bexp b2 s) as p'; destruct p'.
  erewrite IHb1.
  erewrite IHb2.
  crush.
  crush.
  crush.
  crush.
  crush.
  uf eval_bexp.
  intros.
  remember (eval_bexp b s) as p; destruct p.
  erewrite IHb.
  crush.
  crush.
  crush.
Qed.
(* TODO: show that if eval_bexp b s = Some b', then when s takes a step in either the first or second language to s', eval_bexp b s' = Some b'. This is true, due to that set does not overwrite variables.*)


Definition eval_bexp_true (b : bexp) (s : state) :=
  match (eval_bexp b s) with
  | Some true => true
  | _ => false
  end.

Lemma bexp_and_given : forall s b1 b2, eval_bexp b1 s = Some true -> (eval_bexp b2 s = eval_bexp (And b1 b2) s).
intros.
uf eval_bexp.
unfold andb.
rewrite H.
destruct (eval_bexp b2 s); crush.
Qed.

Lemma bexp_and_given_neq : forall s b1 b2, eval_bexp b1 s <> Some true -> eval_bexp (And b1 b2) s <> Some true.
intros.
uf eval_bexp.
destruct (eval_bexp b1 s).
destruct b.
contradiction.
destruct (eval_bexp b2 s).
unfold andb.
auto.
crush.
crush.
Qed.


Definition distr := string.
Definition distr_state := distr -> Comp nat.

Definition wf_distr_state (ds : distr_state) := forall x, well_formed_comp (ds x).

Definition get_d (x:distr) (s:distr_state) : Comp nat := s x.

Definition set_d (x:distr) (n:Comp nat) (s:distr_state) : distr_state := 
  fun y => 
    match string_dec x y with 
        | left H => n 
        | right H' => get_d y s
    end.


Inductive com : Type :=
| Sampl : var -> distr -> com -> com
| If : bexp -> com -> com -> com
| Skip : com.

Inductive cond_com : Type :=
| CondSampl : var -> distr -> cond_com -> cond_com
| CondSkip : cond_com.



Fixpoint sym_exec (c : com) : list (cond_com *  bexp) :=
  match c with
  | Sampl v d k =>
    map (fun p => (CondSampl v d (fst p), snd p)) (sym_exec k)
  | If b c1 c2 =>
    (map (fun p => (fst p, And b (snd p))) (sym_exec c1)) ++ (map (fun p => (fst p, And (Not b) (snd p))) (sym_exec c2))
  | Skip => (CondSkip, Tt) :: nil
  end.

Theorem sym_exec_neq_nil : forall c, sym_exec c <> [].
  induction c.
  unfold sym_exec; fold sym_exec.
  intro H; apply map_eq_nil in H.
  crush.

  unfold sym_exec; fold sym_exec.
  intro H; apply app_eq_nil in H.
  destruct H as [H1 H2]; apply map_eq_nil in H1; crush.
  crush.
Qed.

Lemma repeat_In : forall {A} (c : Comp A) (x : A) (p : A -> bool), In x (getSupport (Repeat c p)) -> p x = true.
  intros.
  simpl in H.
  pose proof (filter_In p x (getSupport c)).
  apply H0 in H.
  destruct H; auto.
Qed.


Ltac repeat_inv := match goal with
                   | [H : In ?x (getSupport (Repeat ?c ?p)) |- _] => apply repeat_In in H
                   end.

Ltac myrem e := remember e; destruct e; subst.


Instance string_EqDec : EqDec string.
apply dec_EqDec.
unfold eq_dec.
apply string_dec.
Qed.

Fixpoint fcf_trans (c : com) (ds : distr_state) (s : state) : Comp (option state) :=
  match c with
  | Sampl v d k => 
     x <-$ (get_d d ds);
     fcf_trans k ds (set v x s)
  | If b c1 c2 =>
    match (eval_bexp b s) with
    | Some true => fcf_trans c1 ds s
    | Some false => fcf_trans c2 ds s
    | _ => ret None
    end
  | Skip => (ret (Some s))
  end.

Lemma wfcomp_trans : forall c ds sc, (forall x, well_formed_comp (ds x)) -> well_formed_comp (fcf_trans c ds sc).
induction c; unfold get_d; simpl; wftac.
intros;
destruct (eval_bexp b sc); wftac.
Qed.

Notation "d1 ~~ d2" := (forall x, d1 x == d2 x) (at level 80).

Fixpoint fcf_leaftrans (c : cond_com) (ds : distr_state) (s : state) : Comp state :=
  match c with
  | CondSampl v d k =>
      x <-$ (get_d d ds);
      fcf_leaftrans k ds (set v x s)
  | CondSkip => ret s
  end.

Lemma wfcomp_leaftrans: forall c ds s, (forall x, well_formed_comp (ds x)) -> well_formed_comp (fcf_leaftrans c ds s).
  induction c; unfold get_d; simpl; wftac.
Qed.

Lemma leaftrans_bexp_stable : forall c ds s x b b', eval_bexp b s = Some b' -> In x (getSupport (fcf_leaftrans c ds s)) -> eval_bexp b x = Some b'.
    induction c; intros.
    simpl in H0.
    apply in_getUnique_if in H0.
    apply in_flatten in H0.
    destruct H0.
    destruct H0.
    apply in_map_iff in H0.
    destruct H0.
    destruct H0.
    subst.
    eapply IHc.
    eapply (eval_bexp_set_stable _ _ _ _ _ H).
    apply H1.
    inversion H0; subst.
    auto.
    inversion H1.
Qed.


    



Definition condition {A : Set} (p : A -> bool) (sc : Comp A) := Repeat sc p.

Definition leaf_prob (ds : distr_state) (leaf : cond_com * bexp) (s' : state) := Pr[s <-$ fcf_leaftrans (fst leaf) ds s'; ret (eval_bexp_true (snd leaf) s)].

Definition leaf_condition (ds : distr_state) (leaf : cond_com * bexp) (c : state) := condition (eval_bexp_true (snd leaf)) (fcf_leaftrans (fst leaf) ds c).

Definition leaf_val (ds : distr_state) (x : state) (c : state) leaf  :=
  (leaf_prob ds leaf c) * (evalDist (leaf_condition ds leaf c) x).


Definition fcf_condtrans (leaves : list (cond_com * bexp)) ds (s : state) : Distribution state := fun x =>
  sumList leaves (leaf_val ds x s).

Lemma fcf_condtrans_cons : forall l ls ds s x, fcf_condtrans (l :: ls) ds s x == leaf_val ds x s l + fcf_condtrans ls ds s x.
  uf fcf_condtrans.
  intros;
  rewrite sumList_cons.
  crush.
  Qed.

Lemma fcf_condtrans_app : forall l1 l2 ds s x, fcf_condtrans (l1 ++ l2) ds s x == (fcf_condtrans l1 ds s x) + (fcf_condtrans l2 ds s x).
  crush.
  uf fcf_condtrans.
  rewrite sumList_app.
  crush.
  Qed.


Lemma filter_ext_cond : forall {A : Set} {eqa : eq_dec A} (p1 p2 : A -> bool) (xs : list A), (forall x, In x xs -> p1 x = p2 x) -> filter p1 xs = filter p2 xs.
  induction xs.
  crush.
  simpl.
  intros.
  destruct (H a).
  crush.
  cut (filter p1 xs = filter p2 xs).
  intro H2; rewrite H2; crush.
  apply IHxs.
  intros.
  apply (H x).
  right; crush.
Qed.  

Lemma evalDist_repeat_equiv : forall {A : Set} (eqa : eq_dec A) (c : Comp A) (p1 p2 : A -> bool),
    (forall x, In x (getSupport c) -> (p1 x = p2 x)) -> forall x, evalDist (Repeat c p1) x == evalDist (Repeat c p2) x.
  crush.
  destruct (In_dec eqa x (getSupport c)).
  apply ratMult_eqRat_compat.
  apply ratMult_eqRat_compat.
  unfold indicator.
  rewrite (H _ i).
  crush.
  erewrite filter_ext_cond.
  apply eqRat_refl.
  apply H.
  crush.

  rewrite (getSupport_not_In_evalDist_h).
  rewrite ratMult_0_r.
  rewrite ratMult_0_r.
  crush.
  crush.
  Unshelve.
  auto.
Qed.

Lemma eval_bexp_true_and : forall b1 b2 s, eval_bexp_true (And b1 b2) s = true <-> (eval_bexp_true b1 s = true ) /\ (eval_bexp_true b2 s = true).
  intros.
  split.
  intros.
  unfold eval_bexp_true in H; fold eval_bexp_true in H.
  remember (eval_bexp (And b1 b2) s) as p; destruct p.
  destruct b.
  unfold eval_bexp in Heqp; fold eval_bexp in Heqp.
  inv (eval_bexp b1 s).
  inv (eval_bexp b2 s).
  crush.
  unfold andb in H0.
  destruct b; destruct b0.
  crush.
  uf eval_bexp_true.
  rewrite <- Heqp0.
  crush.
  crush.
  crush.
  crush.
  uf eval_bexp_true.
  destruct b; destruct b0.
  rewrite <- Heqp1.
  crush.
  simpl in H0; crush.
  simpl in H0; crush.
  simpl in H0; crush.
  crush.
  crush.
  crush.
  crush.

  intros.
  uf eval_bexp_true.
  uf eval_bexp.
  destruct H.
  unfold eval_bexp_true in H.
  inv (eval_bexp b1 s).
  inv b.
  inv (eval_bexp b2 s).
  inv b.
  crush.
  unfold eval_bexp_true in H0.
  rewrite <- Heqp0 in H0.
  crush.
  unfold eval_bexp_true in H0.
  rewrite <- Heqp0 in H0.
  crush.
  crush.
  crush.
Qed.

Lemma fcf_condtrans_true_equiv : forall ls ds s b x, eval_bexp b s = Some true ->
  fcf_condtrans (map (fun p : cond_com * bexp => (fst p, And b (snd p))) (ls)) ds s x
  == fcf_condtrans (ls) ds s x.
  intros.
  unfold fcf_condtrans.
  rewrite sumList_map.
  apply sumList_body_eq.
  intros.
  uf leaf_val.
  uf leaf_prob.
  apply ratMult_eqRat_compat.
  unfold fst.
  destruct a.
  comp_skip.
  assert (eval_bexp (And b b0) x0 = eval_bexp b0 x0).
  symmetry.
  apply bexp_and_given.
  eapply leaftrans_bexp_stable.
  apply H.
  apply H1.
  uf eval_bexp_true.
  unfold snd.
  rewrite H2.
  crush.
  uf leaf_condition.
  unfold condition.
  unfold fst, snd.
  destruct a.
  apply evalDist_repeat_equiv.
  unfold eq_dec.
  repeat decide equality.
  intros.
  uf eval_bexp_true.
  assert (eval_bexp (And b b0) x0 = eval_bexp b0 x0).
  symmetry.
  apply bexp_and_given.
  eapply leaftrans_bexp_stable.
  apply H.
  apply H1.
  rewrite H2.
  crush.
  Qed.

Lemma fcf_condtrans_false_0 : forall ls ds s b x, (forall x, well_formed_comp (ds x)) -> eval_bexp b s = Some false ->
  fcf_condtrans (map (fun p : cond_com * bexp => (fst p, And b (snd p))) (ls)) ds s x
  == 0.
  intros.
  uf fcf_condtrans.
  uf sumList; crush.
  induction ls.
  crush.
  rewrite map_cons.
  simpl.
  rewrite fold_add_body_eq.
  apply IHls.
  uf leaf_val.
  destruct a.
  uf leaf_prob.
  rewrite <- ratAdd_0_l.
  apply ratMult_0.

  left.
  unfold fst, snd.
  fcf_irr_l.
  apply wfcomp_leaftrans.
  apply H.
  crush.
  cut (eval_bexp (And b b0) x0 <> Some true).
  intros H3.
  unfold eval_bexp_true.
  destruct (eval_bexp (And b b0) x0).
  destruct b1.
  contradiction.
  destruct (EqDec_dec bool_EqDec false true).
  inversion e.
  crush.
  destruct (EqDec_dec bool_EqDec false true).
  inversion e.
  crush.
  cut (eval_bexp b x0 = Some false).
  intros.
  uf eval_bexp.
  rewrite H2.
  destruct (eval_bexp b0 x0).
  crush.
  crush.
  eapply leaftrans_bexp_stable.
  apply H0.
  apply H1.
  intros.
  crush.
Qed.
  

Lemma ret_true_1 : forall {A : Set} (C : Comp A), well_formed_comp C -> Pr [_ <-$ C; ret true] == 1.
  intros; fcf_irr_l.
  dist_compute.
Qed.

Lemma filter_tr : forall {A : Set} (l : list A), filter (fun _ => true) l = l.
  induction l; crush.
Qed.


Lemma repeat_true : forall {A : Set} (C : Comp A), well_formed_comp C -> (evalDist C) ~~ (evalDist (Repeat C (fun _ => true))).
  intros.
  pose proof (evalDist_lossless H).
  rewrite FcfLems.unfold_repeat_true.
  rewrite filter_tr.
  rewrite <- ratMult_1_r.
  apply ratMult_eqRat_compat.
  rewrite ratMult_1_r; apply eqRat_refl.
  rewrite ratInverse_eqRat_compat.
  rewrite ratInverse_1.
  rattac.
  rewrite H0; rattac.
  apply H0.
  auto.
Qed.

Theorem fold_eq_init : forall {B} (xs : list B) (f : Rat -> B -> Rat) (i1 i2 : Rat), i1 == i2 -> (forall x1 x2 b, x1 == x2 -> f x1 b == f x2 b) -> fold_left f xs i1 == fold_left f xs i2.
  induction xs.
  crush.
  simpl.
  intros.
  apply IHxs.
  apply H0.
  crush.
  crush.
Qed.

Axiom distLift : forall {A : Set} (d : Distribution A), Comp A.
Axiom distLift_eq : forall {A : Set} (d : Distribution A), d ~~ (evalDist (distLift d)).


Check fcf_trans.
Check fcf_condtrans.

Fixpoint wf_bexps (c : com) (s : state) :=
  match c with
  | Sampl x d k =>
    wf_bexps k (set x 0 s)%nat
  | If b c1 c2 =>
    eval_bexp b s <> None /\ wf_bexps c1 s /\ wf_bexps c2 s
  | Skip => True
  end.

(* todo: finish. sampl case should go through. skip case should go through. then, just complete the needed admits. *)

Theorem mainTheorem (ds : distr_state) (c : com) : forall s x, wf_bexps c s -> wf_distr_state ds -> (evalDist (fcf_trans c ds s) (Some x)) == fcf_condtrans (sym_exec c) ds s x.
  induction c; intros s x wfb H.
  uf fcf_trans.

(*
  cut (evalDist (x0 <-$ get_d d ds; fcf_trans c ds (set v x0 s)) ~~
       evalDist (x0 <-$ get_d d ds; distLift (fcf_condtrans (sym_exec c) ds (set v x0 s)))).
  intros H0; rewrite H0; clear H0.
  crush.
  generalize (sym_exec c) as p.
  induction p.
  crush.
  unfold fcf_condtrans.
  uf sumList.
  simpl.
  admit. (* easy *)
  simpl.
  rewrite fcf_condtrans_cons.
  rewrite <- IHp.
  cut ( sumList (getSupport (get_d d ds))
    (fun b : nat =>
       evalDist (get_d d ds) b * evalDist (distLift (fcf_condtrans (a :: p) ds (set v b s))) x)
        ==
         sumList (getSupport (get_d d ds))
    (fun b : nat =>
     evalDist (get_d d ds) b * (leaf_val ds x (set v b s) a + evalDist (distLift (fcf_condtrans (p) ds (set v b s))) x))).
  intros.
  rewrite H0; clear H0.
  clear IHp.
  admit. (* arithmetic i think is correct *)
  apply sumList_body_eq.
  intros.
  apply ratMult_eqRat_compat.
  crush.
  rewrite <- distLift_eq.
  rewrite fcf_condtrans_cons.
  rewrite <- distLift_eq.
  crush.
  intros.
  comp_skip.
  rewrite <- distLift_eq.
  apply IHc.
  wftac.
 *)
 admit. 

  (* if case *)
  uf sym_exec.
  rewrite fcf_condtrans_app.
  uf fcf_trans.
  remember (eval_bexp b s) as p.
  destruct p.
  symmetry in Heqp.
  destruct b0.
  pose proof (fcf_condtrans_true_equiv (sym_exec c1) ds _ _ x Heqp).
  rewrite H0.
  assert (eval_bexp (Not b) s = Some false).
  uf eval_bexp; crush.
  pose proof (fcf_condtrans_false_0 (sym_exec c2) ds _ _ x H H1).
  rewrite H2.
  rewrite <- ratAdd_0_r.
  eapply IHc1.
  crush.
  crush.
  
  (* same as above *)

  rewrite (fcf_condtrans_false_0 (sym_exec c1) ds _ _ x H Heqp).
  assert (eval_bexp (Not b) s = Some true).
  crush.
  rewrite (fcf_condtrans_true_equiv (sym_exec c2) ds _ _ x H0).
  rewrite IHc2.
  rewrite <- ratAdd_0_l.
  crush.
  crush.
  crush.

  (* bexp is well formed, so this case is impossible *)
  unfold wf_bexps in wfb; fold wf_bexps in wfb.
  destruct wfb.
  symmetry in Heqp.
  contradiction.

  (* skip case *)
  intros.
  crush.
  unfold fcf_condtrans.
  unfold sumList.
  simpl.
  unfold leaf_val.
  unfold leaf_prob.
  unfold leaf_condition.
  unfold condition.
  unfold fst, snd.
  unfold eval_bexp_true.
  unfold eval_bexp.
  rewrite ret_true_1.
  rewrite <- repeat_true.
  unfold fcf_leaftrans.
  unfold evalDist.
  rewrite <- ratAdd_0_l.
  rewrite ratMult_1_l.
  destruct_eq s x.
  subst.
  destruct_eq (Some x) (Some x).
  crush.
  contradiction.
  destruct_eq (Some s) (Some x).
  injection e; intros.
  contradiction.
  crush.
  unfold fcf_leaftrans; wftac.
  unfold fcf_leaftrans; wftac.

Admitted.

  

  



Definition leaf_feasible (ds : distr_state) (l : cond_com * (list bexp)) := bexp_feasible (bexp_and (snd l)) (fcf_leaftrans (fst l) ds).


Definition bexp_feasible (b : bexp) (sc : Comp state) := well_formed_comp (Repeat sc (eval_bexp b)).

Definition nonzero_dec (sc : Comp state) := forall (b : bexp), {Pr[ x <-$ sc; ret (eval_bexp b x)] == 0} + { ~ (Pr [x <-$ sc; ret (negb (eval_bexp b x))] == 0) }.