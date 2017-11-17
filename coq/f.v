Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.

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

Definition bexp_and (b : list bexp) := fold_left (fun acc x => And acc x) b Tt.

Definition state := list (var * nat).


Fixpoint get (x:var) (s:state) : option nat :=
  match s with
  | nil => None
  | (x', v)::s' => match string_dec x x' with
                   | left _ => Some v
                   | right _ => get x s'
                   end
  end.

Fixpoint set (x:var) (n:nat) (s:state) : state := (x,n) :: s.

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

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => match (get x s) with
               | Some v => v
               | None => 0
               end
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => Nat.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

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
| Sampl : var -> distr -> com
| If : bexp -> com -> com -> com
| Seq : com -> com -> com
| Skip : com.

Inductive cond_com : Type :=
| CondSampl : var -> distr -> cond_com
| CondSeq : cond_com -> cond_com -> cond_com
| CondSkip : cond_com.


Fixpoint sym_exec (c : com) : list (cond_com * list bexp) :=
  match c with
  | Sampl v d => (CondSampl v d, nil) :: nil
  | If b c1 c2 =>
    let cs1 := sym_exec c1 in
    let cs2 := sym_exec c2 in
    (map (fun p => (fst p, b :: snd p)) cs1) ++ (map (fun p => (fst p, (Not b) :: snd p)) cs2)
  | Seq c1 c2 =>
    let cs1 := sym_exec c1 in
    let cs2 := sym_exec c2 in
    flatten (map (fun (p : cond_com * list bexp) => let (ca, ba) := p in map (fun (p2 : cond_com * list bexp) => let (cb, bb) := p2 in (CondSeq ca cb, app ba bb)) cs2) cs1)
  | Skip => (CondSkip, nil) :: nil
  end.

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

Fixpoint fcf_trans_ (c : com) (ds : distr_state) (sc : Comp state) : Comp state :=
  match c with
  | Sampl v d => 
     s <-$ sc;
     x <-$ (get_d d ds);
     ret (set v x s)
  | If b c1 c2 =>
    s <-$ sc;
    match (eval_bexp b s) with
    | true => fcf_trans_ c1 ds sc
    | false => fcf_trans_ c2 ds sc
    end
  | Seq c1 c2 =>
    fcf_trans_ c2 ds (fcf_trans_ c1 ds sc)
  | Skip => sc
  end.

Lemma wfcomp_trans : forall c ds sc, well_formed_comp sc -> (forall x, well_formed_comp (ds x)) -> well_formed_comp (fcf_trans_ c ds sc).
induction c; unfold get_d; simpl; wftac.
Qed.


Definition fcf_trans c ds := fcf_trans_ c ds (ret nil).
Notation "d1 ~~ d2" := (forall x, d1 x == d2 x) (at level 80).




Fixpoint fcf_leaftrans_ (c : cond_com) (ds : distr_state) (sc : Comp state) : Comp state :=
  match c with
  | CondSampl v d =>
    s <-$ sc;
      x <-$ (get_d d ds);
      ret (set v x s)
  | CondSeq c1 c2 =>
    fcf_leaftrans_ c2 ds (fcf_leaftrans_ c1 ds sc)
  | CondSkip => sc
  end.

Definition condition {A : Set} (p : A -> bool) (sc : Comp A) := Repeat sc p.

Definition fcf_leaftrans c ds := fcf_leaftrans_ c ds (ret nil).

Definition leaf_prob (ds : distr_state) (leaf : cond_com * (list bexp)) := Pr[s <-$ fcf_leaftrans (fst leaf) ds; ret eval_bexp (bexp_and (snd leaf)) s].

Definition leaf_condition (ds : distr_state) (leaf : cond_com * (list bexp)) := condition (eval_bexp (bexp_and (snd leaf))) (fcf_leaftrans (fst leaf) ds).


Definition fcf_condtrans (ds : distr_state) (leaves : list (cond_com * (list bexp))) : Distribution state := fun x =>
  sumList leaves (fun leaf => (leaf_prob ds leaf) * (evalDist (leaf_condition ds leaf) x)).

Lemma sumList_single : forall {A : Set} (x:A) (f : A -> Rat), sumList (x :: nil) f == f x.
  unfold sumList; unfold fold_left; simpl.
  intros;
  rewrite <- ratAdd_0_l.
  apply eqRat_refl.
  Qed.


Lemma ret_true_1 : forall {A : Set} (C : Comp A), well_formed_comp C -> Pr [_ <-$ C; ret true] == 1.
  intros; fcf_irr_l.
  dist_compute.
Qed.

Lemma filter_tr : forall {A : Set} (l : list A), filter (fun _ => true) l = l.
  induction l; crush.
Qed.


Lemma repeat_true : forall {A : Set} (C : Comp A), well_formed_comp C -> (evalDist C) ~~ (evalDist (Repeat C (fun _ => true))).
  simpl.
  intros.
  unfold indicator.
  rewrite filter_tr.
  cut ( ratInverse (sumList (getSupport C) (evalDist C))  == 1).
  intros.
  rewrite H0.
  repeat rewrite ratMult_1_l.
  rattac.
  rewrite (@ratInverse_eqRat_compat _ 1).
  unfold ratInverse.
  simpl.
  apply eqRat_refl.
  rewrite evalDist_lossless.
  rattac.
  wftac.
  rewrite evalDist_lossless.
  rattac.
  wftac.
Qed.


Theorem mainTheorem (ds : distr_state) (c : com) : wf_distr_state ds -> (evalDist (fcf_trans c ds)) ~~ fcf_condtrans ds (sym_exec c).
  intros; simpl.

  (* sampl case *)
  induction c.
  unfold sym_exec.
  unfold fcf_condtrans.
  rewrite sumList_single.
  unfold leaf_prob.
  unfold snd.
  unfold fst.
  unfold bexp_and; unfold fold_left.
  unfold eval_bexp.
  rewrite ret_true_1.
  rewrite ratMult_1_l.
  unfold leaf_condition.
  unfold snd.
  unfold bexp_and.
  unfold fold_left.
  unfold eval_bexp.
  unfold fst.
  unfold fcf_leaftrans.
  unfold fcf_leaftrans_.
  unfold condition.
  rewrite repeat_true.
  unfold fcf_trans.
  unfold fcf_trans_.
  apply eqRat_refl.
  unfold fcf_leaftrans.
  unfold fcf_leaftrans_.
  wftac.
  unfold fcf_trans.
  apply wfcomp_trans.
  wftac.
  apply H.
  unfold fcf_leaftrans.
  unfold fcf_leaftrans_.
  wftac.

  unfold fcf_trans, fcf_trans_.
  fcf_irr_l.
  wftac.
  inversion H0; subst.
  fold fcf_trans_.
  fold fcf_trans.
  remember (eval_bexp b nil) as p.
  unfold sym_exec.
  fold sym_exec.
  unfold fcf_condtrans.
  rewrite Fold.sumList_app.
  destruct p.
  rewrite IHc1.
  fold fcf_condtrans.
  unfold fcf_condtrans in IHc1.
  unfold leaf_prob.
  
  
  





  

  



Definition leaf_feasible (ds : distr_state) (l : cond_com * (list bexp)) := bexp_feasible (bexp_and (snd l)) (fcf_leaftrans (fst l) ds).


Definition bexp_feasible (b : bexp) (sc : Comp state) := well_formed_comp (Repeat sc (eval_bexp b)).

Definition nonzero_dec (sc : Comp state) := forall (b : bexp), {Pr[ x <-$ sc; ret (eval_bexp b x)] == 0} + { ~ (Pr [x <-$ sc; ret (negb (eval_bexp b x))] == 0) }.