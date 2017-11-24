Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import Bool Arith String List CpdtTactics Program.
Open Scope string_scope.
Require FcfLems.

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
| Sampl : var -> distr -> com -> com
| If : bexp -> com -> com -> com
| Skip : com.

Inductive cond_com : Type :=
| CondSampl : var -> distr -> cond_com -> cond_com
| CondSkip : cond_com.


Fixpoint sym_exec (c : com) : list (cond_com * list bexp) :=
  match c with
  | Sampl v d k =>
    map (fun p => (CondSampl v d (fst p), snd p)) (sym_exec k)
  | If b c1 c2 =>
    (map (fun p => (fst p, b :: snd p)) (sym_exec c1)) ++ (map (fun p => (fst p, (Not b) :: snd p)) (sym_exec c2))
  | Skip => (CondSkip, nil) :: nil
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

Fixpoint fcf_trans (c : com) (ds : distr_state) (s : state) : Comp state :=
  match c with
  | Sampl v d k => 
     x <-$ (get_d d ds);
     fcf_trans k ds (set v x s)
  | If b c1 c2 =>
    match (eval_bexp b s) with
    | true => fcf_trans c1 ds s
    | false => fcf_trans c2 ds s
    end
  | Skip => ret s
  end.

Lemma wfcomp_trans : forall c ds sc, (forall x, well_formed_comp (ds x)) -> well_formed_comp (fcf_trans c ds sc).
induction c; unfold get_d; simpl; wftac.
Qed.

Notation "d1 ~~ d2" := (forall x, d1 x == d2 x) (at level 80).

(* maybe need a stronger hypothesis for this *)
Lemma evalDist_eq_getSupport_eq : forall {A} (c c' : Comp A), evalDist c ~~ evalDist c' -> getSupport c = getSupport c'.
  admit.
Admitted.

Fixpoint fcf_leaftrans (c : cond_com) (ds : distr_state) (s : state) : Comp state :=
  match c with
  | CondSampl v d k =>
      x <-$ (get_d d ds);
      fcf_leaftrans k ds (set v x s)
  | CondSkip => ret s
  end.


Definition condition {A : Set} (p : A -> bool) (sc : Comp A) := Repeat sc p.

Definition leaf_prob (ds : distr_state) (leaf : cond_com * (list bexp)) (s' : state) := Pr[s <-$ fcf_leaftrans (fst leaf) ds s'; ret eval_bexp (bexp_and (snd leaf)) s].

Definition leaf_condition (ds : distr_state) (leaf : cond_com * (list bexp)) (c : state) := condition (eval_bexp (bexp_and (snd leaf))) (fcf_leaftrans (fst leaf) ds c).

Definition fcf_condtrans (ds : distr_state) (leaves : list (cond_com * (list bexp))) (c : state) : Distribution state := fun x =>
  sumList leaves (fun leaf => (leaf_prob ds leaf c) * (evalDist (leaf_condition ds leaf c) x)).

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

Theorem mainTheorem (ds : distr_state) (c : com) : forall s, wf_distr_state ds -> (evalDist (fcf_trans c ds s)) ~~ fcf_condtrans ds (sym_exec c) s.
  induction c; intros.

  crush.
  unfold fcf_condtrans.

  cut (sumList (getSupport (get_d d ds))
               (fun b : nat => evalDist (get_d d ds) b * evalDist (fcf_trans c ds (set v b s)) x) ==
       sumList (getSupport (get_d d ds))
               (fun b : nat => evalDist (get_d d ds) b * fcf_condtrans ds (sym_exec c) (set v b s) x)).
  intros.
  rewrite H0.
  unfold fcf_condtrans.

  cut (sumList (map (fun p : cond_com * list bexp => (CondSampl v d (fst p), snd p)) (sym_exec c))
    (fun leaf : cond_com * list bexp => leaf_prob ds leaf s * evalDist (leaf_condition ds leaf s) x)

       ==
       sumList (sym_exec c)
    (fun leaf : cond_com * list bexp => leaf_prob ds (CondSampl v d (fst leaf), snd leaf) s * evalDist (leaf_condition ds (CondSampl v d (fst leaf), snd leaf) s) x)).
  intros.
  rewrite H1; clear H1.
  
  cut ( sumList (getSupport (get_d d ds))
    (fun b : nat =>
     evalDist (get_d d ds) b *
     sumList (sym_exec c)
       (fun leaf : cond_com * list bexp =>
          leaf_prob ds leaf (set v b s) * evalDist (leaf_condition ds leaf (set v b s)) x)) ==
         sumList (getSupport (get_d d ds))
    (fun b : nat =>
     sumList (sym_exec c)
       (fun leaf : cond_com * list bexp =>
        evalDist (get_d d ds) b *
        leaf_prob ds leaf (set v b s) * evalDist (leaf_condition ds leaf (set v b s)) x))).
  intros.
  rewrite H1; clear H0 H1.
  rewrite sumList_comm.
  apply sumList_body_eq.
  intros.
  unfold leaf_prob.
  unfold leaf_condition.
  destruct a.
  unfold fst, snd.
  uf fcf_leaftrans.
  uf evalDist.
cut (sumList (getSupport (x0 <-$ get_d d ds; fcf_leaftrans c0 ds (set v x0 s)))
    (fun b : state =>
     sumList (getSupport (get_d d ds))
       (fun b0 : nat => evalDist (get_d d ds) b0 * evalDist (fcf_leaftrans c0 ds (set v b0 s)) b) *
     (if EqDec_dec bool_EqDec (eval_bexp (bexp_and l) b) true then 1 else 0)) *
  evalDist (condition (eval_bexp (bexp_and l)) (x0 <-$ get_d d ds; fcf_leaftrans c0 ds (set v x0 s)))
    x

==
sumList (getSupport (x0 <-$ get_d d ds; fcf_leaftrans c0 ds (set v x0 s)))
    (fun b : state =>
     sumList (getSupport (get_d d ds))
       (fun b0 : nat => evalDist (get_d d ds) b0 * evalDist (fcf_leaftrans c0 ds (set v b0 s)) b *
     (if EqDec_dec bool_EqDec (eval_bexp (bexp_and l) b) true then 1 else 0) *
  evalDist (condition (eval_bexp (bexp_and l)) (x0 <-$ get_d d ds; fcf_leaftrans c0 ds (set v x0 s)))
    x))).
intros.
rewrite H1; clear H1.
rewrite sumList_comm.
apply sumList_body_eq.
intros.
admit.
admit.
admit.
admit.
apply sumList_body_eq; intros.
apply ratMult_eqRat_compat.
crush.
apply IHc.
wftac.

uf fcf_trans.
uf sym_exec.
uf leaf_condition.
uf leaf_prob.

admit.
crush.
uf fcf_condtrans.
uf sumList; crush.
uf indicator.
uf sumList; crush.
uf leaf_prob.
crush.
uf sumList; crush.
destruct_eq s x; subst.
destruct_eq x x.
destruct_eq true true.
rattac.
crush.
crush.
destruct_eq s s; destruct_eq true true.
rattac.
crush.
crush.
crush.

Admitted.

  

  



Definition leaf_feasible (ds : distr_state) (l : cond_com * (list bexp)) := bexp_feasible (bexp_and (snd l)) (fcf_leaftrans (fst l) ds).


Definition bexp_feasible (b : bexp) (sc : Comp state) := well_formed_comp (Repeat sc (eval_bexp b)).

Definition nonzero_dec (sc : Comp state) := forall (b : bexp), {Pr[ x <-$ sc; ret (eval_bexp b x)] == 0} + { ~ (Pr [x <-$ sc; ret (negb (eval_bexp b x))] == 0) }.