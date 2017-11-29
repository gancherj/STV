(* NOTE: the issue with the below proofs is that the original bexp's are being evaluated *before* running all commands, and the sym exec bexp's are being evaluated *after* running all commands. For commands which shadow, or evaluate to defaults, this will cause a discrepancy. I want to actually capture statements about states which are stable after forward execution. 

This means I will have to modify the semantics of bexp's and so on to return error if variable is not found. Variables will not be able to be overwritten.

*)


Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import Bool Arith String List CpdtTactics Program.
Open Scope string_scope.
Require Import FcfLems.



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

Lemma fst_eq_set_fst_eq : forall x n s1 s2, map fst s1 = map fst s2 -> map fst (set x n s1) = map fst (set x n s2).
  induction s1; induction s2.
  crush.
  intro H; inversion H.
  intro H; inversion H.
  intros; simpl in *.
  destruct a; destruct a0.
  destruct (string_dec x v); destruct (string_dec x v0).
  simpl in *.
  subst.
  rewrite H.
  auto.


  simpl in *; simpl.
  inversion H.
  crush.
  simpl in H; inversion H.
  subst.
  crush.
  simpl in *; inversion H.
  f_equal.
  apply IHs1.
  auto.
Qed.

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
| Ret : aexp -> com.

Inductive leaf_com : Type :=
| LeafSampl : var -> distr -> leaf_com -> leaf_com
| LeafRet : aexp -> leaf_com.

Fixpoint sym_exec (c : com) : list (leaf_com * bexp) :=
  match c with
  | Sampl v d k =>
    map (fun p => (LeafSampl v d (fst p), snd p)) (sym_exec k)
  | If b c1 c2 =>
    (map (fun p => (fst p, And b (snd p))) (sym_exec c1)) ++ (map (fun p => (fst p, And (Not b) (snd p))) (sym_exec c2))
  | Ret e => (LeafRet e, Tt) :: nil
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



Ltac repeat_inv := match goal with
                   | [H : In ?x (getSupport (Repeat ?c ?p)) |- _] => apply repeat_In in H
                   end.

Ltac myrem e := remember e; destruct e; subst.



Fixpoint eval_com (c : com) (ds : distr_state) (s : state) : Comp (option nat) :=
  match c with
  | Sampl v d k => 
     x <-$ (get_d d ds);
     eval_com k ds (set v x s)
  | If b c1 c2 =>
    match (eval_bexp b s) with
    | Some true => eval_com c1 ds s
    | Some false => eval_com c2 ds s
    | _ => ret None
    end
  | Ret e => (ret (eval_aexp e s))
  end.

Lemma wf_eval_com : forall c ds sc, (forall x, well_formed_comp (ds x)) -> well_formed_comp (eval_com c ds sc).
induction c; unfold get_d; simpl; wftac.
intros;
destruct (eval_bexp b sc); wftac.
Qed.

Notation "d1 ~~ d2" := (forall x, d1 x == d2 x) (at level 80).

Fixpoint eval_leafcom (c : leaf_com) (ds : distr_state) (s : state) : Comp (state * option nat) :=
  match c with
  | LeafSampl v d k =>
    x <-$ (get_d d ds);
      eval_leafcom k ds (set v x s)
  | LeafRet e => ret (s, eval_aexp e s)
  end.

Definition condition {A : Set} (p : A -> bool) (sc : Comp A) := Repeat sc p.
Definition leaf_val (ds : distr_state) (s : state) (leaf : leaf_com * bexp) (y : nat) :=
  p <-$ eval_leafcom (fst leaf) ds s;
  let (s', v) := p in
  match (eval_bexp (snd leaf) s', v) with
     | (Some true, Some v') => (if Nat.eq_dec v' y then ret true else ret false)
     | (_, _) => ret false
  end.

Lemma leaf_val_sampl : forall d ds s leaf v y,
    Pr [x <-$ (get_d d ds); leaf_val ds (set v x s) leaf y] == Pr [leaf_val ds s (LeafSampl v d (fst leaf), snd leaf) y].

  destruct leaf.
  uf leaf_val.
  unfold fst,snd.
  uf eval_leafcom.
  intros;
  fcf_inline rightc.
  comp_skip.
  Qed.

Lemma leafcom_bexp_stable : forall c ds s x b b', eval_bexp b s = Some b' -> In x (getSupport (eval_leafcom c ds s)) -> eval_bexp b (fst x) = Some b'.
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

Fixpoint wf_bexps (c : com) (s : state) : Prop :=
  match c with
  | Sampl x d k =>
    forall v, wf_bexps k (set x v s)%nat
  | If b c1 c2 =>
    eval_bexp b s <> None /\ wf_bexps c1 s /\ wf_bexps c2 s
  | Ret _ => True
  end.


Lemma eval_leafcom_true_equiv : forall ls ds s b x, eval_bexp b s = Some true ->
  sumList (map (fun p : leaf_com * bexp => (fst p, And b (snd p))) (ls)) (fun leaf => Pr [leaf_val ds s leaf x])
  == sumList ls (fun leaf => Pr [leaf_val ds s leaf x]).

  intros.
  rewrite sumList_map.
  apply sumList_body_eq.
  intros.
  destruct a.
  uf leaf_val.
  simpl.
  apply sumList_body_eq.
  intros.
  apply ratMult_eqRat_compat.
  crush.
  destruct a.
  cut (eval_bexp b s0 = Some true).
  intros H3; rewrite H3; clear H3.
  destruct (eval_bexp b0 s0).
  simpl.
  crush.
  crush.
  cut (s0 = fst (s0, o)).
  intro; subst.
  rewrite H2.

  eapply leafcom_bexp_stable.
  apply H.
  apply H1.
  crush.
Qed.  

Lemma eval_leafcom_false_0 : forall ls ds s b x, eval_bexp b s = Some false ->
  sumList (map (fun p : leaf_com * bexp => (fst p, And b (snd p))) (ls)) (fun leaf => Pr [leaf_val ds s leaf x])
  == 0.
  intros.
  rewrite sumList_map.
  uf leaf_val.
  apply sumList_0; intros.
  crush.
  apply sumList_0.
  intros.
  apply ratMult_0.
  right; destruct a0.
  cut (eval_bexp b s0 = Some false).
  intro H3; rewrite H3; simpl.
  destruct (eval_bexp (snd a) s0).
  crush.
  destruct_eq false true; crush.
  crush.
  destruct_eq false true; crush.

  cut (s0 = fst (s0, o)).
  intro.
  rewrite H2.
  eapply leafcom_bexp_stable; crush.
  apply H1.
  crush.
Qed.
  

Theorem mainTheorem (ds : distr_state) (c : com) : forall s x, wf_bexps c s -> wf_distr_state ds ->
   (evalDist (eval_com c ds s) (Some x)) == sumList (sym_exec c) (fun leaf => Pr [leaf_val ds s leaf x]).
  induction c; intros s x wfb H.
  uf eval_com.
  uf sym_exec.
  uf evalDist.
  cut (sumList (getSupport (get_d d ds))
    (fun b : nat => evalDist (get_d d ds) b * evalDist (eval_com c ds (set v b s)) (Some x))
       ==
       sumList (getSupport (get_d d ds))
    (fun b : nat => evalDist (get_d d ds) b * sumList (sym_exec c) (fun leaf => Pr [leaf_val ds (set v b s) leaf x]))).
  intro H3; rewrite H3; clear H3.
  cut (
  sumList (getSupport (get_d d ds))
    (fun b : nat =>
     evalDist (get_d d ds) b *
     sumList (sym_exec c) (fun leaf : leaf_com * bexp => Pr [leaf_val ds (set v b s) leaf x ])) 
  == sumList (getSupport (get_d d ds))
    (fun b : nat =>
     sumList (sym_exec c) (fun leaf : leaf_com * bexp => evalDist (get_d d ds) b * Pr [leaf_val ds (set v b s) leaf x ])) ).
  intro H3; rewrite H3; clear H3.

  rewrite sumList_map.
  rewrite sumList_swap.
  apply sumList_body_eq.
  intros.
  uf leaf_val.
  unfold fst, snd.
  destruct a.
  uf eval_leafcom.
  fcf_inline rightc.
  uf evalDist.
  apply sumList_body_eq.
  intros.
  crush.
  apply sumList_body_eq; intros.
  rewrite sumList_factor_constant_l.
  crush.
  apply sumList_body_eq; intros.
  apply ratMult_eqRat_compat.
  crush.
  apply IHc.
  auto.
  auto.


  (* if case *)
  uf sym_exec.
  rewrite sumList_app.
  uf eval_com.
  remember (eval_bexp b s) as eb.
  destruct eb.
  destruct b0.
  symmetry in Heqeb.
  pose proof (eval_leafcom_true_equiv (sym_exec c1) ds s b x Heqeb).
  rewrite H0.
  assert (eval_bexp (Not b) s = Some false).
  uf eval_bexp; crush.
  pose proof (eval_leafcom_false_0 (sym_exec c2) ds _ _ x H1 ).
  rewrite H2.
  rewrite <- ratAdd_0_r.
  eapply IHc1.
  crush.
  crush.
  
  (* same as above *)

  symmetry in Heqeb.
  rewrite (eval_leafcom_false_0 (sym_exec c1) ds _ _ x Heqeb ).
  assert (eval_bexp (Not b) s = Some true).
  crush.
  rewrite (eval_leafcom_true_equiv (sym_exec c2) ds _ _ x H0).
  rewrite IHc2.
  rewrite <- ratAdd_0_l.
  crush.
  crush.
  crush.

  (* bexp is well formed, so this case is impossible *)
  unfold wf_bexps in wfb; fold wf_bexps in wfb.
  destruct wfb.
  symmetry in Heqeb.
  contradiction.

  uf sym_exec.
  rewrite sumList_single.
  uf eval_com.
  uf leaf_val.
  unfold fst, snd.
  uf eval_leafcom.
  crush.
  rewrite sumList_single.
  destruct_eq (s, eval_aexp a s) (s, eval_aexp a s).
  destruct_eq (eval_aexp a s) (Some x).
  destruct (eval_aexp a s).
  destruct (Nat.eq_dec n x).
  crush.
  destruct_eq true true.
  crush.
  crush.
  inject e0.
  crush.
  crush.
  destruct (eval_aexp a s).
  destruct (Nat.eq_dec n0 x).
  crush.
  crush.
  destruct_eq false true.
  crush.
  rewrite ratMult_0_r.
  crush.
  crush.
  destruct_eq false true.
  crush.
  rewrite ratMult_0_r; crush.
  crush.
Qed.
