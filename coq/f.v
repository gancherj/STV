Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import Bool Arith String List CpdtTactics Program.
Open Scope string_scope.
Require FcfLems.

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

Ltac uf e := unfold e; fold e.

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

(* maybe need a stronger hypothesis for this *)
Lemma evalDist_eq_getSupport_eq : forall {A} (c c' : Comp A), evalDist c ~~ evalDist c' -> getSupport c = getSupport c'.
  admit.
Admitted.



Lemma fcf_trans_iso : forall c ds (sc sc'  : Comp state), (evalDist sc) ~~ (evalDist sc') -> evalDist (fcf_trans_ c ds sc) ~~ evalDist (fcf_trans_ c ds sc').
    induction c; intros.
    crush.
    rewrite (evalDist_eq_getSupport_eq _ _ H).
    apply sumList_body_eq.
    intros.
    rewrite H.
    apply eqRat_refl.

    unfold fcf_trans_; fold fcf_trans_.
    apply evalDist_seq_eq.
    apply H.
    intros.
    destruct (eval_bexp b x0).
    apply IHc1.
    auto.
    apply IHc2.
    auto.


    unfold fcf_trans_; fold fcf_trans_.
    apply IHc2.
    apply IHc1.
    auto.

    crush.
Qed.    
    



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

Lemma fcf_leaftrans_iso : forall c ds sc sc', (evalDist sc) ~~ (evalDist sc') -> evalDist (fcf_leaftrans_ c ds sc) ~~ evalDist (fcf_leaftrans_ c ds sc').
  induction c; intros.
  crush.
  rewrite (evalDist_eq_getSupport_eq _ _ H).
  apply sumList_body_eq.
  intros.
  apply ratMult_eqRat_compat.
  apply H.
  apply eqRat_refl.

  unfold fcf_leaftrans_; fold fcf_leaftrans_.
  apply IHc2.
  apply IHc1.
  auto.

  crush.
Qed.  
  
  

Definition condition {A : Set} (p : A -> bool) (sc : Comp A) := Repeat sc p.

Definition leaf_prob_ (ds : distr_state) (leaf : cond_com * (list bexp)) (cs : Comp state) := Pr[s <-$ fcf_leaftrans_ (fst leaf) ds cs; ret eval_bexp (bexp_and (snd leaf)) s].

Definition leaf_condition_ (ds : distr_state) (leaf : cond_com * (list bexp)) (cs : Comp state) := condition (eval_bexp (bexp_and (snd leaf))) (fcf_leaftrans_ (fst leaf) ds cs).

Lemma leaf_condition_iso : forall ds leaf cs cs', (evalDist cs) ~~ (evalDist cs') -> evalDist (leaf_condition_ ds leaf cs) ~~ evalDist (leaf_condition_ ds leaf cs').
  admit.
  Admitted.

Definition fcf_condtrans_ (ds : distr_state) (leaves : list (cond_com * (list bexp))) (cs : Comp state) : Distribution state := fun x =>
  sumList leaves (fun leaf => (leaf_prob_ ds leaf cs) * (evalDist (leaf_condition_ ds leaf cs) x)).

Lemma fcf_condtrans_iso : forall ds leaves (cs cs' : Comp state), (evalDist cs) ~~ (evalDist cs') -> (fcf_condtrans_ ds leaves cs) ~~ (fcf_condtrans_ ds leaves cs').
  induction leaves.
  intros.
  unfold fcf_condtrans_.
  unfold sumList, fold_left.
  apply eqRat_refl.

  unfold fcf_condtrans_.
  intros.
  rewrite sumList_cons.
  rewrite sumList_cons.
  apply ratAdd_eqRat_compat.
  apply ratMult_eqRat_compat.
  unfold leaf_prob_.
  apply evalDist_seq_eq.
  apply fcf_leaftrans_iso.
  auto.
  intros.
  apply eqRat_refl.
  apply leaf_condition_iso; auto.

  apply sumList_body_eq.
  intros.
  apply ratMult_eqRat_compat.
  unfold leaf_prob_.
  apply evalDist_seq_eq.
  apply fcf_leaftrans_iso.
  auto.
  intros;
  apply eqRat_refl.

  apply leaf_condition_iso; auto.
Qed.

Lemma fcf_condtrans_seq (ds : distr_state) (c1 c2 : com) cs : fcf_condtrans_ ds (sym_exec (Seq c1 c2)) cs ~~ fcf_condtrans_ ds (sym_exec c2) (fcf_trans_ c1 ds cs).



  
  revert c2.
  induction c1; intros.
  uf sym_exec.
  crush.
  rewrite app_nil_r.
  uf fcf_condtrans_.
  generalize (sym_exec c2).
  induction l.
  unfold sumList; crush.
  rewrite map_cons.
  rewrite sumList_cons.
  rewrite IHl.
  rewrite sumList_cons.
  apply ratAdd_eqRat_compat.
  destruct a.
  uf leaf_condition_.
  unfold snd.
  admit.

  apply eqRat_refl.
  uf fcf_trans_.
  uf sym_exec.


  admit.
Admitted.
  

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

Theorem neq_nil_In {A} (xs : list A) : xs <> [] -> (exists x, In x xs).
  induction xs.
  intros; contradiction.
  intros.
  exists a.
  crush.
Qed.


Lemma negP_iff_Not : forall b x, (FcfLems.negP (eval_bexp b)) x = (eval_bexp (Not b)) x.
    crush.
Qed.


Theorem mainTheorem (ds : distr_state) (c : com) `{eq_dec state} : forall cs, well_formed_comp cs -> wf_distr_state ds -> (evalDist (fcf_trans_ c ds cs)) ~~ fcf_condtrans_ ds (sym_exec c) cs.
  induction c; intros.

  (* ret case *)
  unfold fcf_trans_, fcf_condtrans_, sym_exec, leaf_prob_, sumList, fold_left.
  unfold fst, bexp_and, fold_left, leaf_condition_, snd, bexp_and, fold_left, fst.
  unfold eval_bexp.
  unfold fcf_leaftrans_.
  rewrite ret_true_1.
  unfold condition.
  rewrite <- repeat_true.
  rewrite <- ratAdd_0_l.
  rewrite ratMult_1_l.
  apply eqRat_refl.
  wftac.
  wftac.

  uf fcf_trans_.
  uf sym_exec.
  uf fcf_condtrans_.
  pose proof (FcfLems.filter_exists (getSupport cs) (eval_bexp b)).
  destruct H1.
  destruct s.
  destruct s.
  pose proof (getSupport_length_nz H).
  rewrite e in H1.
  inversion H1.

  destruct a.
  destruct (neq_nil_In (filter (eval_bexp b) (getSupport cs)) H1).
  rewrite FcfLems.if_repeat_decomp_l.



  Theorem impossible_leaf_condition_nil : forall ds cs b c bs x, filter (eval_bexp b) (getSupport cs) = [] -> In b bs -> evalDist (leaf_condition_ ds (c,bs) cs) x == 0.
    intros.
    crush.
  
  unfold leaf_condition_.
  admit. (* the actual probabilistic judgement *)
  intros.
  apply wfcomp_trans; auto.
  econstructor; auto.
  apply H3.
  unfold FcfLems.cond_prob.
  rewrite H2.
  uf sumList; crush.

  destruct a.
  destruct (neq_nil_In (filter (FcfLems.negP (eval_bexp b)) (getSupport cs)) H2).


  rewrite FcfLems.if_repeat_decomp_r.
  admit. (* prob calculation *)
  intros.
  apply wfcomp_trans; auto.
  econstructor; auto.
  apply H3.
  unfold FcfLems.cond_prob.
  rewrite H1.
  uf sumList; crush.

  destruct a.
  destruct (neq_nil_In (filter (eval_bexp b) (getSupport cs)) H1).
  destruct (neq_nil_In (filter (FcfLems.negP (eval_bexp b)) (getSupport cs)) H2).
  

  rewrite FcfLems.if_repeat_decomp_both.
  admit. (* prob *)
  intros; apply wfcomp_trans; auto.
  intros; apply wfcomp_trans; auto.
  econstructor; auto.
  apply H3.
  econstructor; auto.
  apply H4.

  (* seq *)
  uf fcf_trans_.
  rewrite IHc2.
  rewrite fcf_condtrans_seq.
  apply eqRat_refl.
  apply wfcomp_trans; auto.
  auto.

  (* skip *)
  crush.
  unfold fcf_condtrans_.
  unfold sumList; crush.
  unfold leaf_prob_.
  unfold fst, snd, bexp_and, fcf_leaftrans_, fold_left.
  rewrite <- ratAdd_0_l.
  unfold eval_bexp.
  rewrite ret_true_1.
  rewrite ratMult_1_l.
  rewrite <- ratMult_1_r.
  rewrite ratMult_comm.
  apply ratMult_eqRat_compat.
  unfold indicator.
  rewrite ratMult_1_l.
  apply eqRat_symm.
  rewrite ratInverse_eqRat_compat.
  apply ratInverse_1.
  rewrite filter_tr.
  rewrite evalDist_lossless.
  rattac.
  auto.
  rewrite filter_tr.
  rewrite evalDist_lossless.
  apply eqRat_refl.
  wftac.
  rewrite ratMult_1_l; apply eqRat_refl.
  wftac.
Admitted.

  
  
  unfold sym_exec; fold sym_exec.
  unfold fcf_condtrans_; fold fcf_condtrans_.w

  unfold fcf_trans_; fold fcf_trans_.
  rewrite <- IHc2.
  rewrite IHc2.
  unfold sym_exec; fold sym_exec.
  

  
  


Admitted.

  

  



Definition leaf_feasible (ds : distr_state) (l : cond_com * (list bexp)) := bexp_feasible (bexp_and (snd l)) (fcf_leaftrans (fst l) ds).


Definition bexp_feasible (b : bexp) (sc : Comp state) := well_formed_comp (Repeat sc (eval_bexp b)).

Definition nonzero_dec (sc : Comp state) := forall (b : bexp), {Pr[ x <-$ sc; ret (eval_bexp b x)] == 0} + { ~ (Pr [x <-$ sc; ret (negb (eval_bexp b x))] == 0) }.