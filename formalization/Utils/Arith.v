From Clerical Require Import Preliminaries.Preliminaries.
From Clerical Require Import Powerdomain.Powerdomain.
From Clerical Require Import Syntax Typing TypingProperties Semantics ReasoningUtils.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.

Inductive arith : forall e, Type :=
  Arith_Var : forall k, arith (VAR k)
| Arith_int_op_plus : forall e1 e2, arith e1 -> arith e2 -> arith (e1 :+: e2)
| Arith_int_op_minus : forall e1 e2, arith e1 -> arith e2 -> arith (e1 :-: e2)
| Arith_int_op_mult : forall e1 e2, arith e1 -> arith e2 -> arith (e1 :*: e2)
| Arith_int_comp_lt : forall e1 e2, arith e1 -> arith e2 -> arith (e1 :<: e2)
| Arith_int_comp_eq : forall e1 e2, arith e1 -> arith e2 -> arith (e1 :=: e2)
| Arith_real_op_plus : forall e1 e2, arith e1 -> arith e2 -> arith (e1 ;+; e2)
| Arith_real_op_minus : forall e1 e2, arith e1 -> arith e2 -> arith (e1 ;-; e2)
| Arith_real_op_mult : forall e1 e2, arith e1 -> arith e2 -> arith (e1 ;*; e2)
| Arith_real_comp_lt : forall e1 e2, arith e1 -> arith e2 -> arith (e1 ;<; e2)
| Arith_real_recip : forall e, arith e -> arith (;/; e)

| Arith_coerce : forall e, arith e -> arith (RE e)
| Arith_exp : forall e, arith e -> arith (EXP e)
| Arith_int : forall k, arith (INT k)
| Arith_true : arith TRUE
| Arith_false : arith FALSE
.


Fixpoint arith_val e (p : arith e) Γ τ : (Γ |- e : τ) -> sem_ctx Γ -> sem_datatype τ.
Proof.
  intro w; dependent destruction p.
  exact (var_access _ _ _ w).

  induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) + (arith_val _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) - (arith_val _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) * (arith_val _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) <? (arith_val _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) =? (arith_val _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) + (arith_val _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) - (arith_val _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (arith_val _ p1 _ _ w1 x) * (arith_val _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => Rltb'' (arith_val _ p1 _ _ w1 x) (arith_val _ p2 _ _ w2 x)).

  induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.  
  exact (fun x => / (arith_val _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.  
  exact (fun x => IZR (arith_val _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.  
  exact (fun x => pow2 (arith_val _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (fun x => k).

  induction (eq_sym (has_type_ro_True_infer  _ _ w)).
  exact (fun x => true).

  induction (eq_sym (has_type_ro_False_infer _ _  w)).
  exact (fun x => false).  
Defined.

Require Import ReasoningRules.
Fixpoint arith_prt Γ e τ (w : Γ |- e : τ) (p : arith e) :
  [x : Γ] |- {{True}} e {{y : τ | y = arith_val e p Γ τ w x}}ᵖ.
Proof.
  dependent destruction p; simpl.
  {
    apply (ro_var_prt_back w (ψ := patf)).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZplus_inverse _ _ _ w)).
    intros w1 w2 e.    
    apply (
        @ro_int_op_plus_prt _ _ _ _
          (fun '(x, y) => y = ( (arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ( (arith_val _ p2 _ _ w2) x))
          patf
      ).
    
    pose proof (arith_prt _ _ _ w1 p1).
    apply (ro_imply_prt' (ψ := patf) (ψ' := patf) X);
      try intros x1 x2; auto; try intros x1 x2 x3; auto.
    pose proof (arith_prt _ _ _ w2 p2).
    apply (ro_imply_prt' (ψ := patf) (ψ' := patf) X);
      try intros x1 x2; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    rewrite e.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZminus_inverse _ _ _ w)); intros w1 w2 e.    
    apply (@ro_int_op_minus_prt _ _ _ _
             (fun '(x, y) => y = arith_val e1 p1 Γ INTEGER w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ INTEGER w2 x)
             patf
          ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZmult_inverse _ _ _ w)); intros w1 w2 e.    
    apply (@ro_int_op_mult_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ INTEGER w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ INTEGER w2 x)
          patf ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZlt_inverse _ _ _ w)); intros w1 w2 e.    
    apply (@ro_int_comp_lt_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ INTEGER w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ INTEGER w2 x)
          patf).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZeq_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (@ro_int_comp_eq_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ INTEGER w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ INTEGER w2 x)
          patf ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRplus_inverse _ _ _ w)); intros w1 w2 e.    
    apply (@ro_real_op_plus_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ REAL w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ REAL w2 x)
          patf ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRminus_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (@ro_real_op_minus_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ REAL w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ REAL w2 x)
          patf ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRmult_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (@ro_real_op_mult_prt _ _ _ _
             (fun '(x, y) => y = arith_val e1 p1 Γ REAL w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ REAL w2 x)
          patf ).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRlt_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (@ro_real_comp_lt_prt _ _ _ _ 
             (fun '(x, y) => y = arith_val e1 p1 Γ REAL w1 x)
             (fun '(x, y) => y = arith_val e2 p2 Γ REAL w2 x)
          patf).
    apply arith_prt.
    apply arith_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer Γ e τ w)).
    pose ((has_type_ro_OpRrecip_inverse _ _ w)) as w1.    
    apply (ro_recip_prt_back (ψ := patf)).
    pose proof (arith_prt _ _ _ w1 p).
    apply (ro_imply_prt' (ψ := patf) (ψ' := patf) X).
    intros x1 x2; auto.
    intros [x1 x2] h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer Γ e τ w)).
    pose ((has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    
    apply (@ro_coerce_prt _ _ _ patf).
    pose proof (arith_prt _ _ _ w1 p).
    apply (ro_imply_prt' (ψ := patf) (ψ' := patf) X).
    intros x1 x2; auto.
    intros [x1 x2] h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }
  
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer Γ e τ w)).
    pose ((has_type_ro_OpZRexp_inverse _ _ w)) as w1.    
    apply (@ro_exp_prt _ _ _ patf).
    pose proof (arith_prt _ _ _ w1 p).
    apply (ro_imply_prt' (ψ := patf) (ψ' := patf) X).
    intros x1 x2; auto.
    intros [x1 x2] h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_Int_infer Γ k τ w)).
    simpl.
    apply (ro_int_prt_back (ψ := patf)).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_True_infer Γ τ w)).
    simpl.
    apply (ro_true_prt_back (ψ := patf)).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_False_infer Γ τ w)).
    simpl.
    apply (ro_false_prt_back (ψ := patf)).
    intros x1 x2; auto.
  }  
  
Defined.


Fixpoint arith_cond e (p : arith e) Γ τ :
  (Γ |- e : τ) -> sem_ctx Γ -> Prop.
Proof.
  intro w; dependent destruction p.
  exact (fun _ => True).
        
  destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  destruct ((has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
  exact  (fun x =>  (arith_cond _ p1 _ _ w1) x /\  (arith_cond  _ p2 _ _ w2) x)%Z.

  destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
  
  destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  destruct (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
    
  destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).   
        
  destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
  
  destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
  
  destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
  exact  (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
  
  destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x).
  
  destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
  exact (fun x => (arith_cond _ p1 _ _ w1) x /\ (arith_cond  _ p2 _ _ w2) x /\
                  ( (arith_val _ p1 _ _ w1) x) <> ( (arith_val _ p2 _ _ w2) x)).
        
  destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.    
  exact (fun x => (arith_cond _ p _ _ w1) x /\
                  ((arith_val _ p _ _ w1) x <> 0%R)).

  destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.    
  exact ((fun x => (arith_cond _ p _ _ w1) x)).

  destruct (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.    
  exact (
      (fun x => (arith_cond _ p _ _ w1) x)).

  destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (
      (fun x => True)).
  
  destruct (eq_sym (has_type_ro_True_infer _ _ w)).
  exact (
      (fun x => True)).
    
  destruct (eq_sym (has_type_ro_False_infer _ _ w)).
  exact (
      (fun x => True)). 
Defined.

Lemma arith_val_typing_irrl : forall e (p : arith e) Γ τ (w1 w2 : Γ |- e : τ),
  forall x, arith_val _ p _ _ w1 x = arith_val _ p _ _ w2 x.
Proof.
  intros.
  dependent induction p; simpl.
  apply var_access_typing_irrl.
  {
    destruct (eq_sym (has_type_ro_OpZplus_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpZplus_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpZplus_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZminus_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpZminus_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpZminus_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZmult_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpZmult_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpZmult_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZlt_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpZlt_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpZlt_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZeq_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpZeq_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpZeq_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRplus_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpRplus_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpRplus_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRminus_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpRminus_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpRminus_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRmult_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpRmult_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpRmult_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRlt_infer Γ e1 e2 τ w1)).
    easy_rewrite_uip.
    destruct (has_type_ro_OpRlt_inverse Γ e1 e2 w1).
    destruct (has_type_ro_OpRlt_inverse Γ e1 e2 w2).
    rewrite (IHp1 _ _ h h1 x).
    rewrite (IHp2 _ _ h0 h2 x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer Γ e τ w1)).
    easy_rewrite_uip.
    rewrite (IHp _ _ (has_type_ro_OpRrecip_inverse Γ e w1) (has_type_ro_OpRrecip_inverse Γ e w2) x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer Γ e τ w1)).
    easy_rewrite_uip.
    rewrite (IHp _ _ (has_type_ro_OpZRcoerce_inverse Γ e w1) (has_type_ro_OpZRcoerce_inverse Γ e w2) x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer Γ e τ w1)).
    easy_rewrite_uip.
    rewrite (IHp _ _ (has_type_ro_OpZRexp_inverse Γ e w1) (has_type_ro_OpZRexp_inverse Γ e w2) x).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_Int_infer Γ k τ w1)).
    easy_rewrite_uip.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_True_infer Γ τ w1)).
    easy_rewrite_uip.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_False_infer Γ τ w1)).
    easy_rewrite_uip.
    reflexivity.
  }
Defined.

Fixpoint arith_tot e (p : arith e) Γ τ (w : Γ |- e : τ) :
  [x : Γ] |- {{ arith_cond _ p _ _ w x }} e {{y : τ | y = arith_val _ p _ _ w x}}ᵗ.
Proof.
  dependent destruction p; simpl.
  {
    apply (ro_var_tot_back w (ψ := patf)).
    intros x _.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_int_op_plus_tot _ _ _ _
          (fun '(x, y) => y = ( (arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ( (arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct (has_type_ro_OpZplus_inverse Γ e1 e2 w).
    rewrite (arith_val_typing_irrl _ _ _ _ w1 h).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 h0).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    destruct ((has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_int_op_minus_tot _ _ _ _ 
          (fun '(x, y) => y = ( (arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ( (arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct ((has_type_ro_OpZminus_inverse _ _ _ w)) as [www1 www2].    
    rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_int_op_mult_tot _ _ _ _ 
          (fun '(x, y) => y = ( (arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ( (arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [www1 www2].    
    rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_int_comp_lt_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [www1 www2].    
    rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_int_comp_eq_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
       destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [www1 www2].    
     rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_real_op_plus_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
       destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [www1 www2].    
    rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
 reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_real_op_minus_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [www1 www2].    
        rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_real_op_mult_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).
    pose proof (arith_tot _ p1 _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; intro h; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [www1 www2].    
        rewrite (arith_val_typing_irrl _ _ _ _ w1 www1).
    rewrite (arith_val_typing_irrl _ _ _ _ w2 www2).
reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        @ro_real_comp_lt_tot _ _ _ _ 
          (fun '(x, y) => y = ((arith_val _ p1 _ _ w1) x) /\  y <> ((arith_val _ p2 _ _ w2) x))
          (fun '(x, y) => y = ((arith_val _ p2 _ _ w2) x))
          patf
      ).

    pose proof (arith_tot _ p1 _ _ w1).
    simpl in X.
    apply (ro_tot_pose_readonly
             (ϕ := fun x => arith_cond e1 p1 Γ REAL w1 x)
             (ψ := fun '(x, y) => (y = arith_val e1 p1 Γ REAL w1 x))
             (fun x =>
                ( (arith_val _ p1 _ _ w1) x) <>
                  ( (arith_val _ p2 _ _  w2) x))) in X.
             
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    split.
    exact x2.
    destruct x3.
    exact H0.
    intros [x1 x2] x3.
    split.
    destruct x3.
    exact H.
    destruct x3.
    rewrite H; exact H0.

    
    pose proof (arith_tot _ p2 _ _ w2).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro h; auto.
    intros x1 x2 x3 h1 h2.
    destruct h1.
    split; auto.
    rewrite <- h2 in H0.
    exact H0.    
    rewrite H, h2; auto.
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [www1 www2].
    simpl.
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [wwww1 wwww2].
    rewrite (arith_val_typing_irrl _ _ _ _ w2 wwww2).
    rewrite (arith_val_typing_irrl _ _ _ _ w1 wwww1).
    reflexivity.

  }
  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
    pose ( (has_type_ro_OpRrecip_inverse _ _ w)) as w1.    
    
    apply (ro_recip_tot_back (ψ := patf)).
    pose proof (arith_tot _ p _ _ w1).
    apply (ro_tot_pose_readonly
             (ψ := patf)
             (fun x => 
                ((arith_val _ p _ _ w1) x) <> 0%R)) in X.
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    split.
    destruct H.
    auto.
    destruct H.
    auto.
    intros [x1 x2] x3.
    destruct x3.
    split.
    rewrite H; auto.
    rewrite H; auto.
  }

  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
    pose ( (has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    

    apply (@ro_coerce_tot _ _ _ (patf)).
    pose proof (arith_tot _ p _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 [x3 x4]]; auto; try intros [x1 x2] x3; auto.
    intro.
    intros.
    simpl in H.
    exact H.
    simpl.    
    rewrite x3; auto.
  }
  
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
    pose ( (has_type_ro_OpZRexp_inverse _ _ w)) as w1.    
    
    apply (@ro_exp_tot _ _ _ patf).
    pose proof (arith_tot _ p _ _ w1).
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X);
      try intros x1 [x2 [x3 x4]]; auto; try intros [x1 x2] x3; auto.
    intro.
    intros.
    simpl in H.
    exact H.
    simpl.
    rewrite x3; auto.
  }

  {
    destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
    apply (@ro_int_tot_back _ _ _ patf).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_True_infer _ _ w)).
    apply (@ro_true_tot_back _ _ patf).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_False_infer _ _ w)).
    apply (@ro_false_tot_back _ _ patf).
    intros x _.
    reflexivity.
  }    
Defined.


Fixpoint arith_dec e : arith e + (arith e -> False).
Proof.
  dependent destruction e;
    try (left; constructor; auto; fail);
    try (destruct b; left; constructor; auto; fail).

  destruct (arith_dec e1).
  destruct (arith_dec e2).
  destruct b; constructor; auto; constructor; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  
  destruct (arith_dec e).
  left; destruct u; constructor; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.

  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  (* right; intro. *)
  (* dependent destruction H. *)
Defined.


