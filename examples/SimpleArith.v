From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.


Lemma pp_ro_tot_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  Γ |-- [{ϕ}] e [{y : τ | ψ y}] -> Γ |-- [{(ϕ /\\ θ)}] e [{y : τ | (ψ /\\\ (fun _ : sem_datatype τ => θ)) y}].
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_tot_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_ro_prt_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  Γ |-- {{ϕ}} e {{y : τ | ψ y}} -> Γ |-- {{(ϕ /\\ θ)}} e {{y : τ | (ψ /\\\ (fun _ : sem_datatype τ => θ)) y}}.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_prt_pose_readonly _ _ _ _ _ _ _ p).
Defined.


  
Inductive simple_arithmetical : forall e, Type :=
  SA_Var : forall k, simple_arithmetical (VAR k)
| SA_int_op_plus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :+: e2)
| SA_int_op_minus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :-: e2)
| SA_int_op_mult : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :*: e2)
| SA_int_comp_lt : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :<: e2)
| SA_int_comp_eq : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :=: e2)
| SA_real_op_plus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;+; e2)
| SA_real_op_minus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;-; e2)
| SA_real_op_mult : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;*; e2)
| SA_real_comp_lt : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;<; e2)
| SA_real_recip : forall e, simple_arithmetical e -> simple_arithmetical (;/; e)

| SA_coerce : forall e, simple_arithmetical e -> simple_arithmetical (RE e)
| SA_exp : forall e, simple_arithmetical e -> simple_arithmetical (EXP e)
| SA_int : forall k, simple_arithmetical (INT k)
| SA_true : simple_arithmetical TRUE
| SA_false : simple_arithmetical FALSE
.

Fixpoint has_type_ro_Int_infer Γ k τ (w : Γ |- INT k : τ) : τ = INTEGER.
Proof.
  dependent destruction w.
  dependent destruction h.
  apply (has_type_ro_Int_infer _ _ _ h).
  exact eq_refl.
Defined.

Fixpoint has_type_ro_True_infer Γ τ (w : Γ |- TRUE : τ) : τ = BOOL.
Proof.
  dependent destruction w.
  dependent destruction h.
  apply (has_type_ro_True_infer _ _ h).
  exact eq_refl.
Defined.

Fixpoint has_type_ro_False_infer Γ τ (w : Γ |- FALSE : τ) : τ = BOOL.
Proof.
  dependent destruction w.
  dependent destruction h.
  apply (has_type_ro_False_infer _ _ h).
  exact eq_refl.
Defined.

Fixpoint simple_arithmetical_value_prt e (p : simple_arithmetical e) Γ τ (w : Γ |- e :τ) : sem_ro_ctx Γ -> sem_datatype τ.
Proof.
  dependent destruction p.
  exact (ro_access _ _ _ w).

  induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) + (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) - (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) * (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) <? (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) =? (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) + (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) - (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) * (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => Rltb'' (simple_arithmetical_value_prt _ p1 _ _ w1 x) (simple_arithmetical_value_prt _ p2 _ _ w2 x)).

  induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.  
  exact (fun x => / (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.  
  exact (fun x => IZR (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.  
  exact (fun x => pow2 (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (fun x => k).

  induction (eq_sym (has_type_ro_True_infer  _ _ w)).
  exact (fun x => true).

  induction (eq_sym (has_type_ro_False_infer _ _  w)).
  exact (fun x => false).  
Defined.

(* Fixpoint simple_arithmetical_value_prt_irrl e (p : simple_arithmetical e) Γ τ (w1 w2 : Γ |- e : τ): *)
(*   forall x, *)
(*     simple_arithmetical_value_prt e p Γ τ w1 x = simple_arithmetical_value_prt e p Γ τ w2 x. *)
(* Proof. *)
(*   intro x. *)
(*   dependent destruction p; simpl. *)

(*   apply ro_access_typing_irrl. *)
  
(*   destruct (eq_sym (has_type_ro_OpZplus_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpZplus_infer Γ e1 e2 INTEGER w1)) with (eq_refl INTEGER) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpZplus_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpZplus_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpZminus_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpZminus_infer Γ e1 e2 INTEGER w1)) with (eq_refl INTEGER) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpZminus_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpZminus_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)
  
(*   destruct (eq_sym (has_type_ro_OpZmult_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpZmult_infer Γ e1 e2 INTEGER w1)) with (eq_refl INTEGER) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpZmult_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpZmult_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpZlt_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpZlt_infer Γ e1 e2 _ w1)) with (eq_refl BOOL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpZlt_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpZlt_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpZeq_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpZeq_infer Γ e1 e2 _ w1)) with (eq_refl BOOL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpZeq_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpZeq_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpRplus_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpRplus_infer Γ e1 e2 REAL w1)) with (eq_refl REAL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpRplus_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpRplus_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpRminus_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpRminus_infer Γ e1 e2 REAL w1)) with (eq_refl REAL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpRminus_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpRminus_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)
  
(*   destruct (eq_sym (has_type_ro_OpRmult_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpRmult_infer Γ e1 e2 REAL w1)) with (eq_refl REAL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpRmult_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpRmult_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpRlt_infer Γ e1 e2 τ w2)). *)
(*   replace (eq_sym (has_type_ro_OpRlt_infer Γ e1 e2 _ w1)) with (eq_refl BOOL) by apply prop_irrl. *)
(*   simpl. *)
(*   destruct (has_type_ro_OpRlt_inverse Γ e1 e2 w1), *)
(*     (has_type_ro_OpRlt_inverse Γ e1 e2 w2). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p1 _ _ h h1 x). *)
(*   rewrite (simple_arithmetical_value_prt_irrl _ p2 _ _ h0 h2 x).     *)
(*   reflexivity. *)

(*   destruct (eq_sym (has_type_ro_OpRrecip_infer Γ e τ w2)). *)
(*   replace  (eq_sym (has_type_ro_OpRrecip_infer Γ e REAL w1)) with (eq_refl REAL) by apply prop_irrl. *)
(*   simpl. *)
(*   apply lp. *)
(*   apply (simple_arithmetical_value_prt_irrl _ p _ _ (has_type_ro_OpRrecip_inverse Γ e w1) (has_type_ro_OpRrecip_inverse Γ e w2) x). *)
(* Defined. *)

Fixpoint simple_arithmetical_prt Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical e) :
  Γ |-- {{fun _ => True}} e {{y : τ | fun x => y = simple_arithmetical_value_prt e p Γ τ w x}}.
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_prt_back w).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZplus_inverse _ _ _ w)). intros w1 w2 e.    
    apply (
        pp_ro_int_op_plus_prt
          (fun y x => y = ( (simple_arithmetical_value_prt _ p1 _ _ w1) x))
          (fun y x => y = ( (simple_arithmetical_value_prt _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_prt _ _ _ w1 p1).
    apply (pp_ro_imply_prt X);
      try intros x1 x2; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_prt _ _ _ w2 p2).
    apply (pp_ro_imply_prt X);
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
    apply (pp_ro_int_op_minus_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_int_op_mult_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_int_comp_lt_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_int_comp_eq_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_real_op_plus_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_real_op_minus_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_real_op_mult_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_real_comp_lt_prt
             (fun y x => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun y x => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
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
    apply (pp_ro_recip_prt_back).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer Γ e τ w)).
    pose ((has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    
    apply (pp_ro_coerce_prt).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }
  
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer Γ e τ w)).
    pose ((has_type_ro_OpZRexp_inverse _ _ w)) as w1.    
    apply (pp_ro_exp_prt).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_Int_infer Γ k τ w)).
    simpl.
    apply (pp_ro_int_prt_back).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_True_infer Γ τ w)).
    simpl.
    apply (pp_ro_true_prt_back).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_False_infer Γ τ w)).
    simpl.
    apply (pp_ro_false_prt_back).
    intros x1 x2; auto.
  }  
  
Defined.


Fixpoint simple_arithmetical_value_tot e (p : simple_arithmetical e) Γ τ (w : Γ |- e : τ)  :
  (sem_ro_ctx Γ -> Prop) * (sem_ro_ctx Γ -> sem_datatype τ).
Proof.
  dependent destruction p.
  exact (fun _ => True, ro_access _ _ _ w).

  destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x + snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x - snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x * snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x <? snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x =? snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x + snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x - snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x * snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x /\
                  (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) <> (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x)
         ,  
         fun x => Rltb'' (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x)))%R.

  destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x /\
                  (snd (simple_arithmetical_value_tot _ p _ _ w1) x <> 0%R)
         ,
         fun x => / snd (simple_arithmetical_value_tot _ p _ _ w1) x))%R.

  destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x
         ,
         fun x => IZR (snd (simple_arithmetical_value_tot _ p _ _ w1) x)))%R.

  destruct (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x
         ,
         fun x => pow2 (snd (simple_arithmetical_value_tot _ p _ _ w1) x)))%R.

  destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (
      (fun x => True,
         fun x => k))%Z.
  
  destruct (eq_sym (has_type_ro_True_infer _ _ w)).
  exact (
      (fun x => True,
         fun x => true))%Z.

  destruct (eq_sym (has_type_ro_False_infer _ _ w)).
  exact (
      (fun x => True,
         fun x => false))%Z.

Defined.

Fixpoint simple_arithmetical_tot e (p : simple_arithmetical e) Γ τ (w : Γ |- e : τ) :
  Γ |-- [{fst (simple_arithmetical_value_tot _ p _ _ w)}] e [{y : τ | fun x => y = snd (simple_arithmetical_value_tot _ p _ _ w) x}].
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_tot_back w).
    intros x _.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_plus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_minus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_mult_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_comp_lt_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_comp_eq_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_plus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_minus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_mult_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_comp_lt_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) /\  y <> (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).

    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_tot_pose_readonly
             (fun x =>
                (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) <>
                  (snd (simple_arithmetical_value_tot _ p2 _ _  w2) x))) in X.
             
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    split.
    exact x2.
    destruct x3.
    exact H0.
    split.
    destruct x3.
    exact H.
    destruct x3.
    rewrite H; exact H0.

    
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    destruct h1.
    split; auto.
    rewrite <- h2 in H0.
    exact H0.    
    rewrite H, h2; auto.
  }
  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
    pose ( (has_type_ro_OpRrecip_inverse _ _ w)) as w1.    
    
    apply (pp_ro_recip_tot_back).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_tot_pose_readonly
             (fun x => 
                (snd (simple_arithmetical_value_tot _ p _ _ w1) x) <> 0%R)) in X.
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    split.
    destruct H.
    auto.
    destruct H.
    auto.
    destruct x3.
    split.
    rewrite H; auto.
    rewrite H; auto.
  }

  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
    pose ( (has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    
    
    apply (pp_ro_coerce_tot).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
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
    
    apply (pp_ro_exp_tot).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    simpl in H.
    exact H.
    simpl.
    rewrite x3; auto.
  }

  {
    destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
    apply (pp_ro_int_tot_back).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_True_infer _ _ w)).
    apply (pp_ro_true_tot_back).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_False_infer _ _ w)).
    apply (pp_ro_false_tot_back).
    intros x _.
    reflexivity.
  }    
Defined.


Fixpoint simple_arithmetical_dec e : simple_arithmetical e + (simple_arithmetical e -> False).
Proof.
  dependent destruction e;
    try (left; constructor; auto; fail);
    try (destruct b; left; constructor; auto; fail).

  destruct (simple_arithmetical_dec e1).
  destruct (simple_arithmetical_dec e2).
  destruct b; constructor; auto; constructor; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  
  destruct (simple_arithmetical_dec e).
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
  right; intro.
  dependent destruction H.
Defined.


Ltac r_auto_typing_step :=
  try apply r_has_type_ro_Var_S;
  try apply r_has_type_ro_Var_0
  ;  try apply  r_has_type_ro_True
  ;  try apply  r_has_type_ro_False
  ;  try apply r_has_type_ro_Int
  ;  try apply r_has_type_ro_OpZplus
  ;  try apply r_has_type_ro_OpZminus
  ;  try apply r_has_type_ro_OpZmult
  ;  try apply r_has_type_ro_OpZlt
  ;  try apply r_has_type_ro_OpZeq
  ;  try apply r_has_type_ro_OpRplus
  ;  try apply r_has_type_ro_OpRminus
  ;  try apply r_has_type_ro_OpRlt
  ;  try apply r_has_type_ro_OpRmult
  ;  try apply r_has_type_ro_OpRrecip
  ;  try apply r_has_type_ro_OpZRcoerce
  ;  try apply r_has_type_ro_OpZRexp
  ;  try apply r_has_type_ro_Skip
  ;  try apply r_has_type_ro_rw_Seq
  ;  try apply r_has_type_ro_rw_Cond
  ;  try apply  r_has_type_ro_rw_Case 
  ;  try apply r_has_type_ro_rw_CaseList
  ;  try apply r_has_type_ro_rw_While
  ;  try apply r_has_type_ro_rw_Newvar
  ;  try apply r_has_type_ro_rw_Assign
  ;  try apply r_has_type_ro_Lim
  ;  try apply r_has_type_rw_ro_Var
  ;  try apply r_has_type_rw_ro_Boolean
  ;  try apply r_has_type_rw_ro_Integer
  ;  try apply r_has_type_rw_ro_BinOp
  ;  try apply r_has_type_rw_ro_UniOp
  ;  try apply r_has_type_rw_ro_Skip
  ;  try apply r_has_type_rw_Seq
  ;  try apply r_has_type_rw_Cond
  ;  try apply  r_has_type_rw_Case 
  ;  try apply r_has_type_rw_CaseList
  ;  try apply r_has_type_rw_While
  ;  try apply r_has_type_rw_Newvar
  ;  try apply r_has_type_rw_Assign
  ;  try apply r_has_type_rw_ro_Lim

  ; try  apply r_has_type_ro_Var_S
  ; try  apply r_has_type_ro_Var_0
  ; try  apply r_has_type_ro_True
  ; try  apply r_has_type_ro_False
  ; try  apply r_has_type_ro_Int
  ; try  apply r_has_type_ro_OpZplus
  ; try  apply r_has_type_ro_OpZminus
  ; try  apply r_has_type_ro_OpZmult
  ; try  apply r_has_type_ro_OpZlt
  ; try  apply r_has_type_ro_OpZeq
  ; try  apply r_has_type_ro_OpRplus
  ; try  apply r_has_type_ro_OpRminus
  ; try  apply r_has_type_ro_OpRlt
  ; try  apply r_has_type_ro_OpRmult
         
  ; try  apply r_has_type_ro_OpRrecip
  ; try  apply r_has_type_ro_OpZRcoerce
  ; try  apply r_has_type_ro_OpZRexp
         
  ; try  apply r_has_type_ro_Skip
  ; try  apply r_has_type_ro_rw_Seq
  ; try  apply r_has_type_ro_rw_Cond
  ; try  apply r_has_type_ro_rw_Case 
      ; try  apply r_has_type_ro_rw_CaseList
      ; try  apply r_has_type_ro_rw_While
      ; try  apply r_has_type_ro_rw_Newvar
      ; try  apply r_has_type_ro_rw_Assign
      ; try  apply r_has_type_ro_Lim
      ; try  apply r_has_type_rw_ro_Var
      ; try  apply r_has_type_rw_ro_Boolean
      ; try  apply r_has_type_rw_ro_Integer
      ; try  apply r_has_type_rw_ro_BinOp
      ; try  apply r_has_type_rw_ro_UniOp
      ; try  apply r_has_type_rw_ro_Skip
      ; try  apply r_has_type_rw_Seq
      ; try  apply r_has_type_rw_Cond
  ; try  apply r_has_type_rw_Case 
      ; try  apply r_has_type_rw_CaseList
      ; try  apply r_has_type_rw_While
      ; try  apply r_has_type_rw_Newvar
      ; try  apply r_has_type_rw_Assign
      ; try  apply r_has_type_rw_ro_Lim.


Ltac auto_typing  :=
  try (apply r_has_type_ro_has_type_ro);
  try (apply r_has_type_rw_has_type_rw);
  repeat r_auto_typing_step;
  try (apply has_type_ro_r_has_type_ro);
  try (apply has_type_rw_r_has_type_rw);
  auto.

Ltac decide_simple_arithmetic e X Xdefi :=
  let v := fresh "tmp" in 
  case_eq (simple_arithmetical_dec
             e
          );
  intros X v; [simpl in v; injection v; intro Xdefi; clear v |simpl in v; discriminate v].

Ltac unfold_stuffs :=
  unfold rw_to_ro_pre;
  unfold ro_to_rw_pre.
  
Ltac auto_imp :=
  match goal with
  |  |- asrt_imp _ _ =>
       let v1 := fresh "tmp" in
       let v2 := fresh "tmp" in
       let v3 := fresh "tmp" in
       let w1 := fresh "tmp" in
       let w2 := fresh "tmp" in
       let w3 := fresh "tmp" in
       unfold_stuffs;
       intros v1 v2;
       repeat destruct v1;
       repeat destruct v2;
       repeat split;
       auto
  |  |- asrt_imp2 _ _ =>
       let v1 := fresh "tmp" in
       let v2 := fresh "tmp" in
       let v3 := fresh "tmp" in
       let w1 := fresh "tmp" in
       let w2 := fresh "tmp" in
       let w3 := fresh "tmp" in
       unfold_stuffs;
       intros v1 v2 v3;
       repeat destruct v1;
       repeat destruct v2;
       repeat destruct v3;
       repeat split;
       auto
  end.

       
Ltac proves_simple_arithmetical :=
  match goal with
  | |- proves_ro_prt_pp ?Γ ?e ?τ ?ϕ ?ψ =>
      
      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_simple_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (simple_arithmetical_prt Γ e τ v3 v1) as v4;
      
      apply (pp_ro_prt_pose_readonly ϕ) in v4;

      simpl in v4;
      
      apply (pp_ro_imply_prt v4); clear v4;

      try (auto_imp; fail);
      rewrite <- v2; clear v2;
      easy_rewrite_uip;

      intros y x [val pre];

      repeat (
          try (destruct has_type_ro_OpZplus_inverse);
          try (destruct has_type_ro_OpZminus_inverse);
          try (destruct has_type_ro_OpZmult_inverse);
          try (destruct has_type_ro_OpZlt_inverse);
          try (destruct has_type_ro_OpZeq_inverse);
          try (destruct has_type_ro_OpRplus_inverse);
          try (destruct has_type_ro_OpRminus_inverse);
          try (destruct has_type_ro_OpRmult_inverse);
          try (destruct has_type_ro_OpRlt_inverse);
          try (destruct has_type_ro_OpRrecip_inverse);
          try (destruct has_type_ro_OpZRexp_inverse);
          try (destruct has_type_ro_OpZRcoerce_inverse);
          try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)) in v);
          try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)) in v);
          try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)) in v);
          simpl in v)

             
             
          

  | |- proves_ro_tot_pp ?Γ ?e ?τ ?ϕ ?ψ =>

      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_simple_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (simple_arithmetical_tot _ v1 _ _  v3) as v4;
      
      apply (pp_ro_tot_pose_readonly (Γ := Γ) ϕ) in v4;

      simpl in v4;
      
      apply (pp_ro_imply_tot v4); clear v4;
      rewrite <- v2; clear v2; easy_rewrite_uip;
      [
        intros x p;
        split;
        [
          repeat (
              try (destruct has_type_ro_OpZplus_inverse);
              try (destruct has_type_ro_OpZminus_inverse);
              try (destruct has_type_ro_OpZmult_inverse);
              try (destruct has_type_ro_OpZlt_inverse);
              try (destruct has_type_ro_OpZeq_inverse);
              try (destruct has_type_ro_OpRplus_inverse);
              try (destruct has_type_ro_OpRminus_inverse);
              try (destruct has_type_ro_OpRmult_inverse);
              try (destruct has_type_ro_OpRlt_inverse);
              try (destruct has_type_ro_OpRrecip_inverse);
              try (destruct has_type_ro_OpZRexp_inverse);
              try (destruct has_type_ro_OpZRcoerce_inverse);
              try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)));
              simpl); auto

        |
          auto          
        ]
      |               
        intros y x [v p];

        repeat (
            try (destruct has_type_ro_OpZplus_inverse);
            try (destruct has_type_ro_OpZminus_inverse);
            try (destruct has_type_ro_OpZmult_inverse);
            try (destruct has_type_ro_OpZlt_inverse);
            try (destruct has_type_ro_OpZeq_inverse);
            try (destruct has_type_ro_OpRplus_inverse);
            try (destruct has_type_ro_OpRminus_inverse);
            try (destruct has_type_ro_OpRmult_inverse);
            try (destruct has_type_ro_OpRlt_inverse);
            try (destruct has_type_ro_OpRrecip_inverse);
            try (destruct has_type_ro_OpZRexp_inverse);
            try (destruct has_type_ro_OpZRcoerce_inverse);
            try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)) in v);
            try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)) in v);
            try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)) in v);
            simpl in v); auto
      ]

  | |- proves_rw_tot_pp ?Γ ?Δ ?e ?τ ?ϕ ?ψ =>
      apply (pp_rw_ro_tot_back (τ := τ));
      proves_simple_arithmetical

  | |- proves_rw_prt_pp ?Γ ?Δ ?e ?τ ?ϕ ?ψ =>
      apply (pp_rw_ro_prt_back (τ := τ));
      proves_simple_arithmetical

  | _ => idtac "bbb"
  end.

Lemma Rltb''_prop : forall x y, Rltb'' x y = true <-> (x < y)%R.
Proof.
  intros.
  unfold Rltb''.
  destruct (total_order_T x y).
  destruct s.
  split; auto.
  split.
  intro.
  contradict H; discriminate.
  intro.
  rewrite e in H.
  contradict (Rlt_irrefl _ H).
  split; intro.
  contradict H; discriminate.
  contradict (Rlt_asym _ _ r H).
Defined.

Notation "':-:' e" := (BinOp OpZminus ( (INT 0)) e) (at level 45, right associativity) : clerical_scope.
Notation "';-;' e" := (BinOp OpRminus (RE (INT 0)) e) (at level 45, right associativity) : clerical_scope.

(* computing the absolute value of variable k *)
Definition exp_abs k :=  
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1))
       ==> ;-; VAR (S k)
       OR
       ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) 
       ==> VAR (S k)
       END)
.

Lemma exp_abs_wty :
  forall Γ k, Γ |- VAR k : REAL ->
                         Γ |- exp_abs k : REAL. 
  intros.
  auto_typing.
Defined.

Require Import Reals.
Open Scope R.

Lemma exp_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    Γ |--
      [{fun _ => True}]
      exp_abs k 
      [{y : REAL | fun x => y = Rabs (ro_access Γ k REAL w x) }].
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun x =>  Rabs (ro_access Γ k REAL w x)));
    try (intros h1 h2 [_ h3]; auto; fail).
  apply (pp_ro_rw_tot_back).
  apply (pp_rw_case_tot
           (Γ := (INTEGER :: Γ))
           (θ1 := ( fun b x => b = true -> (ro_access _ _ _ w (snd (snd_app x))) <
                                      pow2 (- ((fst (snd_app x))) - 1)%Z))
           (θ2 := ( fun b x => b = true -> - (ro_access _ _ _ w (snd (snd_app x))) <
                                      pow2 (- ((fst (snd_app x))) - 1)%Z))
           
           (ϕ1 := ( fun x =>  (ro_access _ _ _ w (snd (snd_app x))) <
                         pow2 (- ((fst (snd_app x))) - 1)%Z))
           (ϕ2 := ( fun x =>  - pow2 (- ((fst (snd_app x))) - 1)%Z < (ro_access _ _ _ w (snd (snd_app x)))))
        ); simpl.
  
  proves_simple_arithmetical.
  intro e.
  rewrite e in val.
  apply eq_sym in val.
  apply (proj1 (Rltb''_prop _ _)) in val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S, ro_access_Var_0 in val.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inv Γ k INTEGER REAL h)).
  exact val.

  proves_simple_arithmetical.
  intro e.
  rewrite e in val.
  apply eq_sym in val.
  apply (proj1 (Rltb''_prop _ _)) in val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S, ro_access_Var_0 in val.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inv Γ k INTEGER REAL h0)).
  Require Import Lra.
  lra.

  proves_simple_arithmetical.
  unfold ro_to_rw_pre in pre.
  pose proof (pre eq_refl).
  rewrite val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S.
  simpl in H.
  
  admit.

  proves_simple_arithmetical.
  admit.

  proves_simple_arithmetical.
  repeat split; auto.
  admit.
  admit.

  proves_simple_arithmetical.
  repeat split; auto.
  admit.
  admit.


  
  
  
