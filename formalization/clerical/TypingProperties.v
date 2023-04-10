Require Import Clerical.
Require Import Typing.
Require Import List.
Require Import Coq.Program.Equality.

Fixpoint unamb_Var_0 Γ τ σ (w : (σ :: Γ) |- Var 0 : τ) : σ = τ.
Proof.
  inversion w.
  inversion H.
  simpl in H7.
  apply (unamb_Var_0 _ _ _ H7).
  auto.
Defined.

Fixpoint has_type_ro_Var_S_inv  Γ k τ a (H : (a :: Γ) |- VAR S k : τ) : Γ |- Var k : τ.
Proof.
  intros.
  inversion H.
  inversion H0.
  apply (has_type_ro_Var_S_inv _ _ _ _ H8).
  exact H4.
Defined.

Fixpoint has_type_ro_Var_absurd k τ (w : nil |- Var k : τ) : False.
Proof.
  inversion w.
  inversion H.
  apply ( has_type_ro_Var_absurd _ _ H7).
Defined.


Definition unamb_Var k Γ τ σ (w1 : Γ |- Var k : τ) (w2 : Γ |- Var k : σ) : τ = σ.
Proof.
  generalize Γ τ σ w1 w2.
  clear Γ τ σ w1 w2.
  induction k.
  intros.
  destruct Γ.
  contradict (has_type_ro_Var_absurd _ _ w1).
  rewrite <- (unamb_Var_0 _ _ _ w1).
  rewrite <- (unamb_Var_0 _ _ _ w2).
  auto.
  intros.
  destruct Γ.
  contradict (has_type_ro_Var_absurd _ _ w1).
  apply (IHk _ _ _ (has_type_ro_Var_S_inv _ _ _ _ w1) (has_type_ro_Var_S_inv _ _ _ _ w2)).
Defined.

Fixpoint unamb_True Γ τ (w : Γ |- TRUE : τ) : τ = BOOL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_True _ _ H7).
  auto.
Defined.

Fixpoint unamb_False Γ τ (w : Γ |- FALSE : τ) : τ = BOOL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_False _ _ H7).
  auto.
Defined.

Fixpoint unamb_Skip Γ τ (w : Γ |- SKIP : τ) : τ = UNIT.
Proof.
  inversion w.
  inversion H.
  apply (unamb_Skip _ _ H7).
  auto.
Defined.

Fixpoint unamb_Int Γ k τ (w : Γ |- INT k : τ) : τ = INTEGER.
Proof.
  inversion w.
  inversion H.
  apply (unamb_Int _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpRrecip Γ e τ (w : Γ |- ;/; e : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpRrecip _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpZRcoerce Γ e τ (w : Γ |- RE e : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZRcoerce _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpZRexp Γ e τ (w : Γ |- EXP e : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZRexp _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpZplus Γ e1 e2 τ (w : Γ |-  (e1 :+: e2) : τ) : τ = INTEGER.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZplus _ _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpZmult Γ e1 e2 τ (w : Γ |-  (e1 :*: e2) : τ) : τ = INTEGER.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZmult _ _ _ _ H7).
  auto.
Defined.

Fixpoint unamb_OpZminus Γ e1 e2 τ (w : Γ |-  (e1 :-: e2) : τ) : τ = INTEGER.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZminus _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpZeq Γ e1 e2 τ (w : Γ |-  (e1 :=: e2) : τ) : τ = BOOL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZeq _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpZlt Γ e1 e2 τ (w : Γ |-  (e1 :<: e2) : τ) : τ = BOOL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpZlt _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpRplus Γ e1 e2 τ (w : Γ |-  (e1 ;+; e2) : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpRplus _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpRminus Γ e1 e2 τ (w : Γ |-  (e1 ;-; e2) : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpRminus _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpRmult Γ e1 e2 τ (w : Γ |-  (e1 ;*; e2) : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpRmult _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_OpRlt Γ e1 e2 τ (w : Γ |-  (e1 ;<; e2) : τ) : τ = BOOL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_OpRlt _ _ _ _ H7).
  auto.
Defined.


Fixpoint unamb_Lim Γ e τ (w : Γ |-  Lim e : τ) : τ = REAL.
Proof.
  inversion w.
  inversion H.
  apply (unamb_Lim  _ _ _ H7).
  auto.
Defined.

Definition ro_in_rw Γ Δ c τ (w : (Δ ++ Γ) ;;; nil ||- c : τ) : (Γ ;;; Δ ||- c : τ).
Proof.
  apply has_type_rw_ro.
  apply has_type_ro_rw.
  exact w.
Defined.
  
Fixpoint has_type_rw_Seq_inv Γ Δ c1 c2 τ (w3 : Γ ;;; Δ ||- (c1 ;; c2) : τ) : (Γ ;;; Δ ||- c2 : τ).
Proof.
  inversion w3.
  inversion H3.
  pose proof (has_type_rw_Seq_inv _ _ _ _ _ H4).
  apply ro_in_rw.
  exact H8.
  exact H5.
Defined.

(* Fixpoint unamb_Seq Γ Δ c1 c2 τ σ (w : Γ ;;; Δ ||- (c1 ;; c2) : τ) : (Γ ;;; Δ ||- c2 : σ) -> τ = σ. *)
(* Proof. *)
(*   intro. *)
(*   inversion w. *)
(*   inversion H4. *)
  

(* Fixpoint unamb_Seq Γ Δ c1 c2 τ σ (w : Γ ;;; Δ ||- (c1 ;; c2) : τ) (w' : Γ ;;; Δ ||- (c1 ;; c2) : σ) : τ = σ. *)
(* Proof. *)
(*   inversion w. *)
(*   inversion w'. *)
(*   inversion H3. *)
(*   inversion H8. *)
(*   apply (unamb_Seq _ _ _ _ _ _ H9 H13). *)
(*   inversion H3. *)
(*   inversion H11. *)
  
(*   inversion H3. *)
(*   pose proof (has_type_rw_Seq_inv _ _ _ _ _ H4). *)
(*   apply ro_in_rw. *)
(*   exact H8. *)
(*   exact H5. *)
(* Defined. *)
(* Fixpoint has_type_ro_unambiguous Γ e τ σ (w1 : Γ |- e : τ) (w2 : Γ |- e : σ) : τ = σ. *)
(* Proof. *)
(*   destruct e. *)
(*   apply (unamb_Var _ _ _ _ w1 w2). *)
(*   destruct b. *)
(*   rewrite (unamb_True _ _ w1). *)
(*   rewrite (unamb_True _ _ w2). *)
(*   auto. *)
(*   rewrite (unamb_False _ _ w1), (unamb_False _ _ w2); auto. *)
(*   rewrite (unamb_Int _ _ _ w1), (unamb_Int _ _ _ w2); auto. *)
(*   destruct b. *)
(*   rewrite (unamb_OpZplus _ _ _ _ w1), (unamb_OpZplus _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZminus _ _ _ _ w1), (unamb_OpZminus _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZmult _ _ _ _ w1), (unamb_OpZmult _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZlt _ _ _ _ w1), (unamb_OpZlt _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZeq _ _ _ _ w1), (unamb_OpZeq _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpRplus _ _ _ _ w1), (unamb_OpRplus _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpRminus _ _ _ _ w1), (unamb_OpRminus _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpRlt _ _ _ _ w1), (unamb_OpRlt _ _ _ _ w2); auto. *)
(*   rewrite (unamb_OpRmult _ _ _ _ w1), (unamb_OpRmult _ _ _ _ w2); auto. *)
(*   destruct u. *)
(*   rewrite (unamb_OpRrecip _ _ _ w1), (unamb_OpRrecip _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZRcoerce _ _ _ w1), (unamb_OpZRcoerce _ _ _ w2); auto. *)
(*   rewrite (unamb_OpZRexp _ _ _ w1), (unamb_OpZRexp _ _ _ w2); auto. *)
(*   rewrite (unamb_Skip _ _ w1), (unamb_Skip _ _ w2); auto. *)
(*   inversion w1. *)
(*   inversion H. *)
(*   apply (has_type_ro_unambiguous _ _ _ _ H7 w2). *)
(*   inversion w2. *)
(*   inversion H10. *)
(*   contradict magic. *)

(*   (* apply (has_type_ro_unambiguous _ _ _ _ w1 H18). *) *)

(*   apply (has_type_ro_unambiguous _ _ _ _ (has_type_ro_rw _ _ _ H9) (has_type_ro_rw _ _ _ H20)). *)
  
(*   contradict magic. *)
(*   contradict magic. *)
(*   contradict magic. *)
(*   contradict magic. *)
(*   contradict magic. *)
(*   contradict magic. *)
(* Defined. *)


(*   inversion w2. *)
(*   inversion H. *)
(*   inversion H3. *)
(*   apply (has_type_ro_unambiguous _ _ _ _ H11 H16). *)

(*   inversion w1. *)
(*   inversion w2. *)
(*   apply (has_type_rw_unambiguous _ _ _ _ _ H H3). *)
(*   inversion w1. *)
(*   inversion w2. *)
(*   apply (has_type_rw_unambiguous _ _ _ _ _ H H3). *)
(*   inversion w1. *)
(*   inversion w2. *)
(*   apply (has_type_rw_unambiguous _ _ _ _ _ H H3). *)
(*   inversion w1. *)
(*   inversion w2. *)
(*   apply (has_type_rw_unambiguous _ _ _ _ _ H H3). *)
(*   inversion w1. *)
(*   inversion w2. *)
(*   apply (has_type_rw_unambiguous _ _ _ _ _ H H3). *)
(*   rewrite (unamb_Lim _ _ _ w1), (unamb_Lim _ _ _ w2); auto. *)


(* intros. *)


Fixpoint ro_assign_absurd Γ k e (w : Γ |- Assign k e : DUnit) : False.
Proof.
  inversion w.
  inversion H.
  simpl in H7.
  apply (ro_assign_absurd Γ k e H7) .
  contradict H6.
  intro.
  inversion H6.
Defined.

Reserved Notation " Γ |~ t : T " (at level 50, t, T at next level). 
Reserved Notation " Γ ;;; Δ ||~ t : T " (at level 50, Δ, t, T at next level). 


Inductive phas_type_ro : ro_ctx -> comp -> datatype -> Type :=
(* from readwrite *)
| phas_type_ro_rw_Seq : forall Γ c1 c2 τ, Γ ;;; nil ||~ (c1 ;; c2) : τ -> Γ |~ (c1 ;; c2) : τ 

| phas_type_ro_rw_Assign : forall Γ e k, Γ ;;; nil ||~ (Assign k e) : DUnit -> Γ |~ (Assign k e) : DUnit
                                                                                                     
| phas_type_ro_rw_Newvar : forall Γ e c τ, Γ ;;; nil ||~ (Newvar e c) : τ -> Γ |~ (Newvar e c) : τ

| phas_type_ro_rw_Cond : forall Γ e c1 c2 τ, Γ ;;; nil ||~ (Cond e c1 c2) : τ -> Γ |~ (Cond e c1 c2) : τ

| phas_type_ro_rw_Case : forall Γ e1 c1 e2 c2 τ,
    Γ ;;; nil ||~ (Case e1 c1 e2 c2) : τ -> Γ |~ (Case e1 c1 e2 c2) : τ
                                                                                                                               
| phas_type_ro_rw_While : forall Γ e c, Γ ;;; nil ||~ (While e c) : DUnit -> Γ |~ (While e c) : DUnit
                                                                                              
(* variables *)
| phas_type_ro_Var_0 : forall Γ τ,  ((τ :: Γ) |~ (VAR 0) : τ)
| phas_type_ro_Var_S : forall Γ σ τ k, Γ |~ Var k : τ -> (σ :: Γ) |~ VAR (S k) : τ

(* constants *)
| phas_type_ro_True : forall Γ, Γ |~ TRUE : DBoolean
| phas_type_ro_False : forall Γ, Γ |~ FALSE : DBoolean
| phas_type_ro_Skip : forall Γ, Γ |~ SKIP : DUnit
| phas_type_ro_Int : forall Γ k, Γ |~ INT k : DInteger

(* unary ops *)
| phas_type_ro_OpRrecip : forall Γ e, Γ |~ e : DReal -> Γ |~ (UniOp OpRrecip e) : DReal
| phas_type_ro_OpZRcoerce : forall Γ e, Γ |~ e : DInteger -> Γ |~ (UniOp OpZRcoerce e) : DReal
| phas_type_ro_OpZRexp : forall Γ e, Γ |~ e : DInteger -> Γ |~ (UniOp OpZRexp e) : DReal

(* binary ops *)
| phas_type_ro_OpZplus : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZplus e1 e2) : DInteger
| phas_type_ro_OpZminus : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZminus e1 e2) : DInteger
| phas_type_ro_OpZmult : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZmult e1 e2) : DInteger
| phas_type_ro_OpZlt : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZlt e1 e2) : DBoolean
| phas_type_ro_OpZeq : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZeq e1 e2) : DBoolean 
| phas_type_ro_OpRplus : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRplus e1 e2) : DReal
| phas_type_ro_OpRminus : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRminus e1 e2) : DReal
| phas_type_ro_OpRmult : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRmult e1 e2) : DReal
| phas_type_ro_OpRlt : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRlt e1 e2) : DBoolean

(* limit *)
| phas_type_ro_Lim : forall Γ e, (DInteger :: Γ) |~ e : DReal -> Γ |~ Lim e : DReal
                                                                                                         
with phas_type_rw : rw_ctx -> comp -> datatype -> Type :=
(* from readonly *)
| phas_type_rw_ro_Var :
  forall Γ Δ k τ,
    (Δ ++ Γ) |~ Var k : τ -> Γ ;;; Δ ||~ Var k : τ
| phas_type_rw_ro_Boolean :
  forall Γ Δ b,
    (Δ ++ Γ) |~ Boolean b : DBoolean -> Γ ;;; Δ ||~ Boolean b : DBoolean
| phas_type_rw_ro_Integer :
  forall Γ Δ k,
    (Δ ++ Γ) |~ Integer k : DInteger -> Γ ;;; Δ ||~ Integer k : DInteger
| phas_type_rw_ro_BinOp :
  forall Γ Δ e1 e2 τ op,
    (Δ ++ Γ) |~ BinOp op e1 e2 : τ -> Γ ;;; Δ ||~ BinOp op e1 e2 : τ
| phas_type_rw_ro_UniOp :
  forall Γ Δ e τ op,
    (Δ ++ Γ) |~ UniOp op e : τ -> Γ ;;; Δ ||~ UniOp op e : τ
| phas_type_rw_ro_Skip :
  forall Γ Δ ,
    (Δ ++ Γ) |~ Skip : DUnit -> Γ ;;; Δ ||~ Skip : DUnit
                  
| phas_type_rw_ro_Lim :
  forall Γ Δ  e,
    (Δ ++ Γ) |~ Lim e : DReal -> Γ ;;; Δ ||~ Lim e : DReal

(* sequential *)
| phas_type_rw_Seq : forall Γ Δ c1 c2 τ, Γ ;;; Δ ||~ c1 : DUnit -> Γ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ (Seq c1 c2) : τ 
                                                                        
(* assignment *)
| phas_type_rw_Assign : forall Γ Δ e τ k, assignable Δ τ k -> (Δ ++ Γ) |~ e : τ -> Γ ;;; Δ ||~ Assign k e : DUnit

(* newvar *)
| phas_type_rw_Newvar : forall Γ Δ e c σ τ, (Δ ++ Γ) |~ e : σ -> Γ ;;; σ :: Δ ||~ c : τ -> Γ ;;; Δ ||~ Newvar e c : τ

(* cond *)
| phas_type_rw_Cond : forall Γ Δ e c1 c2 τ, (Δ ++ Γ) |~ e : DBoolean -> Γ ;;; Δ ||~ c1 : τ -> Γ ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ Cond e c1 c2 : τ

(* case *)
| phas_type_rw_Case : forall Γ Δ e1 c1 e2 c2 τ, (Δ ++ Γ) |~ e1 : DBoolean -> Γ ;;; Δ ||~ c1 : τ -> (Δ ++ Γ) |~ e2 : DBoolean -> Γ ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ Case e1 c1 e2 c2 : τ

(* while *)
| phas_type_rw_While : forall Γ Δ e c, (Δ ++ Γ) |~ e : DBoolean -> Γ ;;; Δ ||~ c : DUnit -> Γ ;;; Δ ||~ While e c : DUnit
                                                                                                                                                                 
                                                                                                             
where " Γ |~ c : τ " := (phas_type_ro Γ c τ) and " Γ ;;; Δ ||~ c : τ " := (phas_type_rw (mk_rw_ctx Γ Δ) c τ).

Axiom mymagic : forall A : Type, A.

Lemma assignable_push_back Γ Δ k τ (t : assignable Γ k τ) : assignable (Γ ++ Δ) k τ.
Proof.
  induction t.
  simpl.
  constructor.
  constructor.
  exact IHt.
Defined.
  
Fixpoint phas_type_rw_move Γ Δ1 Δ2 e τ (w : (Δ2 ++ Γ) ;;; Δ1 ||~ e : τ) : Γ ;;; (Δ1 ++ Δ2) ||~ e : τ.
Proof.
  inversion w.
  apply phas_type_rw_ro_Var; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_Boolean; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_Integer; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_BinOp; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_UniOp; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_Skip; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply phas_type_rw_ro_Lim; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  pose proof (phas_type_rw_move _ _ _ _ _ H1).
  pose proof (phas_type_rw_move _ _ _ _ _ H4).
  apply phas_type_rw_Seq; auto.
  apply (phas_type_rw_Assign _ _ _ τ0).
  apply assignable_push_back; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply (phas_type_rw_Newvar _ _ _ _ σ); auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  replace ((σ :: Δ1 ++ Δ2)) with ((σ :: Δ1) ++ Δ2) by apply app_comm_cons.
  apply phas_type_rw_move; auto.
  apply (phas_type_rw_Cond _ _ _ _ _); auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply (phas_type_rw_Case _ _ _ _ _); auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  apply (phas_type_rw_While _ _ _ _); auto.
  replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
Qed.



Fixpoint unamb_Var_0' Γ τ σ (w : (σ :: Γ) |~ Var 0 : τ) : σ = τ.
Proof.
  inversion w.
  auto.
Defined.

Fixpoint phas_type_ro_Var_S_inv  Γ k τ a (H : (a :: Γ) |~ VAR S k : τ) : Γ |~ Var k : τ.
Proof.
  intros.
  inversion H.
  inversion H0.
  auto.
Defined.

Fixpoint phas_type_ro_Var_absurd k τ (w : nil |~ Var k : τ) : False.
Proof.
  inversion w.
Defined.


Definition unamb_Var' k Γ τ σ (w1 : Γ |~ Var k : τ) (w2 : Γ |~ Var k : σ) : τ = σ.
Proof.
  generalize Γ τ σ w1 w2.
  clear Γ τ σ w1 w2.
  induction k.
  intros.
  destruct Γ.
  contradict (phas_type_ro_Var_absurd _ _ w1).
  rewrite <- (unamb_Var_0' _ _ _ w1).
  rewrite <- (unamb_Var_0' _ _ _ w2).
  auto.
  intros.
  destruct Γ.
  contradict (phas_type_ro_Var_absurd _ _ w1).
  apply (IHk _ _ _ (phas_type_ro_Var_S_inv _ _ _ _ w1) (phas_type_ro_Var_S_inv _ _ _ _ w2)).
Defined.
  
Fixpoint has_type_ro_phas_type_ro Γ e τ (w : Γ |- e : τ) {struct w}: Γ |~ e : τ
with has_type_rw_phas_type_rw Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) {struct w}: Γ ;;; Δ ||~ e : τ.
Proof.
  +
    inversion w.
    inversion H.
    apply (has_type_ro_phas_type_ro _ _ _ H7).
    apply phas_type_ro_rw_Seq.
    apply phas_type_rw_Seq.
    apply has_type_rw_phas_type_rw; auto.
    apply has_type_rw_phas_type_rw; auto.
    apply phas_type_ro_rw_Assign.
    apply (phas_type_rw_Assign _ _ _ τ1); auto.
    apply phas_type_ro_rw_Newvar.
    apply (phas_type_rw_Newvar _ _ _ _ σ); auto.
    apply phas_type_ro_rw_Cond.
    apply (phas_type_rw_Cond _ _ _ _ _ τ); auto.
    apply phas_type_ro_rw_Case.
    apply (phas_type_rw_Case _ _ _ _ _ _ τ); auto.
    apply phas_type_ro_rw_While.
    apply (phas_type_rw_While _ _ _ _); auto.
    apply phas_type_ro_Var_0; auto.
    apply phas_type_ro_Var_S; auto.
    apply phas_type_ro_True.
    apply phas_type_ro_False.
    apply phas_type_ro_Skip.
    apply phas_type_ro_Int.
    apply phas_type_ro_OpRrecip; auto.
    apply phas_type_ro_OpZRcoerce; auto.
    apply phas_type_ro_OpZRexp; auto.
    apply phas_type_ro_OpZplus; auto.
    apply phas_type_ro_OpZminus; auto.
    apply phas_type_ro_OpZmult; auto.
    apply phas_type_ro_OpZlt; auto.
    apply phas_type_ro_OpZeq; auto.
    apply phas_type_ro_OpRplus; auto.
    apply phas_type_ro_OpRminus; auto.
    apply phas_type_ro_OpRmult; auto.
    apply phas_type_ro_OpRlt; auto.
    apply phas_type_ro_Lim; auto.
  +
    dependent destruction w.
    dependent destruction h.
    apply has_type_rw_phas_type_rw in h.
    apply phas_type_rw_move in h.
    exact h.
    apply phas_type_rw_ro_Var.
    rewrite <- x.
    apply phas_type_ro_Var_0.
    apply phas_type_rw_ro_Var.
    rewrite <- x.
    apply phas_type_ro_Var_S; auto.
    apply phas_type_rw_ro_Boolean.
    apply phas_type_ro_True.
    apply phas_type_rw_ro_Boolean.
    apply phas_type_ro_False.
    apply phas_type_rw_ro_Skip; constructor.
    apply phas_type_rw_ro_Integer; constructor.
    apply phas_type_rw_ro_UniOp.
    apply has_type_ro_phas_type_ro in h.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h.
    constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h.
    constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h1;
      apply has_type_ro_phas_type_ro in h2;
      constructor; auto.
    constructor; auto.

    apply has_type_ro_phas_type_ro in h;
      constructor; auto.
    constructor; auto.
    
    apply has_type_rw_phas_type_rw in w1;
      apply has_type_rw_phas_type_rw in w2.
    constructor; auto.
    apply has_type_ro_phas_type_ro in h.
    apply (phas_type_rw_Assign _ _ _ τ); auto.
    apply has_type_ro_phas_type_ro in h;
      apply has_type_rw_phas_type_rw in w.
    apply (phas_type_rw_Newvar _ _ _ _ σ); auto.
    apply has_type_ro_phas_type_ro in h;
      apply has_type_rw_phas_type_rw in w1;
      apply has_type_rw_phas_type_rw in w2.
    apply (phas_type_rw_Cond); auto.
    apply has_type_ro_phas_type_ro in h;
    apply has_type_ro_phas_type_ro in h0;
      apply has_type_rw_phas_type_rw in w1;
      apply has_type_rw_phas_type_rw in w2.
    apply (phas_type_rw_Case); auto.
    apply has_type_ro_phas_type_ro in h;
      apply has_type_rw_phas_type_rw in w.
    apply (phas_type_rw_While); auto.
Defined.


 
Fixpoint phas_type_ro_unambiguous Γ e τ σ (w1 : Γ |~ e : τ){struct w1} : (Γ |~ e : σ) -> τ = σ
with phas_type_rw_unambiguous Γ Δ e τ σ (w1 : Γ ;;; Δ ||~ e : τ){struct w1} : ( Γ ;;; Δ ||~ e  : σ)  -> τ = σ.
Proof.
  +
    intro w2.
    dependent destruction w1;
      dependent destruction w2; auto.
    dependent destruction p.
    dependent destruction p0.
    apply (phas_type_rw_unambiguous _ _ _ _ _ p2 p0_2).
    dependent destruction p.
    dependent destruction p1.
    rewrite (phas_type_ro_unambiguous _ _ _ _ p p1) in p0.
    apply (phas_type_rw_unambiguous _ _ _ _ _ p0 p2).
    dependent destruction p.
    dependent destruction p0.
    apply (phas_type_rw_unambiguous _ _ _ _ _ p2 p0_1).
    dependent destruction p.
    dependent destruction p0.
    apply (phas_type_rw_unambiguous _ _ _ _ _ p2 p0_1).
    apply (unamb_Var' _ _ _ _ w1 w2).
  +
    intro w2.
    dependent destruction w1;
      dependent destruction w2; auto.
    apply (unamb_Var' _ _ _ _ p p0).
    dependent destruction p;
      dependent destruction p0; auto.
    dependent destruction p;
      dependent destruction p0; auto.
    apply (phas_type_rw_unambiguous _ _ _ _ _ w1_2 w2_2).
    rewrite (phas_type_ro_unambiguous _ _ _ _ p p0) in w1.
    apply (phas_type_rw_unambiguous _ _ _ _ _ w1 w2).
    apply (phas_type_rw_unambiguous _ _ _ _ _ w1_1 w2_1).
    apply (phas_type_rw_unambiguous _ _ _ _ _ w1_1 w2_1).
Defined.

Lemma has_type_ro_unambiguous Γ e τ σ :  Γ |- e : τ -> Γ |- e : σ -> τ = σ.
Proof.
  intros w1 w2.
  apply has_type_ro_phas_type_ro in w1.
  apply has_type_ro_phas_type_ro in w2.
  apply (phas_type_ro_unambiguous _ _ _ _ w1 w2).
Defined.

Lemma has_type_rw_unambiguous Γ Δ e τ σ : Γ ;;; Δ ||- e : τ -> Γ ;;; Δ ||- e  : σ -> τ = σ.
Proof.
  intros w1 w2.
  apply has_type_rw_phas_type_rw in w1.
  apply has_type_rw_phas_type_rw in w2.
  apply (phas_type_rw_unambiguous _ _ _ _ _ w1 w2).
Defined.
