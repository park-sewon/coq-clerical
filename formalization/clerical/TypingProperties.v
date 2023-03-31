Require Import Clerical.
Require Import Typing.
Require Import List.

Axiom magic : False.

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


Fixpoint has_type_ro_unambiguous Γ e τ σ (w1 : Γ |- e : τ) (w2 : Γ |- e : σ) : τ = σ
with has_type_ro_unambiguous' Γ e τ σ (w1 : Γ ;;; nil ||- e : τ){struct w1} : ( Γ ;;; nil ||- e  : σ)  -> τ = σ.
  +
    destruct e.
    apply (unamb_Var _ _ _ _ w1 w2).
    destruct b.
    rewrite (unamb_True _ _ w1).
    rewrite (unamb_True _ _ w2).
    auto.
    rewrite (unamb_False _ _ w1), (unamb_False _ _ w2); auto.
    rewrite (unamb_Int _ _ _ w1), (unamb_Int _ _ _ w2); auto.
    destruct b.
    rewrite (unamb_OpZplus _ _ _ _ w1), (unamb_OpZplus _ _ _ _ w2); auto.
    rewrite (unamb_OpZminus _ _ _ _ w1), (unamb_OpZminus _ _ _ _ w2); auto.
    rewrite (unamb_OpZmult _ _ _ _ w1), (unamb_OpZmult _ _ _ _ w2); auto.
    rewrite (unamb_OpZlt _ _ _ _ w1), (unamb_OpZlt _ _ _ _ w2); auto.
    rewrite (unamb_OpZeq _ _ _ _ w1), (unamb_OpZeq _ _ _ _ w2); auto.
    rewrite (unamb_OpRplus _ _ _ _ w1), (unamb_OpRplus _ _ _ _ w2); auto.
    rewrite (unamb_OpRminus _ _ _ _ w1), (unamb_OpRminus _ _ _ _ w2); auto.
    rewrite (unamb_OpRlt _ _ _ _ w1), (unamb_OpRlt _ _ _ _ w2); auto.
    rewrite (unamb_OpRmult _ _ _ _ w1), (unamb_OpRmult _ _ _ _ w2); auto.
    destruct u.
    rewrite (unamb_OpRrecip _ _ _ w1), (unamb_OpRrecip _ _ _ w2); auto.
    rewrite (unamb_OpZRcoerce _ _ _ w1), (unamb_OpZRcoerce _ _ _ w2); auto.
    rewrite (unamb_OpZRexp _ _ _ w1), (unamb_OpZRexp _ _ _ w2); auto.
    rewrite (unamb_Skip _ _ w1), (unamb_Skip _ _ w2); auto.
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    inversion w1.
    inversion w2.
    apply (has_type_ro_unambiguous' _ _ _ _ H H3).
    rewrite (unamb_Lim _ _ _ w1), (unamb_Lim _ _ _ w2); auto.
  +
    destruct e.
    induction w1.
    intro w2. 
    inversion w2.
    apply (has_type_ro_unambiguous _ _ _ _ h H3).
    induction H2.
    inversion h.

(* inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion w1. *)
(*     inversion w2. *)
(*     apply (has_type_ro_unambiguous _ _ _ _ H3 H8). *)
(*     inversion H3.  *)
(*     apply (has_type_ro_unambiguous' _ _ _ _ H11 (has_type_rw_Seq _ _ _ _ _ H9 H10)). *)
(*     inversion w2. *)
(*     inversion H10. *)

 
(* contradict magic. *)
(*     contradict magic. *)
(*     contradict magic. *)
(*     contradict magic. *)
(*     contradict magic. *)
(*     contradict magic. *)
(*     contradict magic. *)
(* Defined. *)
Admitted.


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


