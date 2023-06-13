Require Import Coq.Program.Equality.
Require Import Reals.
Require Import List.

Require Import Clerical.Preliminaries.Preliminaries.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.



Definition ro_asrt_imp {Γ} (P Q : sem_ctx Γ -> Prop) : Prop :=
  forall γ, P γ -> Q γ.

Definition asrt_imp {X : Type} (P Q : X -> Prop) : Prop :=
  forall γ, P γ -> Q γ.

Definition asrt_imp2 {X Y : Type} (P Q : X -> Y -> Prop) : Prop :=
  forall γ δ, P γ δ -> Q γ δ.

Definition asrt_or {X : Type} (P Q : X -> Prop) : X -> Prop :=
  fun γ =>  (P γ \/ Q γ).

Definition asrt_and {X : Type} (P Q : X -> Prop) : X -> Prop :=
  fun γ => (P γ /\ Q γ).

Definition asrt_and2 {X Y : Type} (P Q : X -> Y -> Prop) : X -> Y -> Prop :=
  fun γ δ  => (P γ δ /\ Q γ δ).

Infix "->>" := asrt_imp (at level 80).
Infix "->>>" := asrt_imp2 (at level 80).
Infix "/\\\" := asrt_and2 (at level 80).
Infix "/\\" := asrt_and (at level 80).
Infix "\//" := asrt_or (at level 80).


Section Rules.
  Reserved Notation " ' x : Γ |- w {{ ϕ }} e {{ y : τ | ψ }}ᵖ "
    (at level 50,  Γ, w, ϕ, e, y, τ, ψ at next level, x pattern).
  Reserved Notation " ' x : Γ |- w {{ ϕ }} e {{ y : τ | ψ }}ᵗ "
    (at level 50,  Γ, w, ϕ, e, y, τ, ψ at next level, x pattern).
  Reserved Notation " ' x : Γ ;;; ' y : Δ ||- w {{ ϕ }} e {{ z : τ | ψ }}ᵖ "
    (at level 50,  Γ,  Δ, w, ϕ, e, z, τ, ψ at next level, x pattern, y pattern).
  Reserved Notation " ' x : Γ ;;; ' y : Δ ||- w {{ ϕ }} e {{ z : τ | ψ }}ᵗ "
    (at level 50,  Γ,  Δ, w, ϕ, e, z, τ, ψ at next level, x pattern, y pattern).

(* This file defines the proof rules for specifications. *)



(* Fixpoint ro_access  Γ k τ (w: Γ |- Var k : τ) : sem_ctx Γ -> sem_datatype τ. *)
(* Proof. *)
(*   inversion w. *)
(*   inversion H. *)
(*   simpl in H7. *)
(*   exact (ro_access _ _ _ H7). *)
(*   intro. *)
(*   simpl in X. *)
(*   destruct X. *)
(*   exact s. *)
(*   intro. *)
(*   apply (ro_access _ _ _ H1). *)
(*   destruct X. *)
(*   exact s0. *)
(* Defined. *)

Definition rw_to_ro_pre {Γ Δ} (ϕ : sem_ctx Δ * sem_ctx Γ -> Prop) :=
                        fun δγ => ϕ (tedious_sem_app _ _ δγ).

Definition ro_to_rw_pre {Γ Δ} (ϕ : sem_ctx (Δ ++ Γ) -> Prop) : sem_ctx Δ * sem_ctx Γ -> Prop := fun δγ => ϕ (tedious_prod_sem Δ Γ δγ) .

Definition post {X Y : Type} := X -> Y -> Prop.

Definition rwpost {X Y Z : Type} := X -> Y -> Z -> Prop.
Definition rwpre {X Y : Type} := X -> Y -> Prop.


Inductive proves_ro_prt : forall Γ e τ (w : Γ |- e : τ), ro_prt w -> Type :=
(*  partial correctness triple for read only expressions *)
(** logical rules *)
| ro_imply_prt : forall Γ e τ (w w' : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    ' x : Γ |- w {{ P x }} e {{y : τ | Q x y}}ᵖ -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w' {{ P x }} e {{y : τ | Q x y}}ᵖ

| ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)    
    ' x : Γ |- w {{False}} e {{y : τ | Q y x }}ᵖ

| ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q1 Q2,
    

    ' x : Γ |- w {{ P x }} e {{y : τ | Q1 x y}}ᵖ -> 
    ' x : Γ |- w {{ P x }} e {{y : τ | Q2 x y}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ P x }} e {{y : τ | Q1 x y /\ Q2 x y}}ᵖ 

| ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P1 P2 Q,

    ' x : Γ |- w {{ P1 x }} e {{y : τ | Q x y}}ᵖ -> 
    ' x : Γ |- w {{ P2 x }} e {{y : τ | Q x y}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ P1 x /\ P2 x }} e {{y : τ | Q x y}}ᵖ  

(** variables and constants *)
| ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x (ro_access Γ k τ w x) }} VAR k {{y : τ | Q x y}}ᵖ

| ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x tt}} SKIP {{y : UNIT | Q x y}}ᵖ

                  
| ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x true }} TRUE {{y : BOOL | Q x y}}ᵖ

| ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x false }} FALSE {{y : BOOL | Q x y}}ᵖ

| ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x k }} INT k {{y : INTEGER | Q x y}}ᵖ

(** passage between read-only and read-write correctness *)
| ro_rw_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),

    ' γ : Γ ;;; ' _ : nil  ||- w {{ P γ tt }} c {{y : τ | Q γ tt y}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ tt }} c {{y : τ | Q γ tt y}}ᵖ


(* (** restricting auxiliary variables *) *)
(* | ro_proj_prt : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}} *)

                                 
(** coercion and exponentiation *)
| ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL),
    
    ' γ : Γ |- w {{ P γ }} e {{y : INTEGER | Q γ (IZR y)}}ᵖ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ }} RE e {{y : REAL | Q γ y}}ᵖ

| ro_exp_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL),
    
    ' γ : Γ |- w {{ P γ }} e {{y : INTEGER | Q γ (pow2 y)}}ᵖ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ }} EXP e {{y : REAL | Q γ y}}ᵖ    

(** integer arithmetic  *)
| ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zplus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :+: e2  {{y : INTEGER | ψ γ y}}ᵖ

| ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zmult y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :*: e2  {{y : INTEGER | ψ γ y}}ᵖ

| ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zminus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :-: e2  {{y : INTEGER | ψ γ y}}ᵖ

(** real arithmetic  *)
| ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rplus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;+; e2  {{y : REAL | ψ γ y}}ᵖ

| ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rmult y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;*; e2  {{y : REAL | ψ γ y}}ᵖ

| ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rminus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;-; e2  {{y : REAL | ψ γ y}}ᵖ

(** reciprocal *)
| ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) (ψ : post),

    ' γ : Γ |- w {{ ϕ γ }} e {{y : REAL | θ γ y}}ᵖ -> 
     (forall γ x, θ γ x /\ x <> 0%R -> ψ γ (/x)%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} ;/; e  {{y : REAL | ψ γ y}}ᵖ

(** integer comparison  *)
| ro_int_comp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ  γ (Z.eqb y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :=: e2  {{y : BOOL | ψ γ y}}ᵖ

| ro_int_comp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ  γ (Z.ltb y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :<: e2  {{y : BOOL | ψ γ y}}ᵖ

(** real comparison  *)
| ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵖ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵖ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rltb'' y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;<; e2  {{y : BOOL | ψ γ y}}ᵖ

(* Limit *)
| ro_lim_prt : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    ' (x, γ) : (INTEGER :: Γ) |- w {{ ϕ γ }} e {{y : REAL | θ (x, γ) y}}ᵗ -> 

         
         (forall γ : sem_ctx Γ, ϕ γ -> exists y, ψ γ y /\ forall x z, θ (x, γ) z -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} Lim e  {{y : REAL | ψ γ y}}ᵖ
                                                        
with proves_ro_tot : forall Γ e τ (w : Γ |- e : τ), ro_tot w -> Type :=
(** logical rules *)
(** logical rules *)
| ro_imply_tot : forall Γ e τ (w w' : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    ' x : Γ |- w {{ P x }} e {{y : τ | Q x y}}ᵗ -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w' {{ P x }} e {{y : τ | Q x y}}ᵗ

| ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)    
    ' x : Γ |- w {{False}} e {{y : τ | Q y x }}ᵗ

| ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q1 Q2,
    

    ' x : Γ |- w {{ P x }} e {{y : τ | Q1 x y}}ᵗ -> 
    ' x : Γ |- w {{ P x }} e {{y : τ | Q2 x y}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ P x }} e {{y : τ | Q1 x y /\ Q2 x y}}ᵗ 

| ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P1 P2 Q,

    ' x : Γ |- w {{ P1 x }} e {{y : τ | Q x y}}ᵗ -> 
    ' x : Γ |- w {{ P2 x }} e {{y : τ | Q x y}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ P1 x /\ P2 x }} e {{y : τ | Q x y}}ᵗ  

(** variables and constants *)
| ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x (ro_access Γ k τ w x) }} VAR k {{y : τ | Q x y}}ᵗ

| ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x tt}} SKIP {{y : UNIT | Q x y}}ᵗ

                  
| ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x true }} TRUE {{y : BOOL | Q x y}}ᵗ

| ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x false }} FALSE {{y : BOOL | Q x y}}ᵗ

| ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- w {{ Q x k }} INT k {{y : INTEGER | Q x y}}ᵗ

(** passage between read-only and read-write correctness *)
| ro_rw_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),

    ' γ : Γ ;;; ' _ : nil  ||- w {{ P γ tt }} c {{y : τ | Q γ tt y}}ᵗ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ tt }} c {{y : τ | Q γ tt y}}ᵗ


(* (** restricting auxiliary variables *) *)
(* | ro_proj_tot : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}} *)

                                 
(** coercion and exponentiation *)
| ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL),
    
    ' γ : Γ |- w {{ P γ }} e {{y : INTEGER | Q γ (IZR y)}}ᵗ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ }} RE e {{y : REAL | Q γ y}}ᵗ

| ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL),
    
    ' γ : Γ |- w {{ P γ }} e {{y : INTEGER | Q γ (pow2 y)}}ᵗ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ P γ }} EXP e {{y : REAL | Q γ y}}ᵗ    

(** integer arithmetic  *)
| ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zplus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :+: e2  {{y : INTEGER | ψ γ y}}ᵗ

| ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zmult y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :*: e2  {{y : INTEGER | ψ γ y}}ᵗ

| ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Zminus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :-: e2  {{y : INTEGER | ψ γ y}}ᵗ

(** real arithmetic  *)
| ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rplus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;+; e2  {{y : REAL | ψ γ y}}ᵗ

| ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rmult y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;*; e2  {{y : REAL | ψ γ y}}ᵗ

| ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ γ (Rminus y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;-; e2  {{y : REAL | ψ γ y}}ᵗ

(** reciprocal *)
| ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) (ψ : post),

    ' γ : Γ |- w {{ ϕ γ }} e {{y : REAL | θ γ y}}ᵗ -> 
     (forall γ x, θ γ x /\ x <> 0%R -> ψ γ (/x)%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} ;/; e  {{y : REAL | ψ γ y}}ᵗ

(** integer comparison  *)
| ro_int_comp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ  γ (Z.eqb y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :=: e2  {{y : BOOL | ψ γ y}}ᵗ

| ro_int_comp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : INTEGER | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : INTEGER | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> ψ  γ (Z.ltb y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 :<: e2  {{y : BOOL | ψ γ y}}ᵗ

(** real comparison  *)
| ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    ' γ : Γ |- w1 {{ ϕ γ }} e1 {{y : REAL | ψ1 γ y}}ᵗ -> 
    ' γ : Γ |- w2 {{ ϕ γ }} e2 {{y : REAL | ψ2 γ y}}ᵗ -> 
    (forall y1 y2 γ, ψ1 γ y1 -> ψ2 γ y2 -> (y1 <> y2)%R /\ ψ γ (Rltb'' y1 y2)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} e1 ;<; e2  {{y : BOOL | ψ γ y}}ᵗ

(* Limit *)
| ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    ' (x, γ) : (INTEGER :: Γ) |- w {{ ϕ γ }} e {{y : REAL | θ (x, γ) y}}ᵗ -> 

         
         (forall γ : sem_ctx Γ, ϕ γ -> exists y, ψ γ y /\ forall x z, θ (x, γ) z -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- w' {{ ϕ γ }} Lim e  {{y : REAL | ψ γ y}}ᵗ
                                                        

                                                        
                                                        
with proves_rw_prt : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_prt w -> Type :=
(** logical rules *)
| rw_imply_prt : forall Γ Δ e τ (w w' : Γ ;;; Δ ||- e : τ) (ϕ ϕ': rwpre) (ψ ψ' : rwpost),
    
    (forall γ δ, ϕ' γ δ -> ϕ γ δ) -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵖ -> 
    (forall γ δ y, ψ γ δ y -> ψ' γ δ y) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ ϕ' γ δ }} e {{y : τ | ψ' γ δ y }}ᵖ 

| rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{False}} e {{y : τ | ψ γ δ y }}ᵖ  
    
| rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ',
    
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ' γ δ y }}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | (ψ γ δ y) /\ (ψ' γ δ y) }}ᵖ

| rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ' γ δ }} e {{y : τ | ψ γ δ y }}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{ (ϕ γ δ) \/ (ϕ' γ δ) }} e {{y : τ | ψ γ δ y }}ᵖ 

(** passage between read-only and read-write correctness *)
| rw_ro_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    'γ : (Δ ++ Γ) |- w {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ (δ ; γ)}} e {{y : τ | ψ (δ ; γ) y}}ᵖ

(* (** restricting auxiliary variables *) *)
(* | rw_proj_prt : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||- {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}} *)

(** operational proof rules  *)                            
| rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    'γ : Γ ;;; 'δ : Δ ||- w1 {{ϕ γ δ}} c1 {{y : UNIT | θ γ δ y}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- w2 {{θ γ δ tt}} c2 {{y : τ | ψ γ δ y}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} c1 ;; c2 {{y : τ | ψ γ δ y}}ᵖ

| rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    'x : (Δ ++ Γ) |- w1 {{ϕ (snd_app x) (fst_app x)}} e {{y : σ | θ (snd_app x) (fst_app x) y}}ᵖ -> 
    'γ : Γ ;;; '(x, δ) : (σ :: Δ) ||- w2 {{θ γ δ x}} c {{y : τ | ψ γ δ y}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} NEWVAR e IN c {{y : τ | ψ γ δ y}}ᵖ

| rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : rwpost) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    'x : (Δ ++ Γ) |- w {{ϕ (snd_app x) (fst_app x)}} e {{y : τ | θ x y}}ᵖ -> 
    (forall x γ δ, θ (δ; γ) x -> ψ γ (update' w w' δ x) tt) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} LET k := e {{y : UNIT | ψ γ δ y}}ᵖ

| rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    'x : (Δ ++ Γ) |- w {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- w1 {{θ (δ ; γ) true}} c1 {{y : τ | ψ γ δ y}}ᵖ ->
    'γ : Γ ;;; 'δ : Δ ||- w2 {{θ (δ ; γ) false}} c2 {{y : τ | ψ γ δ y}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} Cond e c1 c2 {{y : τ | ψ γ δ y}}ᵖ

| rw_case_list_prt : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ =>  sem_ctx (Δ ++ Γ) -> bool -> Prop) l)
                            ϕ ψ,
    ForallT2 _ _ 
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : sem_ctx (Δ ++ Γ) -> bool ->  Prop)  =>
         
       ('x : (Δ ++ Γ) |- (fst wty_l) {{ϕ (snd_app x) (fst_app x)}} fst ec {{y : BOOL | θ x y}}ᵖ)
       * ('γ : Γ ;;; 'δ : Δ ||- (snd wty_l) {{θ (δ ; γ) true}} snd ec {{y : τ | ψ γ δ y}}ᵗ)
    )%type l wty_l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- wty {{ϕ γ δ}} CaseList l {{y : τ | ψ γ δ y}}ᵖ


        
| rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ,

    'x : (Δ ++ Γ) |- wty_e {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- wty_c {{θ (δ ; γ) true}} c {{y : UNIT | ϕ γ δ}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- wty {{ϕ γ δ}} While e c {{y : UNIT | (ϕ γ δ) /\ θ (δ; γ) false}}ᵖ
       

                                  
with proves_rw_tot : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_tot w -> Type :=
(** logical rules *)
| rw_imply_tot : forall Γ Δ e τ (w w' : Γ ;;; Δ ||- e : τ) (ϕ ϕ': rwpre) (ψ ψ' : rwpost),
    
    (forall γ δ, ϕ' γ δ -> ϕ γ δ) -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵗ -> 
    (forall γ δ y, ψ γ δ y -> ψ' γ δ y) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ ϕ' γ δ }} e {{y : τ | ψ' γ δ y }}ᵗ 

| rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{False}} e {{y : τ | ψ γ δ y }}ᵗ  
    
| rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ',
    
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ' γ δ y }}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | (ψ γ δ y) /\ (ψ' γ δ y) }}ᵗ

| rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ γ δ }} e {{y : τ | ψ γ δ y }}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- w {{ ϕ' γ δ }} e {{y : τ | ψ γ δ y }}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w {{ (ϕ γ δ) \/ (ϕ' γ δ) }} e {{y : τ | ψ γ δ y }}ᵗ 

(** passage between read-only and read-write correctness *)
| rw_ro_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    'γ : (Δ ++ Γ) |- w {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ (δ ; γ)}} e {{y : τ | ψ (δ ; γ) y}}ᵗ

(* (** restricting auxiliary variables *) *)
(* | rw_proj_tot : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||- {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}} *)

(** operational proof rules  *)                            
| rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    'γ : Γ ;;; 'δ : Δ ||- w1 {{ϕ γ δ}} c1 {{y : UNIT | θ γ δ y}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- w2 {{θ γ δ tt}} c2 {{y : τ | ψ γ δ y}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} c1 ;; c2 {{y : τ | ψ γ δ y}}ᵗ

| rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    'x : (Δ ++ Γ) |- w1 {{ϕ (snd_app x) (fst_app x)}} e {{y : σ | θ (snd_app x) (fst_app x) y}}ᵗ -> 
    'γ : Γ ;;; '(x, δ) : (σ :: Δ) ||- w2 {{θ γ δ x}} c {{y : τ | ψ γ δ y}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} NEWVAR e IN c {{y : τ | ψ γ δ y}}ᵗ

| rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : rwpost) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    'x : (Δ ++ Γ) |- w {{ϕ (snd_app x) (fst_app x)}} e {{y : τ | θ x y}}ᵗ -> 
    (forall x γ δ, θ (δ; γ) x -> ψ γ (update' w w' δ x) tt) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} LET k := e {{y : UNIT | ψ γ δ y}}ᵗ

| rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    'x : (Δ ++ Γ) |- w {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- w1 {{θ (δ ; γ) true}} c1 {{y : τ | ψ γ δ y}}ᵗ ->
    'γ : Γ ;;; 'δ : Δ ||- w2 {{θ (δ ; γ) false}} c2 {{y : τ | ψ γ δ y}}ᵗ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- w' {{ϕ γ δ}} Cond e c1 c2 {{y : τ | ψ γ δ y}}ᵗ

| rw_case_list_tot : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ =>  sem_ctx (Δ ++ Γ) -> bool -> Prop) l)
                            (ϕi : ForallT (fun _ => sem_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,
    ForallT3 _ _ _
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : sem_ctx (Δ ++ Γ) -> bool -> Prop) (ϕi : sem_ctx (Δ ++ Γ) -> Prop)  =>
         
    ('x : (Δ ++ Γ) |- fst (wty_l) {{ϕ (snd_app x) (fst_app x)}} fst ec {{y : BOOL | θ x y}}ᵖ) *
    ('γ : Γ ;;; 'δ : Δ ||- snd (wty_l) {{θ (δ; γ) true}} snd ec {{y : τ | ψ γ δ y}}ᵗ) * 
    ('x : (Δ ++ Γ) |- fst (wty_l) {{ϕi x}} fst ec {{b : BOOL | b = true}}ᵗ)) %type l wty_l θ ϕi ->
    (forall x, (ϕ (snd_app x) (fst_app x)) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- wty {{ϕ γ δ}} CaseList l {{y : τ | ψ γ δ y}}ᵗ

 | rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL)
                                               (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty_c' : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ,
     'x : (Δ ++ Γ) |- wty_e {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- wty_c' {{θ (δ ; γ) true}} c {{y : UNIT | ϕ γ δ}}ᵗ ->
    'x : (Γ ++ Δ) ;;; 'δ : Δ ||- wty_c {{θ (δ ; (fst_app x)) true}} c {{y : UNIT | ψ x δ}}ᵗ ->
             (forall δ γ, ϕ γ δ  ->  
                           ~exists f : nat -> sem_ctx Δ,
                               f O = δ /\ forall n, ψ (γ ; f n) (f (S n))) ->
                    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- wty {{ϕ γ δ}} While e c {{y : UNIT | (ϕ γ δ) /\ θ (δ; γ) false}}ᵗ

                                                                                                       
where
" ' x : Γ |- w {{ P }} e {{ y : τ | Q }}ᵖ " := (proves_ro_prt Γ e τ w (mk_ro_prt w (fun x => P) (fun x y => Q))) and
" ' x : Γ |- w {{ P }} e {{ y : τ | Q }}ᵗ " := (proves_ro_tot Γ e τ w (mk_ro_tot w (fun x => P) (fun x y => Q))) and
" ' x : Γ ;;; ' y : Δ ||- w {{ P }} e {{ z : τ | Q }}ᵖ " := (proves_rw_prt Γ Δ e τ w (mk_rw_prt w (fun x y => P) (fun x y z => Q))) and
" ' x : Γ ;;; ' y : Δ ||- w {{ P }} e {{ z : τ | Q }}ᵗ " := (proves_rw_tot Γ Δ e τ w (mk_rw_tot w (fun x y => P) (fun x y z => Q))).


End Rules.

Notation " ' x : Γ |- w {{ ϕ }} e {{ y : τ | ψ }}ᵖ "
  := (proves_ro_prt Γ e τ w (mk_ro_prt w (fun x => ϕ) (fun x y => ψ)))
       (at level 50,  Γ, w, ϕ, e, y, τ, ψ at next level, x pattern).
Notation " ' x : Γ |- w {{ ϕ }} e {{ y : τ | ψ }}ᵗ "
  := (proves_ro_tot Γ e τ w (mk_ro_tot w (fun x => ϕ) (fun x y => ψ)))
       (at level 50,  Γ, w, ϕ, e, y, τ, ψ at next level, x pattern).
Notation " ' x : Γ ;;; ' y : Δ ||- w {{ P }} e {{ z : τ | Q }}ᵖ "
  := (proves_rw_prt Γ Δ e τ w (mk_rw_prt w (fun x y => P) (fun x y z => Q)))
       (at level 50,  Γ,  Δ, w, P, e, z, τ, Q at next level, x pattern, y pattern).
Notation " ' x : Γ ;;; ' y : Δ ||- w {{ P }} e {{ z : τ | Q }}ᵗ "
  := (proves_rw_tot Γ Δ e τ w (mk_rw_tot w (fun x y => P) (fun x y z => Q)))
       (at level 50,  Γ,  Δ, w, P, e, z, τ, Q at next level, x pattern, y pattern).

