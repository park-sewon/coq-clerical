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


Definition asrt_imp {X : Type} (P Q : X -> Prop) : Prop :=
  forall γ, P γ -> Q γ.

Definition asrt_or {X : Type} (P Q : X -> Prop) : X -> Prop :=
  fun γ =>  (P γ \/ Q γ).

Definition asrt_and {X : Type} (P Q : X -> Prop) : X -> Prop :=
  fun γ => (P γ /\ Q γ).

Infix "->>" := asrt_imp (at level 80).
Infix "/\\" := asrt_and (at level 80).
Infix "\//" := asrt_or (at level 80).

(* notations to be used as placeholders to teach Coq type inference engine
   when using function types whose input is pattern  *)
Notation patf := (fun '(_, _) => _) (only parsing). 
Notation pattf := (fun '(_, (_, _)) => _) (only parsing).

Section Rules.
  Reserved Notation " ' x : Γ |- {{ ϕ }} e {{ y : τ | ψ }}ᵖ "
    (at level 50,  Γ, ϕ, e, y, τ, ψ at next level, x pattern).
  Reserved Notation " ' x : Γ |- {{ ϕ }} e {{ y : τ | ψ }}ᵗ "
    (at level 50,  Γ, ϕ, e, y, τ, ψ at next level, x pattern).
  Reserved Notation " ' x : Γ ;;; ' y : Δ ||- {{ ϕ }} e {{ z : τ | ψ }}ᵖ "
    (at level 50,  Γ,  Δ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern).
  Reserved Notation " ' x : Γ ;;; ' y : Δ ||- {{ ϕ }} e {{ z : τ | ψ }}ᵗ "
    (at level 50,  Γ,  Δ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern).

(* This file defines the proof rules for specifications. *)
  Definition pred {X : Type} := X -> Prop.
  

  
Inductive proves_ro_prt : forall Γ e τ , ro_prt Γ e τ -> Type :=
(*  partial correctness triple for read only expressions *)
(** logical rules *)
| ro_imply_prt : forall Γ e τ P Q P' Q',

    ' x : Γ |- {{ P x }} e {{y : τ | Q (x, y)}}ᵖ -> 
    P' ->> P -> 
    Q ->> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P' x }} e {{y : τ | Q' (x, y)}}ᵖ

| ro_exfalso_prt : forall Γ e τ Q,
    Γ |- e : τ ->
    (*——————————-——————————-——————————-——————————-——————————-*)    
    ' x : Γ |- {{False}} e {{y : τ | Q (x, y) }}ᵖ

| ro_conj_prt : forall Γ e τ P Q1 Q2,
    

    ' x : Γ |- {{ P x }} e {{y : τ | Q1 (x, y)}}ᵖ -> 
    ' x : Γ |- {{ P x }} e {{y : τ | Q2 (x, y)}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P x }} e {{y : τ | Q1 (x, y) /\ Q2 (x, y)}}ᵖ 

| ro_disj_prt : forall Γ e τ P1 P2 Q,

    ' x : Γ |- {{ P1 x }} e {{y : τ | Q (x, y)}}ᵖ -> 
    ' x : Γ |- {{ P2 x }} e {{y : τ | Q (x, y)}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P1 x \/ P2 x }} e {{y : τ | Q (x, y)}}ᵖ  

(** variables and constants *)
| ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, (var_access Γ k τ w x)) }} VAR k {{y : τ | Q (x, y)}}ᵖ

| ro_skip_prt : forall Γ Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, tt) }} SKIP {{y : UNIT | Q (x, y)}}ᵖ

                  
| ro_true_prt : forall Γ Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, true) }} TRUE {{y : BOOL | Q (x, y)}}ᵖ

| ro_false_prt : forall Γ Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, false) }} FALSE {{y : BOOL | Q (x, y)}}ᵖ

| ro_int_prt : forall Γ k Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, k) }} INT k {{y : INTEGER | Q (x, y)}}ᵖ

(** passage between read-only and read-write correctness *)
| ro_rw_prt : forall Γ c τ P Q,

    ' γ : Γ ;;; ' _ : nil  ||- {{ P (γ, tt) }} c {{y : τ | Q (γ, (tt, y))}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P (γ, tt) }} c {{y : τ | Q (γ, (tt, y))}}ᵖ
   
(** coercion and exponentiation *)
| ro_coerce_prt : forall Γ e P Q,
    
    ' γ : Γ |- {{ P γ }} e {{y : INTEGER | Q (γ, (IZR y))}}ᵖ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P γ }} RE e {{y : REAL | Q (γ, y)}}ᵖ

| ro_exp_prt : forall Γ e P Q,
    
    ' γ : Γ |- {{ P γ }} e {{y : INTEGER | Q (γ, (pow2 y))}}ᵖ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P γ }} EXP e {{y : REAL | Q (γ, y)}}ᵖ    

(** integer arithmetic  *)
| ro_int_op_plus_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ :pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zplus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :+: e2  {{y : INTEGER | ψ (γ, y)}}ᵖ

| ro_int_op_mult_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zmult y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :*: e2  {{y : INTEGER | ψ (γ, y)}}ᵖ

| ro_int_op_minus_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zminus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :-: e2  {{y : INTEGER | ψ (γ, y)}}ᵖ

(** real arithmetic  *)
| ro_real_op_plus_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rplus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;+; e2  {{y : REAL | ψ (γ, y)}}ᵖ

| ro_real_op_mult_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rmult y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;*; e2  {{y : REAL | ψ (γ, y)}}ᵖ

| ro_real_op_minus_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rminus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;-; e2  {{y : REAL | ψ (γ, y)}}ᵖ

(** reciprocal *)
| ro_recip_prt : forall Γ e ϕ θ (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e {{y : REAL | θ (γ, y)}}ᵖ -> 
     (forall γ x, θ (γ, x) /\ x <> 0%R -> ψ (γ, (/x))%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} ;/; e  {{y : REAL | ψ (γ, y)}}ᵖ

(** integer comparison  *)
| ro_int_comp_eq_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ  (γ, (Z.eqb y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :=: e2  {{y : BOOL | ψ (γ, y)}}ᵖ

| ro_int_comp_lt_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ  (γ, (Z.ltb y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :<: e2  {{y : BOOL | ψ (γ, y)}}ᵖ

(** real comparison  *)
| ro_real_comp_lt_prt : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> y1 <> y2 -> ψ (γ, (Rltb'' y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;<; e2  {{y : BOOL | ψ (γ, y)}}ᵖ

(* Limit *)
| ro_lim_prt : forall Γ e ϕ θ ψ,

    ' (γ, x) : (Γ ::: INTEGER) |- {{ ϕ γ }} e {{y : REAL | θ ((γ, x), y)}}ᵗ -> 
    (forall γ : sem_ctx Γ, ϕ γ -> exists y, ψ (γ, y) /\ forall x z, θ ((γ, x), z) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} Lim e  {{y : REAL | ψ (γ, y)}}ᵖ



                         
with proves_ro_tot : forall Γ e τ , ro_tot Γ e τ -> Type :=
(** logical rules *)
| ro_imply_tot : forall Γ e τ P Q P' Q',

    ' x : Γ |- {{ P x }} e {{y : τ | Q (x, y)}}ᵗ -> 
    P' ->> P -> 
    Q ->> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P' x }} e {{y : τ | Q' (x, y)}}ᵗ

| ro_exfalso_tot : forall Γ e τ Q,
    Γ |- e : τ ->
    (*——————————-——————————-——————————-——————————-——————————-*)    
    ' x : Γ |- {{False}} e {{y : τ | Q (x, y) }}ᵗ

| ro_conj_tot : forall Γ e τ  P Q1 Q2,
    

    ' x : Γ |- {{ P x }} e {{y : τ | Q1 (x, y)}}ᵗ -> 
    ' x : Γ |- {{ P x }} e {{y : τ | Q2 (x, y)}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P x }} e {{y : τ | Q1 (x, y) /\ Q2 (x, y)}}ᵗ 

| ro_disj_tot : forall Γ e τ  P1 P2 Q,

    ' x : Γ |- {{ P1 x }} e {{y : τ | Q (x, y)}}ᵗ -> 
    ' x : Γ |- {{ P2 x }} e {{y : τ | Q (x, y)}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ P1 x \/ P2 x }} e {{y : τ | Q (x, y)}}ᵗ  

(** variables and constants *)
| ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, (var_access Γ k τ w x)) }} VAR k {{y : τ | Q (x, y)}}ᵗ

| ro_skip_tot : forall Γ Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, tt) }} SKIP {{y : UNIT | Q (x, y)}}ᵗ

                  
| ro_true_tot : forall Γ Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, true) }} TRUE {{y : BOOL | Q (x, y)}}ᵗ

| ro_false_tot : forall Γ Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, false) }} FALSE {{y : BOOL | Q (x, y)}}ᵗ

| ro_int_tot : forall Γ k Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    ' x : Γ |- {{ Q (x, k) }} INT k {{y : INTEGER | Q (x, y)}}ᵗ

(** passage between read-only and read-write correctness *)
| ro_rw_tot : forall Γ c τ P Q,

    ' γ : Γ ;;; ' _ : nil  ||- {{ P (γ, tt) }} c {{y : τ | Q (γ, (tt, y))}}ᵗ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P (γ, tt) }} c {{y : τ | Q (γ, (tt, y))}}ᵗ

                                 
(** coercion and exponentiation *)
| ro_coerce_tot : forall Γ e P Q,
    
    ' γ : Γ |- {{ P γ }} e {{y : INTEGER | Q (γ, (IZR y))}}ᵗ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P γ }} RE e {{y : REAL | Q (γ, y)}}ᵗ

| ro_exp_tot : forall Γ e P Q,
    
    ' γ : Γ |- {{ P γ }} e {{y : INTEGER | Q (γ, (pow2 y))}}ᵗ ->
   (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ P γ }} EXP e {{y : REAL | Q (γ, y)}}ᵗ    

(** integer arithmetic  *)
| ro_int_op_plus_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ :pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zplus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :+: e2  {{y : INTEGER | ψ (γ, y)}}ᵗ

| ro_int_op_mult_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zmult y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :*: e2  {{y : INTEGER | ψ (γ, y)}}ᵗ

| ro_int_op_minus_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Zminus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :-: e2  {{y : INTEGER | ψ (γ, y)}}ᵗ

(** real arithmetic  *)
| ro_real_op_plus_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rplus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;+; e2  {{y : REAL | ψ (γ, y)}}ᵗ

| ro_real_op_mult_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rmult y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;*; e2  {{y : REAL | ψ (γ, y)}}ᵗ

| ro_real_op_minus_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ (γ, (Rminus y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;-; e2  {{y : REAL | ψ (γ, y)}}ᵗ

(** reciprocal *)
| ro_recip_tot : forall Γ e  ϕ θ (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e {{y : REAL | θ (γ, y)}}ᵗ -> 
     (forall γ x, θ (γ, x) -> x <> 0%R /\ ψ (γ, (/x))%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} ;/; e  {{y : REAL | ψ (γ, y)}}ᵗ

(** integer comparison  *)
| ro_int_comp_eq_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ  (γ, (Z.eqb y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :=: e2  {{y : BOOL | ψ (γ, y)}}ᵗ

| ro_int_comp_lt_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),

    ' γ : Γ |- {{ ϕ γ }} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> ψ  (γ, (Z.ltb y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 :<: e2  {{y : BOOL | ψ (γ, y)}}ᵗ

(** real comparison  *)
| ro_real_comp_lt_tot : forall Γ e1 e2 ϕ ψ1 ψ2 (ψ : pred),
    
    ' γ : Γ |- {{ ϕ γ }} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ -> 
    ' γ : Γ |- {{ ϕ γ }} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ -> 
    (forall γ y1 y2, ψ1 (γ, y1) -> ψ2 (γ, y2) -> y1 <> y2 /\ ψ (γ, (Rltb'' y1 y2))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} e1 ;<; e2  {{y : BOOL | ψ (γ, y)}}ᵗ

(* Limit *)
| ro_lim_tot : forall Γ e ϕ θ ψ,

    ' (γ, x) : (Γ ::: INTEGER) |- {{ ϕ γ }} e {{y : REAL | θ ((γ, x), y)}}ᵗ -> 
    (forall γ : sem_ctx Γ, ϕ γ -> exists y, ψ (γ, y) /\ forall x z, θ ((γ, x), z) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    ' γ : Γ |- {{ ϕ γ }} Lim e  {{y : REAL | ψ (γ, y)}}ᵗ

                         
with proves_rw_prt : forall Γ Δ c τ, rw_prt Γ Δ c τ -> Type :=
(** logical rules *)
| rw_imply_prt : forall Γ Δ e τ (ϕ ϕ': pred) (ψ ψ' : pred),
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ -> 
    (ϕ' ->> ϕ) -> 
    (ψ ->> ψ') -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ' (γ, δ) }} e {{y : τ | ψ' (γ, (δ, y)) }}ᵖ
                      
                      
| rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{False}} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ  
    
| rw_conj_prt : forall Γ Δ e τ ϕ ψ ψ',
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ' (γ, (δ, y)) }}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | (ψ (γ, (δ, y))) /\ (ψ' (γ, (δ, y))) }}ᵖ

| rw_disj_prt : forall Γ Δ e τ ϕ ϕ' ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ' (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) \/ ϕ' (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ 

(** passage between read-only and read-write correctness *)
| rw_ro_prt : forall Γ Δ e τ ϕ ψ,
    
    'γ : (Γ +++ Δ) |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ; δ)}} e {{y : τ | ψ ((γ; δ), y)}}ᵖ

(** operational proof rules  *)                            
| rw_sequence_prt : forall Γ Δ c1 c2 τ ϕ θ ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} c1 {{y : UNIT | θ (γ, (δ, y))}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ (γ, (δ, tt))}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} c1 ;; c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ

| rw_new_var_prt : forall Γ Δ e c τ σ  ϕ ψ θ,

    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵖ -> 
    'γ : Γ ;;; '(δ, x) : (Δ ::: σ) ||- {{θ ((γ; δ), x)}} c {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} NEWVAR e IN c {{y : τ | ψ (γ, (δ, y))}}ᵖ

| rw_assign_prt : forall Γ Δ e k τ ϕ θ (ψ : pred)
    (a : assignable Δ τ k),
    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵖ -> 
    (forall γ δ x, θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} LET k := e {{y : UNIT | ψ (γ, (δ, y))}}ᵖ

| rw_cond_prt : forall Γ Δ e c1 c2 τ ϕ θ ψ,

    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵖ ->
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} Cond e c1 c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ

| rw_case_list_prt : forall Γ Δ l τ
                            (θ : ForallT (fun _ =>  sem_ctx (Γ +++ Δ) * bool -> Prop) l)
                            ϕ ψ,  (1 <= length l)%nat ->
    ForallT1 _ 
    (fun ec  (θ : sem_ctx (Γ +++ Δ) * bool ->  Prop)  =>
         
       ('x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ)
       * ('γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ)
    )%type l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵖ

        
| rw_while_prt : forall Γ Δ e c ϕ θ,

    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵖ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} c {{y : UNIT | ϕ (γ, δ)}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} While e c {{y : UNIT | ϕ (γ, δ) /\ θ ((γ; δ), false)}}ᵖ

                    
                      
with proves_rw_tot : forall Γ Δ c τ, rw_tot Γ Δ c τ -> Type :=  
(** logical rules *)
| rw_imply_tot : forall Γ Δ e τ (ϕ ϕ': pred) (ψ ψ' : pred),
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ -> 
    (ϕ' ->> ϕ) -> 
    (ψ ->> ψ') -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ' (γ, δ) }} e {{y : τ | ψ' (γ, (δ, y)) }}ᵗ 


                      
| rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{False}} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ  
    
| rw_conj_tot : forall Γ Δ e τ ϕ ψ ψ',
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ' (γ, (δ, y)) }}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | (ψ (γ, (δ, y))) /\ (ψ' (γ, (δ, y))) }}ᵗ

| rw_disj_tot : forall Γ Δ e τ ϕ ϕ' ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ' (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ ϕ (γ, δ) \/ ϕ' (γ, δ) }} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ 

(** passage between read-only and read-write correctness *)
| rw_ro_tot : forall Γ Δ e τ ϕ ψ,
    
    'γ : (Γ +++ Δ) |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ; δ)}} e {{y : τ | ψ ((γ; δ), y)}}ᵗ

(** operational proof rules  *)                            
| rw_sequence_tot : forall Γ Δ c1 c2 τ ϕ θ ψ,
    
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} c1 {{y : UNIT | θ (γ, (δ, y))}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ (γ, (δ, tt))}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} c1 ;; c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ

| rw_new_var_tot : forall Γ Δ e c τ σ ϕ ψ θ,
    
    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵗ -> 
    'γ : Γ ;;; '(δ, x) : (Δ ::: σ) ||- {{θ ((γ; δ), x)}} c {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} NEWVAR e IN c {{y : τ | ψ (γ, (δ, y))}}ᵗ

| rw_assign_tot : forall Γ Δ e k τ ϕ θ (ψ : pred) (a : assignable Δ τ k),
    
    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵗ -> 
    (forall γ δ x, θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} LET k := e {{y : UNIT | ψ (γ, (δ, y))}}ᵗ

| rw_cond_tot : forall Γ Δ e c1 c2 τ ϕ θ ψ,

    'x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} Cond e c1 c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ

| rw_case_list_tot : forall Γ Δ l τ
                            
                            (θ : ForallT (fun _ =>  sem_ctx (Δ ++ Γ) * bool -> Prop) l)
                            (ϕi : ForallT (fun _ => sem_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,  (1 <= length l)%nat -> 
    ForallT2 _ _
    (fun ec (θ : sem_ctx (Δ ++ Γ) * bool -> Prop) (ϕi : sem_ctx (Δ ++ Γ) -> Prop)  =>
         
    ('x : (Δ ++ Γ) |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ) *
    ('γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵗ) * 
    ('x : (Δ ++ Γ) |- {{ϕi x}} fst ec {{b : BOOL | b = true}}ᵗ)) %type l θ ϕi ->
    (forall x, (ϕ (fst_app x, snd_app x)) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵗ

 | rw_while_tot : forall Γ Δ e c ϕ θ ψ,
     'x : (Δ ++ Γ) |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ -> 
    'γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} c {{y : UNIT | ϕ (γ, δ)}}ᵗ ->
    'x : (Δ +++ Γ) ;;; 'δ : Δ ||- {{θ ((snd_app x; δ), true) /\ δ = fst_app x}} c {{y : UNIT | ψ (x, δ)}}ᵗ ->
             (forall γ δ, ϕ (γ, δ)  ->  
                           ~exists f : nat -> sem_ctx Δ,
                               f O = δ /\ forall n, ψ ((f n ; γ), f (S n))) ->
                    (*——————————-——————————-——————————-——————————-——————————-*)
    'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} While e c {{y : UNIT | ϕ (γ, δ) /\ θ ((γ; δ), false)}}ᵗ

                                                                                                       
where
" ' x : Γ |- {{ P }} e {{ y : τ | Q }}ᵖ " := (proves_ro_prt Γ e τ (@mk_ro_prt Γ e τ (fun x => P) (fun '(x, y) => Q))) and
" ' x : Γ |- {{ P }} e {{ y : τ | Q }}ᵗ " := (proves_ro_tot Γ e τ (@mk_ro_tot Γ e τ (fun x => P) (fun '(x, y) => Q))) and
" ' x : Γ ;;; ' y : Δ ||- {{ P }} e {{ z : τ | Q }}ᵖ " := (proves_rw_prt Γ Δ e τ (@mk_rw_prt Γ Δ e τ (fun '(x, y) => P) (fun '(x, (y, z)) => Q))) and
" ' x : Γ ;;; ' y : Δ ||- {{ P }} e {{ z : τ | Q }}ᵗ " := (proves_rw_tot Γ Δ e τ (@mk_rw_tot Γ Δ e τ (fun '(x, y) => P) (fun '(x, (y, z)) => Q))).


End Rules.

Notation " [ x : Γ ] |- {{ ϕ }} e {{ y : τ | ψ }}ᵖ "
  := (proves_ro_prt Γ e τ (@mk_ro_prt Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)))
       (at level 50,  Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.
Notation " [ x : Γ ] |- {{ ϕ }} e {{ y : τ | ψ }}ᵗ "
  := (proves_ro_tot Γ e τ (@mk_ro_tot Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)))
       (at level 50,  Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.
Notation " [ x ':' Γ  ';;;'  y ':' Δ ] '||-' '{{' ϕ '}}' e '{{' z ':' τ '|' ψ '}}ᵖ' "
  := (proves_rw_prt Γ Δ e τ (@mk_rw_prt Γ Δ e τ (fun '(x, y) => ϕ) (fun '(x, (y, z)) => ψ)))
       (at level 50,  Γ,  Δ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern) : clerical_scope.
Notation " [ x ':' Γ  ';;;'   y ':' Δ ]  '||-' '{{' ϕ '}}' e '{{' z ':' τ '|' ψ '}}ᵗ' "
  := (proves_rw_tot Γ Δ e τ (@mk_rw_tot Γ Δ e τ (fun '(x, y) => ϕ) (fun '(x, (y, z)) => ψ)))
       (at level 50,  Γ,  Δ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern) : clerical_scope.
