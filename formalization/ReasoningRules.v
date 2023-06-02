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




Definition ro_asrt_imp {Γ} (P Q : sem_ro_ctx Γ -> Prop) : Prop :=
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
Reserved Notation " w |- {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w |- {{ P }} e {{ y | Q }} " (at level 50, P, e,y, Q at next level).
Reserved Notation " w |- [{ P }] e [{ Q }] " (at level 50, P, e, Q at next level).
Reserved Notation " w ||- {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w ||- [{ P }] e [{ Q }] " (at level 50, P, e, Q at next level).
Reserved Notation " w |- [{ P }] e [{ y | Q }] " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||- {{ P }} e {{ y | Q }} " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||- [{ P }] e [{ y | Q }] " (at level 50, P, e, y, Q at next level).

(* This file defines the proof rules for specifications. *)



(* Fixpoint ro_access  Γ k τ (w: Γ |- Var k : τ) : sem_ro_ctx Γ -> sem_datatype τ. *)
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

Definition rw_to_ro_pre {Γ Δ} (ϕ : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop) :=
                        fun δγ => ϕ (tedious_sem_app _ _ δγ).

Definition ro_to_rw_pre {Γ Δ} (ϕ : sem_ro_ctx (Δ ++ Γ) -> Prop) : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop := fun δγ => ϕ (tedious_prod_sem Δ Γ δγ) .

Definition post {X Y : Type} := X -> Y -> Prop.

Inductive proves_ro_prt : forall Γ e τ (w : Γ |- e : τ), ro_prt w -> Type :=
(*  partial correctness triple for read only expressions *)
(** logical rules *)
| ro_imply_prt : forall Γ e τ (w w' : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    w |- {{ P }} e {{ Q }} -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ P'}}  e {{ Q' }}

| ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)    
    w |- {{ (fun _ => False) }} e {{ Q }}

| ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q Q',
    

    w |- {{P}} e {{Q}} -> 
    w |- {{P}} e {{Q'}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{P}} e {{Q /\\\ Q'}}

| ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P P' Q,

    w |- {{P}} e {{Q}} -> 
    w |- {{P'}} e {{Q}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{P \// P'}} e {{Q}}

(** variables and constants *)
| ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{fun γ => Q (ro_access Γ k τ w γ) γ}} VAR k {{Q}}

| ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{Q tt}} SKIP {{Q}}

| ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{Q true}} TRUE {{Q}}

| ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{Q false}} FALSE {{Q}}

| ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- {{Q k}} INT k {{Q}}

(** passage between read-only and read-write correctness *)
| ro_rw_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    
    w ||- {{P}} c {{Q}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{fun γ => P (tt, γ)}} c {{fun v w => Q v (tt, w)}}

(* (** restricting auxiliary variables *) *)
(* | ro_proj_prt : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}} *)

                                 
(** coercion and exponentiation *)
| ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL),
    
    w |- {{P}} e {{y | Q (IZR y)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{P}} RE e {{Q}}

| ro_exp_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL),
    
    w |- {{P}} e {{y | Q (powerRZ 2 y)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{P}} EXP e {{Q}}

(** integer arithmetic  *)
| ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),
    
    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)->
    (*——————————-——————————-——————————-——————————-——————————-*)
     w' |- {{ϕ}} e1 :+: e2 {{ψ}}

| ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 :*: e2) {{ψ}}

| ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 :-: e2) {{ψ}}

(** real arithmetic  *)
| ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 ;+; e2) {{ψ}}

| ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 ;*; e2) {{ψ}}

| ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 ;-; e2) {{ψ}}

(** reciprocal *)
| ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ,

    w |- {{ϕ}} e {{θ}} -> 
    (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} UniOp OpRrecip e {{ψ}}

(** integer comparison  *)
| ro_int_comp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    w1 |- {{ϕ}} e1 {{ψ1}} -> 
    w2 |- {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} (e1 :=: e2) {{ψ}}

| ro_int_comp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    w1 |- {{P}} e1 {{ψ1}} -> 
    w2 |- {{P}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{P}} (e1 :<: e2) {{ψ}}

(** real comparison  *)
| ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) P ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    w1 |- {{P}} e1 {{ψ1}} -> 
    w2 |- {{P}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{P}} (e1 ;<; e2) {{ψ}}

(* Limit *)
| ro_lim_prt : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    w |- [{fun γ' : sem_ro_ctx _ => ϕ (snd γ')}] e [{θ}] ->
    (forall γ : sem_ro_ctx Γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- {{ϕ}} Lim e {{ψ}}
                                                        
with proves_ro_tot : forall Γ e τ (w : Γ |- e : τ), ro_tot w -> Type :=
(** logical rules *)
| ro_imply_tot : forall Γ e τ (w w' : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    w |- [{ P }] e [{ Q }] -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ P'}]  e [{ Q' }]

| ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)    
    w |- [{ (fun _ => False) }] e [{ Q }]

| ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q Q',
    

    w |- [{P}] e [{Q}] -> 
    w |- [{P}] e [{Q'}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{P}] e [{Q /\\\ Q'}]

| ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P P' Q,

    w |- [{P}] e [{Q}] -> 
    w |- [{P'}] e [{Q}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{P \// P'}] e [{Q}]

(** variables and constants *)
| ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{fun γ => Q (ro_access Γ k τ w γ) γ}] VAR k [{Q}]

| ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{Q tt}] SKIP [{Q}]

| ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{Q true}] TRUE [{Q}]

| ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{Q false}] FALSE [{Q}]

| ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |- [{Q k}] INT k [{Q}]

(** passage between read-only and read-write correctness *)
| ro_rw_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    
    w ||- [{P}] c [{Q}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{fun γ => P (tt, γ)}] c [{fun v w => Q v (tt, w)}]

(* (** restricting auxiliary variables *) *)
(* | ro_proj_tot : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |- [{ϕ}] e [{ψ}] -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |- [{fun γ => exists γ', ϕ (γ ; γ')}] e [{y | fun γ => exists γ', ψ y (γ ; γ')}] *)

                                 
(** coercion and exponentiation *)
| ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- RE e : REAL),
    
    w |- [{ϕ}] e [{y | ψ (IZR y)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] RE e [{ψ}]

| ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- EXP e : REAL),
    
    w |- [{ϕ}] e [{y | ψ (powerRZ 2 y)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] EXP e [{ψ}]

(** integer arithmetic  *)
| ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)->
    (*——————————-——————————-——————————-——————————-——————————-*)
     w' |- [{ϕ}] e1 :+: e2 [{ψ}]

| ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 :*: e2) [{ψ}]

| ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 :-: e2) [{ψ}]

(** real arithmetic  *)
| ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 ;+; e2) [{ψ}]

| ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 ;*; e2) [{ψ}]

| ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 ;-; e2) [{ψ}]
  

(** reciprocal *)
| ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ,

    w |- [{ϕ}] e [{θ}] -> 
    (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] ;/; e [{ψ}]

(** integer comparison  *)
| ro_int_comp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 :=: e2) [{ψ}]

| ro_int_comp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    w1 |- [{P}] e1 [{ψ1}] -> 
    w2 |- [{P}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{P}] (e1 :<: e2) [{ψ}]

(** real comparison  *)
| ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2  (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    w1 |- [{ϕ}] e1 [{ψ1}] -> 
    w2 |- [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] (e1 ;<; e2) [{ψ}]


(* Limit *)
| ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    w |- [{fun γ' : sem_ro_ctx _ => ϕ (snd γ')}] e [{θ}] ->
    (forall γ :sem_ro_ctx Γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |- [{ϕ}] Lim e [{ψ}]
                                                        

                                                        
                                                        
with proves_rw_prt : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_prt w -> Type :=
(** logical rules *)
| rw_imply_prt : forall Γ Δ e τ (w w' : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ',
    
    ϕ' ->> ϕ -> 
    w ||- {{ ϕ }} e {{ ψ }} -> 
    ψ ->>> ψ' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{ ϕ'}}  e {{ ψ' }}

| rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- {{ (fun _ => False) }} e {{ ψ }}

| rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ',
    
    w ||- {{ϕ}} e {{ψ}} -> 
    w ||- {{ϕ}} e {{ψ'}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- {{ϕ}} e {{ψ /\\\ ψ'}}

| rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ,
    
    w ||- {{ϕ}} e {{ψ}} -> 
    w ||- {{ϕ'}} e {{ψ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- {{ϕ \// ϕ'}} e {{ψ}}

(** passage between read-only and read-write correctness *)
| rw_ro_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    w |- {{ϕ}} e {{ψ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}}

(* (** restricting auxiliary variables *) *)
(* | rw_proj_prt : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||- {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||- {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}} *)

(** operational proof rules  *)                            
| rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    w1 ||- {{ϕ}} c1 {{θ}} -> 
    w2 ||- {{θ tt}} c2 {{ψ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{ϕ}} c1 ;; c2 {{ψ}}

| rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    w1 |- {{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}} e {{θ}} -> 
    w2 ||- {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{ϕ}} NEWVAR e IN c {{ψ}}

| rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    w |- {{fun δγ => ϕ (tedious_sem_app _ _ δγ)}} e {{θ}} -> 
    (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{ϕ}} LET k := e {{ψ}}

| rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    w |- {{rw_to_ro_pre ϕ}} e {{θ}} ->
    w1 ||- {{ro_to_rw_pre (θ true)}} c1 {{ψ}} ->
    w2 ||- {{ro_to_rw_pre (θ false)}} c2 {{ψ}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}

| rw_case_prt : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ,

    wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} -> 
    wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} -> 
    wty_c1 ||- {{ro_to_rw_pre (θ1 true)}} c1 {{ψ}} -> 
    wty_c2 ||- {{ro_to_rw_pre (θ2 true)}} c2 {{ψ}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- {{ϕ}} Case e1 c1 e2 c2 {{ψ}}

| rw_case_list_prt : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,
    ForallT2 _ _ 
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)  =>
         
    (fst (wty_l) |- {{rw_to_ro_pre ϕ}} fst ec {{θ}}) *
    (snd (wty_l) ||- {{ro_to_rw_pre (θ true)}} snd ec {{ψ}}))%type l wty_l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- {{ϕ}} CaseList l {{ψ}}


        
| rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ,

    wty_e |- {{rw_to_ro_pre ϕ}} e {{θ}} -> 
    wty_c ||- {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}}
                        

                                  
with proves_rw_tot : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_tot w -> Type :=
(** logical rules *)
| rw_imply_tot : forall Γ Δ e τ (w w' : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ',
    
    ϕ' ->> ϕ -> 
    w ||- [{ ϕ }] e [{ ψ }] -> 
    ψ ->>> ψ' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{ ϕ'}]  e [{ ψ' }]

| rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- [{ (fun _ => False) }] e [{ ψ }]

| rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ',
    
    w ||- [{ϕ}] e [{ψ}] -> 
    w ||- [{ϕ}] e [{ψ'}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- [{ϕ}] e [{ψ /\\\ ψ'}]

| rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ,
    
    w ||- [{ϕ}] e [{ψ}] -> 
    w ||- [{ϕ'}] e [{ψ}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||- [{ϕ \// ϕ'}] e [{ψ}]

(** passage between read-only and read-write correctness *)
| rw_ro_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    w |- [{ϕ}] e [{ψ}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}] e [{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}]

(* (** restricting auxiliary variables *) *)
(* | rw_proj_tot : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||- [{ϕ}] e [{ψ}] -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||- [{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}] e [{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}] *)
      
(** operational proof rules  *)                            
| rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : UNIT) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    w1 ||- [{ϕ}] c1 [{θ}] -> 
    w2 ||- [{θ tt}] c2 [{ψ}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{ϕ}] c1 ;; c2 [{ψ}]

| rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    w1 |- [{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}] e [{θ}] -> 
    w2 ||- [{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}] c [{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{ϕ}] NEWVAR e IN c [{ψ}]

| rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    w |- [{fun δγ => ϕ (tedious_sem_app _ _ δγ)}] e [{θ}] -> 
    (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{ϕ}] LET k := e [{ψ}]

| rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    w |- [{rw_to_ro_pre ϕ}] e [{θ}] ->
    w1 ||- [{ro_to_rw_pre (θ true)}] c1 [{ψ}] ->
    w2 ||- [{ro_to_rw_pre (θ false)}] c2 [{ψ}] ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||- [{ϕ}] Cond e c1 c2 [{ψ}]


| rw_case_tot : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ ϕ1 ϕ2,
    
    wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} -> 
    wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} -> 
    wty_c1 ||- [{ro_to_rw_pre (θ1 true)}] c1 [{ψ}] -> 
    wty_c2 ||- [{ro_to_rw_pre (θ2 true)}] c2 [{ψ}] -> 
    wty_e1 |- [{ϕ1}] e1 [{b |fun _ => b = true}] -> 
    wty_e2 |- [{ϕ2}] e2 [{b | fun _ => b = true}] -> 
    (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x)) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- [{ϕ}] Case e1 c1 e2 c2 [{ψ}]


| rw_case_list_tot : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            (ϕi : ForallT (fun _ => sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,
    ForallT3 _ _ _
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) (ϕi : sem_ro_ctx (Δ ++ Γ) -> Prop)  =>
         
    (fst (wty_l) |- {{rw_to_ro_pre ϕ}} fst ec {{θ}}) *
    (snd (wty_l) ||- [{ro_to_rw_pre (θ true)}] snd ec [{ψ}]) * 
    (fst (wty_l) |- [{ϕi}] fst ec [{b | fun _ => b = true}])) %type l wty_l θ ϕi ->
    (forall x, (rw_to_ro_pre ϕ x) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- [{ϕ}] CaseList l [{ψ}]

        
| rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ,
    
    wty_e |- [{rw_to_ro_pre ϕ}] e [{θ}] ->
    wty_c ||- [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ δγδ' }] ->
             (forall δ γ, ϕ (δ, γ) ->  
                           ~exists f : nat -> sem_ro_ctx Δ,
                               f O = δ /\ forall n, ψ (f (S n), (γ ; f n))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||- [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}]

                                                                                                       
where
" w |- {{ P }} e {{ Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P Q)) and  " w |- {{ P }} e {{ y | Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P (fun y => Q))) and " w |- [{ P }] e [{ y | Q }] " := (proves_ro_tot _ e _ w (mk_ro_tot w P (fun y => Q))) and " w ||- {{ P }} e {{ y | Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P (fun y => Q))) and " w ||- [{ P }] e [{ y | Q }] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P (fun y => Q))) and " w |- [{ P }] e [{ Q }] " := (proves_ro_tot _ e _ w (mk_ro_tot w P Q)) and " w ||- {{ P }} e {{ Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P Q)) and " w ||- [{ P }] e [{ Q }] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P Q)).


End Rules.

Notation " w |- {{ P }} e {{ Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P Q))  (at level 50, P, e, Q at next level) : clerical_scope.

Notation " w |- [{ P }] e [{ Q }] " := (proves_ro_tot _ e _ w (mk_ro_tot w P Q)) (at level 50, P, e, Q at next level) : clerical_scope.

Notation " w ||- {{ P }} e {{ Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P Q)) (at level 50, P, e, Q at next level) : clerical_scope.

Notation " w ||- [{ P }] e [{ Q }] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P Q)) (at level 50, P, e, Q at next level) : clerical_scope.

Notation  " w |- {{ P }} e {{ y | Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P (fun y => Q))) (at level 50, P, e, Q, y at next level) : clerical_scope.

Notation " w |- [{ P }] e [{ y | Q }] " := (proves_ro_tot _ e _ w (mk_ro_tot w P (fun y => Q))) (at level 50, P, e, Q, y  at next level) : clerical_scope.

Notation " w ||- {{ P }} e {{ y | Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P (fun y => Q))) (at level 50, P, e, Q, y  at next level) : clerical_scope.

Notation " w ||- [{ P }] e [{ y | Q }] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P (fun y => Q))) (at level 50, P, e, Q, y at next level) : clerical_scope.
