Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.


Arguments existT {_} {_}.

Reserved Notation " w |~ {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w |~ {{ P }} e {{ y | Q }} " (at level 50, P, e,y, Q at next level).
Reserved Notation " w |~ [{ P }] e [{ Q }] " (at level 50, P, e, Q at next level).
Reserved Notation " w ||~ {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w ||~ [{ P }] e [{ Q }] " (at level 50, P, e, Q at next level).
Reserved Notation " w |~ [{ P }] e [{ y | Q }] " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||~ {{ P }} e {{ y | Q }} " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||~ [{ P }] e [{ y | Q }] " (at level 50, P, e, y, Q at next level).

Fixpoint ForallT_by_restriction {X} (P : X -> Type) (l : list X) : (forall x, P x) -> ForallT P l.
Proof.
  intro f.
  destruct l.
  apply ForallT_nil.
  apply ForallT_cons.
  exact (f x).
  exact (ForallT_by_restriction X P l f).
Defined.


Fixpoint ForallT_map {A} {l : list A} {P Q : A -> Type} (f : forall a, P a -> Q a) (g : ForallT P l) : ForallT Q l.
Proof.
  dependent destruction g.
  apply ForallT_nil.
  exact (ForallT_cons Q x l (f x p) (ForallT_map A l P Q f g)).
Defined.

Lemma ForallT_map_ForalT_nil {A} {l : list A} {P Q : A -> Type} {f : forall a, P a -> Q a}
  : ForallT_map f (ForallT_nil P) = ForallT_nil Q.
Proof.
  simpl.
  reflexivity.
Defined.
    
Section RestrictedRules.

Inductive r_proves_ro_prt : forall Γ e τ (w : Γ |- e : τ), ro_prt w -> Type :=
(*  partial correctness triple for read only expressions *)
(** logical rules *)
| r_ro_imply_prt : forall Γ e τ (w : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    w |~ {{ P }} e {{ Q }} -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{ P'}}  e {{ Q' }}

(** variables and constants *)
| r_ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{fun γ => Q (ro_access Γ k τ w γ) γ}} VAR k {{Q}}

| r_ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{Q tt}} SKIP {{Q}}

| r_ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{Q true}} TRUE {{Q}}

| r_ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{Q false}} FALSE {{Q}}

| r_ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ {{Q k}} INT k {{Q}}

(** passage between read-only and read-write correctness *)
| r_rw_ro_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    
    w ||~ {{P}} c {{Q}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{fun γ => P (tt, γ)}} c {{fun v w => Q v (tt, w)}}

(* (** restricting auxiliary variables *) *)
(* | r_ro_proj_prt : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |~ {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |~ {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}} *)

                                 
(** coercion and exponentiation *)
| r_ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL),
    
    w |~ {{P}} e {{y | Q (IZR y)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{P}} RE e {{Q}}

| r_ro_exp_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL),
    
    w |~ {{P}} e {{y | Q (powerRZ 2 y)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{P}} EXP e {{Q}}

(** integer arithmetic  *)
| r_ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),
    
    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)->
    (*——————————-——————————-——————————-——————————-——————————-*)
     w' |~ {{ϕ}} e1 :+: e2 {{ψ}}

| r_ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 :*: e2) {{ψ}}

| r_ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 :-: e2) {{ψ}}

(** real arithmetic  *)
| r_ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 ;+; e2) {{ψ}}

| r_ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 ;*; e2) {{ψ}}

| r_ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 ;-; e2) {{ψ}}

(** reciprocal *)
| r_ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ,

    w |~ {{ϕ}} e {{θ}} -> 
    (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} UniOp OpRrecip e {{ψ}}

(** integer comparison  *)
| r_ro_int_comp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    w1 |~ {{ϕ}} e1 {{ψ1}} -> 
    w2 |~ {{ϕ}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} (e1 :=: e2) {{ψ}}

| r_ro_int_comp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    w1 |~ {{P}} e1 {{ψ1}} -> 
    w2 |~ {{P}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{P}} (e1 :<: e2) {{ψ}}

(** real comparison  *)
| r_ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) P ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    w1 |~ {{P}} e1 {{ψ1}} -> 
    w2 |~ {{P}} e2 {{ψ2}} -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{P}} (e1 ;<; e2) {{ψ}}

(* Limit *)
| r_ro_lim_prt : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    w |~ [{fun γ' => ϕ (snd γ')}] e [{θ}] ->
    (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ {{ϕ}} Lim e {{ψ}}
                                                        
with r_proves_ro_tot : forall Γ e τ (w : Γ |- e : τ), ro_tot w -> Type :=
(** logical rules *)
| r_ro_imply_tot : forall Γ e τ (w : Γ |- e : τ) P Q P' Q',

    P' ->> P -> 
    w |~ [{ P }] e [{ Q }] -> 
    Q ->>> Q' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{ P'}]  e [{ Q' }]

(** variables and constants *)
| r_ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{fun γ => Q (ro_access Γ k τ w γ) γ}] VAR k [{Q}]

| r_ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q,
    
    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{Q tt}] SKIP [{Q}]

| r_ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{Q true}] TRUE [{Q}]

| r_ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{Q false}] FALSE [{Q}]

| r_ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q,

    (*——————————-——————————-——————————-——————————-——————————-*)
    w |~ [{Q k}] INT k [{Q}]

(** passage between read-only and read-write correctness *)
| r_rw_ro_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    
    w ||~ [{P}] c [{Q}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{fun γ => P (tt, γ)}] c [{fun v w => Q v (tt, w)}]

(* (** restricting auxiliary variables *) *)
(* | r_ro_proj_tot : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
(*     w' |~ [{ϕ}] e [{ψ}] -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w |~ [{fun γ => exists γ', ϕ (γ ; γ')}] e [{y | fun γ => exists γ', ψ y (γ ; γ')}] *)

                                 
(** coercion and exponentiation *)
| r_ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- RE e : REAL),
    
    w |~ [{ϕ}] e [{y | ψ (IZR y)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] RE e [{ψ}]

| r_ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- EXP e : REAL),
    
    w |~ [{ϕ}] e [{y | ψ (powerRZ 2 y)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] EXP e [{ψ}]

(** integer arithmetic  *)
| r_ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)->
    (*——————————-——————————-——————————-——————————-——————————-*)
     w' |~ [{ϕ}] e1 :+: e2 [{ψ}]

| r_ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 :*: e2) [{ψ}]

| r_ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 :-: e2) [{ψ}]

(** real arithmetic  *)
| r_ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 ;+; e2) [{ψ}]

| r_ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 ;*; e2) [{ψ}]

| r_ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post),

    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 ;-; e2) [{ψ}]
  

(** reciprocal *)
| r_ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ,

    w |~ [{ϕ}] e [{θ}] -> 
    (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] ;/; e [{ψ}]

(** integer comparison  *)
| r_ro_int_comp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post),

    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 :=: e2) [{ψ}]

| r_ro_int_comp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post),

    w1 |~ [{P}] e1 [{ψ1}] -> 
    w2 |~ [{P}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{P}] (e1 :<: e2) [{ψ}]

(** real comparison  *)
| r_ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2  (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post),
    
    w1 |~ [{ϕ}] e1 [{ψ1}] -> 
    w2 |~ [{ϕ}] e2 [{ψ2}] -> 
    (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] (e1 ;<; e2) [{ψ}]


(* Limit *)
| r_ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ,

    w |~ [{fun γ' => ϕ (snd γ')}] e [{θ}] ->
    (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' |~ [{ϕ}] Lim e [{ψ}]
                                                        

                                                        
                                                        
with r_proves_rw_prt : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_prt w -> Type :=
(** logical rules *)
| r_rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ',
    
    ϕ' ->> ϕ -> 
    w ||~ {{ ϕ }} e {{ ψ }} -> 
    ψ ->>> ψ' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||~ {{ ϕ'}}  e {{ ψ' }}

(** passage between read-only and read-write correctness *)
| r_ro_rw_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    w |~ {{ϕ}} e {{ψ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ {{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}}

(* (** restricting auxiliary variables *) *)
(* | r_rw_proj_prt : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||~ {{ϕ}} e {{ψ}} -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||~ {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}} *)

(** operational proof rules  *)                            
| r_rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    w1 ||~ {{ϕ}} c1 {{θ}} -> 
    w2 ||~ {{θ tt}} c2 {{ψ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ {{ϕ}} c1 ;; c2 {{ψ}}

| r_rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    w1 |~ {{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}} e {{θ}} -> 
    w2 ||~ {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ {{ϕ}} NEWVAR e IN c {{ψ}}

| r_rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    w |~ {{fun δγ => ϕ (tedious_sem_app _ _ δγ)}} e {{θ}} -> 
    (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ {{ϕ}} LET k := e {{ψ}}

| r_rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    w |~ {{rw_to_ro_pre ϕ}} e {{θ}} ->
    w1 ||~ {{ro_to_rw_pre (θ true)}} c1 {{ψ}} ->
    w2 ||~ {{ro_to_rw_pre (θ false)}} c2 {{ψ}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ {{ϕ}} Cond e c1 c2 {{ψ}}

| r_rw_case_prt : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ,

    wty_e1 |~ {{rw_to_ro_pre ϕ}} e1 {{θ1}} -> 
    wty_e2 |~ {{rw_to_ro_pre ϕ}} e2 {{θ2}} -> 
    wty_c1 ||~ {{ro_to_rw_pre (θ1 true)}} c1 {{ψ}} -> 
    wty_c2 ||~ {{ro_to_rw_pre (θ2 true)}} c2 {{ψ}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ {{ϕ}} Case e1 c1 e2 c2 {{ψ}}

| r_rw_case_list_prt : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,
    ForallT2 _ _ 
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)  =>
         
    (fst (wty_l) |~ {{rw_to_ro_pre ϕ}} fst ec {{θ}}) *
    (snd (wty_l) ||~ {{ro_to_rw_pre (θ true)}} snd ec {{ψ}}))%type l wty_l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ {{ϕ}} CaseList l {{ψ}}


        
| r_rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ,

    wty_e |~ {{rw_to_ro_pre ϕ}} e {{θ}} -> 
    wty_c ||~ {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}}
                        

                                  
with r_proves_rw_tot : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_tot w -> Type :=
(** logical rules *)
| r_rw_imply_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ',
    
    ϕ' ->> ϕ -> 
    w ||~ [{ ϕ }] e [{ ψ }] -> 
    ψ ->>> ψ' -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w ||~ [{ ϕ'}]  e [{ ψ' }]

(** passage between read-only and read-write correctness *)
| r_ro_rw_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ),
    
    w |~ [{ϕ}] e [{ψ}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ [{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}] e [{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}]

(* (** restricting auxiliary variables *) *)
(* | r_rw_proj_tot : forall Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ,  *)
(*     w' ||~ [{ϕ}] e [{ψ}] -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     w ||~ [{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}] e [{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}] *)
      
(** operational proof rules  *)                            
| r_rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : UNIT) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ),
    
    w1 ||~ [{ϕ}] c1 [{θ}] -> 
    w2 ||~ [{θ tt}] c2 [{ψ}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ [{ϕ}] c1 ;; c2 [{ψ}]

| r_rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ),

    w1 |~ [{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}] e [{θ}] -> 
    w2 ||~ [{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}] c [{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}] -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ [{ϕ}] NEWVAR e IN c [{ψ}]

| r_rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT),

    w |~ [{fun δγ => ϕ (tedious_sem_app _ _ δγ)}] e [{θ}] -> 
    (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ [{ϕ}] LET k := e [{ψ}]

| r_rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,

    w |~ [{rw_to_ro_pre ϕ}] e [{θ}] ->
    w1 ||~ [{ro_to_rw_pre (θ true)}] c1 [{ψ}] ->
    w2 ||~ [{ro_to_rw_pre (θ false)}] c2 [{ψ}] ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    w' ||~ [{ϕ}] Cond e c1 c2 [{ψ}]


| r_rw_case_tot : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ ϕ1 ϕ2,
    
    wty_e1 |~ {{rw_to_ro_pre ϕ}} e1 {{θ1}} -> 
    wty_e2 |~ {{rw_to_ro_pre ϕ}} e2 {{θ2}} -> 
    wty_c1 ||~ [{ro_to_rw_pre (θ1 true)}] c1 [{ψ}] -> 
    wty_c2 ||~ [{ro_to_rw_pre (θ2 true)}] c2 [{ψ}] -> 
    wty_e1 |~ [{ϕ1}] e1 [{b |fun _ => b = true}] -> 
    wty_e2 |~ [{ϕ2}] e2 [{b | fun _ => b = true}] -> 
    (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x)) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ [{ϕ}] Case e1 c1 e2 c2 [{ψ}]


| r_rw_case_list_tot : forall Γ Δ l τ
                            (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l)
                            (wty : Γ ;;; Δ ||- CaseList l : τ)
                            (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            (ϕi : ForallT (fun _ => sem_ro_ctx (Δ ++ Γ) -> Prop) l)
                            ϕ ψ,
    ForallT3 _ _ _
    (fun ec (wty_l : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))  (θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) (ϕi : sem_ro_ctx (Δ ++ Γ) -> Prop)  =>
         
    (fst (wty_l) |~ {{rw_to_ro_pre ϕ}} fst ec {{θ}}) *
    (snd (wty_l) ||~ [{ro_to_rw_pre (θ true)}] snd ec [{ψ}]) * 
    (fst (wty_l) |~ [{ϕi}] fst ec [{b | fun _ => b = true}])) %type l wty_l θ ϕi ->
    (forall x, (rw_to_ro_pre ϕ x) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ [{ϕ}] CaseList l [{ψ}]

        
| r_rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ,
    
    wty_e |~ [{rw_to_ro_pre ϕ}] e [{θ}] ->
    wty_c ||~ [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ δγδ' }] ->
             (forall δ γ, ϕ (δ, γ) ->  
                           ~exists f : nat -> sem_ro_ctx Δ,
                               f O = δ /\ forall n, ψ (f (S n), (γ ; f n))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||~ [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}]

                                                                                                       
where
" w |~ {{ P }} e {{ Q }} " := (r_proves_ro_prt _ e _ w (mk_ro_prt w P Q)) and  " w |~ {{ P }} e {{ y | Q }} " := (r_proves_ro_prt _ e _ w (mk_ro_prt w P (fun y => Q))) and " w |~ [{ P }] e [{ y | Q }] " := (r_proves_ro_tot _ e _ w (mk_ro_tot w P (fun y => Q))) and " w ||~ {{ P }} e {{ y | Q }} " := (r_proves_rw_prt _ _ e _ w (mk_rw_prt w P (fun y => Q))) and " w ||~ [{ P }] e [{ y | Q }] " := (r_proves_rw_tot _ _ e _ w (mk_rw_tot w P (fun y => Q))) and " w |~ [{ P }] e [{ Q }] " := (r_proves_ro_tot _ e _ w (mk_ro_tot w P Q)) and " w ||~ {{ P }} e {{ Q }} " := (r_proves_rw_prt _ _ e _ w (mk_rw_prt w P Q)) and " w ||~ [{ P }] e [{ Q }] " := (r_proves_rw_tot _ _ e _ w (mk_rw_tot w P Q)).


Axiom magic : forall A, A.

Fixpoint has_type_ro_add_auxiliary Γ e τ (w : Γ |- e : τ) Γ' : (Γ ++ Γ') |- e : τ
with has_type_rw_add_auxiliary Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) Γ' : (Γ ++ Γ') ;;; Δ ||- e : τ.
Admitted.



Fixpoint r_admissible_ro_exfalso_prt Γ e τ (w : Γ |- e : τ) ψ {struct e}: w |~ {{fun _ => False}} e {{ψ}}
with r_admissible_ro_exfalso_tot Γ e τ (w : Γ |- e : τ) ψ {struct e}: w |~ [{fun _ => False}] e [{ψ}]
with r_admissible_rw_exfalso_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ {struct e}: w ||~ {{fun _ => False}} e {{ψ}}
with r_admissible_rw_exfalso_tot Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ {struct e}: w ||~ [{fun _ => False}] e [{ψ}].
Proof.
  +
    dependent destruction e.

    pose proof (r_ro_var_prt _ _ _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    destruct b.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.


    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_prt _ _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct b;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H as w1, H0 as w2;
      pose proof (r_admissible_ro_exfalso_prt _ _ _ w1 (fun _ _ => False));
      pose proof (r_admissible_ro_exfalso_prt _ _ _ w2 (fun _ _ => False)).
    apply (r_ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct u;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H.
    
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun _ _ => False)).
    apply (r_ro_recip_prt _ _ _ _ _ _ _ X).
    intros h1 h2 h3.
    destruct h3.
    contradict H0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun x => ψ (IZR x))).
    apply (r_ro_coerce_prt _ _ _ _ _ _ X).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun x => ψ ((powerRZ 2 x)))).
    apply (r_ro_exp_prt _ _ _ _ _ _ X).

    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

              
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r1, r2.
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ (Typing.has_type_rw_Seq _ _ _ _ _ r1 r2 ) X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X1).
    simpl in X2.
    exact X2.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r3.
    apply r_has_type_ro_has_type_ro in r1. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r3 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0.
    pose proof (r_rw_cond_prt _ _ _ _ _ _ _ _ _ (has_type_rw_Cond _ _ _ _ _ _ r1 r2 r3) (fun _ => False) _ _ X X0 X1).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    exact X3.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r4.
    apply r_has_type_ro_has_type_ro in r1, r3. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r3 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r4 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0, X2.
    pose proof (r_rw_case_prt _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Case _ _ _ _ _ _ _ r1 r2 r3 r4) (fun _ => False) _ _ _ X X1 X0 X2).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X3).
    simpl in X4.
    exact X4.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_prt).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    pose proof (r_rw_case_list_prt Γ nil _ _ f1
                                   (has_type_rw_CaseList _ _ _ _ l1 f1) f0 (fun _ => False) (fun y x => ψ y (snd x))
               ).
    assert (ForallT2 (fun ec : exp * exp => (((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l : ((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))
            (θ : bool -> sem_ro_ctx (nil ++ Γ) -> Prop) =>
          ((fst wty_l |~ {{rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False)}} fst ec {{y | θ y}}) *
           (snd wty_l ||~ {{ro_to_rw_pre (θ true)}} snd ec {{y
                                                            | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ y (snd x))}}))%type) l f1 f0).
    clear X0 l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT2_nil.
    dependent destruction f.
    apply ForallT2_cons.
    apply IHl.

    split.
    simpl.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_prt.

    pose proof (X0 X1).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    exact X3.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_while_prt.
    pose proof (r_rw_while_prt _ _ _ _ _ _ (has_type_rw_While _ _ _ _ r r0) _ _ X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H.
    contradict H; auto.

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_new_var_prt.
    pose proof (r_rw_new_var_prt _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ (has_type_rw_Newvar _ _ _ _ _ _ r r0) X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H; auto.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    contradict (assignable_absurd _ _ a).

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in H. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    pose proof r_ro_lim_prt.
    pose proof (r_ro_lim_prt _ _ _ (fun _ => False) (fun _ _ => False) w ψ X).
    assert ( (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) Γ,
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) Γ => False) γ ->
        exists y : R,
          ψ y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x)))).
    intros.
    contradict H0.
    pose proof (X1 H0).
    exact X2.

  +
    dependent destruction e.

    pose proof (r_ro_var_tot _ _ _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    destruct b.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.


    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_tot _ _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct b;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H as w1, H0 as w2;
      pose proof (r_admissible_ro_exfalso_tot _ _ _ w1 (fun _ _ => False));
      pose proof (r_admissible_ro_exfalso_tot _ _ _ w2 (fun _ _ => False)).
    apply (r_ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct u;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H.
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    apply (r_ro_recip_tot _ _ _ _ _ _ _ X).
    intros h1 h2 h3.
    destruct h3.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun x => ψ (IZR x))).
    apply (r_ro_coerce_tot _ _ _ _ _ _ X).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun x => ψ ((powerRZ 2 x)))).
    apply (r_ro_exp_tot _ _ _ _ _ _ X).

    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

              
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r1, r2.
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ (Typing.has_type_rw_Seq _ _ _ _ _ r1 r2 ) X X0).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X1).
    simpl in X2.
    exact X2.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r3.
    apply r_has_type_ro_has_type_ro in r1. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r3 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0.
    pose proof (r_rw_cond_tot _ _ _ _ _ _ _ _ _ (has_type_rw_Cond _ _ _ _ _ _ r1 r2 r3) (fun _ => False) _ _ X X0 X1).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X2).
    simpl in X3.
    exact X3.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r4.
    apply r_has_type_ro_has_type_ro in r1, r3. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r3 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r4 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun b _ => b = true)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r3 (fun b _ => b = true)).
    simpl in X, X1, X0, X2.
    pose proof (r_rw_case_tot _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Case _ _ _ _ _ _ _ r1 r2 r3 r4) (fun _ => False) _ _ _ (fun _ => False) (fun _ => False) X X1 X0 X2 X3 X4).
    assert ((forall x : sem_ro_ctx (nil ++ Γ),
        rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) x ->
        (fun _ : sem_ro_ctx (nil ++ Γ) => False) x \/ (fun _ : sem_ro_ctx (nil ++ Γ) => False) x)).
    intros.
    destruct H.
    
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w (X5 H)).
    simpl in X6.
    exact X6.

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose (ForallT_by_restriction (fun _ : exp * exp =>  sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ => False)).
    pose proof (r_rw_case_list_tot).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    pose proof (r_rw_case_list_tot Γ nil _ _ f2
                                   (has_type_rw_CaseList _ _ _ _ l1 f2) f0 f1 (fun _ => False) (fun y x => ψ y (snd x))
               ).
    assert (ForallT3 (fun ec : exp * exp => (((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l : ((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))
            (θ : bool -> sem_ro_ctx (nil ++ Γ) -> Prop) (ϕi : sem_ro_ctx (nil ++ Γ) -> Prop) =>
          ((fst wty_l |~ {{rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False)}} fst ec {{y | θ y}}) *
           (snd wty_l ||~ [{ro_to_rw_pre (θ true)}] snd ec [{y
            | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ y (snd x))}]) *
           (fst wty_l |~ [{ϕi}] fst ec [{b | (fun _ : sem_ro_ctx (nil ++ Γ) => b = true)}]))%type) l f2 f0 f1). 
    
    clear X0 l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT3_nil.
    dependent destruction f.
    apply ForallT3_cons.
    apply IHl.
    split.
    split.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_tot.
    apply r_admissible_ro_exfalso_tot.
    pose proof (X0 X1).
    assert ((forall x : sem_ro_ctx (nil ++ Γ),
        rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) x ->
        ForallT_disj (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop)
                     (fun (a : exp * exp) (ϕi : (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop) a) => ϕi x) l f1)).
    intros.
    destruct H.
    pose proof (X2 H).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X3).
    exact X4.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot (Γ ++ nil) nil e2 _ (has_type_rw_add_auxiliary _ _ _ _ r0 nil) (fun _ _ => False)).
    assert (has_type_rw_add_auxiliary Γ nil e2 UNIT r0 nil
  ||~ [{(fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) =>
         ro_to_rw_pre (fun _ : sem_ro_ctx (nil ++ Γ) => False) (fst δγδ', fst_app (snd δγδ')) /\
         fst δγδ' = snd_app (snd δγδ'))}] e2 [{_
                                              | (fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => (fun _ => False) (fst δγδ', fst_app (snd δγδ')) /\ False)}]).

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros x y.

    destruct y.
    destruct H.
    intros h1 h2 h3; auto.
    
    pose proof (r_rw_while_tot _ _ _ _ _ _ (has_type_rw_While _ _ _ _ r r0) _ _ (fun _ => False) X X1).
    assert ((forall (δ : sem_ro_ctx nil) (γ : sem_ro_ctx Γ),
        (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) (δ, γ) ->
        ~
        (exists f : nat -> sem_ro_ctx nil,
           f 0%nat = δ /\
             (forall n : nat, (fun _ : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => False) (f (S n), (γ; f n)))))).
    intros.
    destruct H.
    pose proof (X2 H).    
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X3).
    simpl in X3.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X4);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H0.
    contradict H0; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_new_var_tot.
    pose proof (r_rw_new_var_tot _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ (has_type_rw_Newvar _ _ _ _ _ _ r r0) X X0).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H; auto.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    contradict (assignable_absurd _ _ a).

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in H. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    pose proof r_ro_lim_tot.
    pose proof (r_ro_lim_tot _ _ _ (fun _ => False) (fun _ _ => False) w ψ X).
    assert ( (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) Γ,
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) Γ => False) γ ->
        exists y : R,
          ψ y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x)))).
    intros.
    contradict H0.
    pose proof (X1 H0).
    exact X2.


  +
    dependent destruction e.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_var_prt _ _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_true_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_false_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.


    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_int_prt _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_plus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_minus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_mult_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_lt_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 <? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_eq_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZeq _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 =? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_plus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_minus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_lt_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
                (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
                (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
                y1 <> y2 -> (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (Rltb'' y1 y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_mult_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct u.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_recip_prt _ _ _ _ _ (has_type_ro_OpRrecip _ _  r) (fun y x => ψ y (fst_app x, snd_app x)) X).
    assert (((fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) /\\\
        (fun (x : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => x <> 0)) ->>>
       (fun x : sem_datatype REAL => (fun (y : R) (x0 : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x0, snd_app x0)) (/ x))).
    intros h1 h2 [h3 _].
    destruct h3.
    pose proof (X0 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X1).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_coerce_prt _ _ _ _ (fun y x => False) (has_type_ro_OpZRcoerce _ _  r) X).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_exp_prt _ _ _ _ (fun y x => False) (has_type_ro_OpZRexp _ _  r) X).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_skip_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ X X0).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r, r0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r0 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1 X2).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_prt).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    apply (r_rw_case_list_prt Γ Δ _ _ f1 w f0 (fun _ => False) ψ).

    clear l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT2_nil.
    dependent destruction f.
    apply ForallT2_cons.
    apply IHl.
    split.
    simpl.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_prt.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_while_prt.
    pose proof (r_rw_while_prt _ _ _ _ _ _ w  _ _ X X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H0.
    contradict H0.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_new_var_prt.
    pose proof (r_rw_new_var_prt _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ w X X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H0; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof r_rw_assign_prt.
    pose proof (r_rw_assign_prt _ _ _ _ _ _ (fun _ => False) (fun _ _ => False) ψ w X).
    assert ((forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ),
                (fun (_ : sem_datatype τ) (_ : sem_ro_ctx (Δ ++ Γ)) => False) x (δ; γ) -> ψ tt (update' r w δ x, γ))).
    intros.
    contradict H.
    exact (X1 H).
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r. 
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_ro_lim_prt.
    pose proof (r_ro_lim_prt _ _ _ (fun _ => False) (fun _ _ => False)
                             (has_type_ro_Lim _ _ r) (fun y x => ψ y (fst_app x , snd_app x)) X).
    assert (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) (Δ ++ Γ),
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) (Δ ++ Γ) => False) γ ->
        exists y : R,
          (fun (y0 : R)
             (x : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                     match lst with
                     | nil => unit
                     | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                     end) (Δ ++ Γ)) => ψ y0 (fst_app x, snd_app x)) y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Δ ++ Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x))).
    intros.
    contradict H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

  +
    dependent destruction e.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_var_tot _ _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_true_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_false_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.


    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_int_tot _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_plus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_minus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_mult_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_lt_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 <? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_eq_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZeq _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 =? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_plus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_minus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_lt_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        y1 <> y2 /\ (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (Rltb'' y1 y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_mult_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct u.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_recip_tot _ _ _ _ _ (has_type_ro_OpRrecip _ _  r) (fun y x => ψ y (fst_app x, snd_app x)) X).
    assert ((fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) ->>>
       ((fun (x : R) (_ : sem_ro_ctx (Δ ++ Γ)) => x <> 0) /\\\
        (fun x : R => (fun (y : R) (x0 : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x0, snd_app x0)) (/ x)))).
    intros h1 h2 h3.
    destruct h3.
    pose proof (X0 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X1).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_coerce_tot _ _ _ _ (fun y x => False) (has_type_ro_OpZRcoerce _ _  r) X).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_exp_tot _ _ _ _ (fun y x => False) (has_type_ro_OpZRexp _ _  r) X).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_skip_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ). 
    apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ X X0).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ). 
    apply (r_rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r, r0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r0 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun b _ => b = true)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r0 (fun b _ => b = true)).
    apply (r_rw_case_tot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1 X2 X3 X4).
    intros.
    contradict H1.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_tot).
    pose (ForallT_map
            (fun _ x =>
               pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                    (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
            f).
    pose (ForallT_by_restriction (fun _ : exp * exp =>  sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ => False)).
    apply (r_rw_case_list_tot Γ Δ _ _ f1 w f0 f2 (fun _ => False) ψ).
    clear l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT3_nil.
    dependent destruction f.
    apply ForallT3_cons.
    apply IHl.
    split.
    split.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_tot.
    apply r_admissible_ro_exfalso_tot.
    intros.
    contradict H.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r.    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot (Γ ++ Δ) Δ e2 _ (has_type_rw_add_auxiliary _ _ _ _ H Δ) (fun _ _ => False)).
    assert (has_type_rw_add_auxiliary Γ Δ e2 UNIT H Δ
  ||~ [{(fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) =>
         ro_to_rw_pre (fun _ : sem_ro_ctx (Δ ++ Γ) => False) (fst δγδ', fst_app (snd δγδ')) /\
         fst δγδ' = snd_app (snd δγδ'))}] e2 [{_
                                              | (fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => (fun _ => False) (fst δγδ', fst_app (snd δγδ')) /\ False)}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    contradict H0.
    intros h1 h2 h3; auto.
    
    pose proof (r_rw_while_tot _ _ _ _ _ _ w _ _ (fun _ => False) X X1).
    assert  (forall (δ : sem_ro_ctx Δ) (γ : sem_ro_ctx Γ),
        (fun _ : sem_ro_ctx Δ * sem_ro_ctx Γ => False) (δ, γ) ->
        ~
        (exists f : nat -> sem_ro_ctx Δ,
           f 0%nat = δ /\
             (forall n : nat, (fun _ : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => False) (f (S n), (γ; f n))))).
    intros.
    contradict H0.
    pose proof (X2 H0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H1.
    contradict H1.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_new_var_tot.
    pose proof (r_rw_new_var_tot _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ w X X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H0; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_rw_assign_tot.
    pose proof (r_rw_assign_tot _ _ _ _ _ _ (fun _ => False) (fun _ _ => False) ψ w X).
    assert ((forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ),
                (fun (_ : sem_datatype τ) (_ : sem_ro_ctx (Δ ++ Γ)) => False) x (δ; γ) -> ψ tt (update' r w δ x, γ))).
    intros.
    contradict H.
    exact (X1 H).
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r. 
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_ro_lim_tot.
    pose proof (r_ro_lim_tot _ _ _ (fun _ => False) (fun _ _ => False)
                             (has_type_ro_Lim _ _ r) (fun y x => ψ y (fst_app x , snd_app x)) X).
    assert (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) (Δ ++ Γ),
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) (Δ ++ Γ) => False) γ ->
        exists y : R,
          (fun (y0 : R)
             (x : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                     match lst with
                     | nil => unit
                     | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                     end) (Δ ++ Γ)) => ψ y0 (fst_app x, snd_app x)) y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Δ ++ Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x))).
    intros.
    contradict H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
Defined.



Fixpoint proves_ro_prt_r_proves_ro_prt Γ e τ (w : Γ |- e : τ) ϕ ψ (p : w |- {{ϕ}} e {{ψ}}) : w |~ {{ϕ}} e {{ψ}}
with proves_ro_tot_r_proves_ro_tot Γ e τ (w : Γ |- e : τ) ϕ ψ (p : w |- [{ϕ}] e [{ψ}]) : w |~ [{ϕ}] e [{ψ}]
with proves_rw_prt_r_proves_rw_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (p : w ||- {{ϕ}} e {{ψ}}) : w ||~ {{ϕ}} e {{ψ}}
with proves_rw_tot_r_proves_rw_tot Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (p : w ||- [{ϕ}] e [{ψ}]) : w ||~ [{ϕ}] e [{ψ}].
Proof.
  +
    dependent induction p.
    pose proof (IHp P Q eq_refl).
    apply (r_ro_imply_prt _ _ _ _ _ _ _ _ a X a0).

    induction w.
Admitted.

  


  
End RestrictedRules.




Lemma proves_admissible_ro_prt_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  ψ ->>> θ -> w |- {{ϕ}} e {{θ}}.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma proves_admissible_ro_prt_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  θ ->> ϕ -> w |- {{θ}} e {{ψ}}.
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ H X H0).
Defined.

Lemma proves_admissible_ro_tot_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  ψ ->>> θ -> w |- [{ϕ}] e [{θ}].
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma proves_admissible_ro_tot_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  θ ->> ϕ -> w |- [{θ}] e [{ψ}].
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ H X H0).
Defined.

Section RoAccess.
  Fixpoint p_ro_access  Γ k τ (w : r_has_type_ro Γ (Var k) τ) : sem_ro_ctx Γ -> sem_datatype τ.
  Proof.
    inversion w.  
    intro.
    simpl in X.
    destruct X.
    exact s.
    intro.
    apply (p_ro_access _ _ _ H1).
    destruct X.
    exact s0.
  Defined.
  
  Fixpoint ro_access_Var_0 Γ τ (w : (τ :: Γ) |- Var 0 : τ) {struct w} : forall x (γ : sem_ro_ctx Γ), ro_access (τ :: Γ) 0 τ w (x, γ) = x.
  Proof.
    intros.
    dependent destruction w.
    dependent destruction h.
    assert (ro_access (τ :: Γ) 0 τ (has_type_ro_rw (τ :: Γ) (VAR 0) τ (has_type_rw_ro (τ :: Γ) nil (VAR 0) τ h)) (x, γ) = ro_access _ _ _ h (x, γ)).
    auto.
    rewrite H.
    apply ro_access_Var_0.
    simpl.
    clear ro_access_Var_0.
    auto.  
  Defined.

  Fixpoint has_type_ro_Var_S_inv Γ k τ σ (w : (τ :: Γ) |- Var (S k) : σ) : Γ |- Var k : σ.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_Var_S_inv _ _ _ _ h).
    exact w.
  Defined.

  Fixpoint ro_access_Var_S Γ k τ σ (w : (τ :: Γ) |- Var (S k) : σ) {struct w} : forall x (γ : sem_ro_ctx Γ),
      ro_access (τ :: Γ) (S k) σ w (x, γ) = ro_access Γ k σ (has_type_ro_Var_S_inv _ _ _ _ w) γ .
  Proof.
    intros.
    dependent destruction w.
    dependent destruction h.
    assert (ro_access (τ :: Γ) (S k) τ0 (has_type_ro_rw (τ :: Γ) (VAR S k) τ0 (has_type_rw_ro (τ :: Γ) nil (VAR S k) τ0 h)) (x, γ) = ro_access _ _ _ h (x, γ)).
    auto.
    rewrite H.
    assert ((has_type_ro_Var_S_inv Γ k τ τ0 (has_type_ro_rw (τ :: Γ) (VAR S k) τ0 (has_type_rw_ro (τ :: Γ) nil (VAR S k) τ0 h))) = (has_type_ro_Var_S_inv Γ k τ τ0 h)).
    simpl.
    unfold simplification_heq.
    unfold solution_left.
    unfold eq_rect_r.
    simpl.
    
    rewrite (prop_irrl _ (eq_sym _) eq_refl).
    simpl.
    auto.
    rewrite H0.
    apply ro_access_Var_S.
    simpl.
    
    unfold eq_rect_r.
    simpl.  
    unfold simplification_heq.
    unfold solution_left.
    unfold eq_rect_r.
    rewrite (prop_irrl _ (eq_sym _) eq_refl).
    simpl.
    rewrite (prop_irrl _ (eq_sym _) eq_refl).
    simpl.
    auto.
  Defined.

  Lemma ro_access_typing_irrl k : forall Γ τ (w1 : Γ |- Var k : τ) (w2 : Γ |- Var k : τ) γ, ro_access Γ k τ w1 γ = ro_access Γ k τ w2 γ.
  Proof.
    dependent induction k; intros.
    destruct Γ.
    contradict w1.
    intro.
    apply has_type_ro_r_has_type_ro in w1.
    apply r_has_type_ro_Var_absurd in w1.
    auto.
    simpl in γ.
    destruct γ.
    pose proof (has_type_ro_unambiguous _ _ _ _ w1 (has_type_ro_Var_0 Γ d)).
    induction H.
    rewrite (ro_access_Var_0 Γ τ w1 ).
    rewrite (ro_access_Var_0 Γ τ w2 ).
    auto.
    destruct Γ.
    contradict w1.
    intro.
    apply has_type_ro_r_has_type_ro in w1.
    apply r_has_type_ro_Var_absurd in w1.
    auto.
    simpl in γ.
    destruct γ.
    rewrite ro_access_Var_S.
    rewrite ro_access_Var_S.
    apply (IHk _ _ (has_type_ro_Var_S_inv Γ k d τ w1) (has_type_ro_Var_S_inv Γ k d τ w2)).
  Defined.

  Fixpoint ro_access_app  Γ γ k τ w Δ δ w':
      ro_access Γ k τ w γ = ro_access (Γ ++ Δ) k τ w' (γ ; δ).
  Proof.
    intros.
    dependent induction w.
    dependent destruction h.
    easy_rewrite_uip.
    apply ro_access_app.
    simpl.
    easy_rewrite_uip.
    destruct γ.
    simpl in w'.
    rewrite ro_access_Var_0.
    reflexivity.
    easy_rewrite_uip.
    destruct γ.
    rewrite ro_access_Var_S.
    
    rewrite (ro_access_app Γ s0 k0 τ w Δ δ (has_type_ro_Var_S_inv (Γ ++ Δ) k0 σ τ w')).
    reflexivity.
  Qed.
  
End RoAccess.


Fixpoint proves_admissible_ro_prt_proj Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ
         (X : w' |- {{ϕ}} e {{ψ}}) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}}

with proves_admissible_ro_tot_proj Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ
                                   (X : w' |- [{ϕ}] e [{ψ}]) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w |- [{fun γ => exists γ', ϕ (γ ; γ')}] e [{y | fun γ => exists γ', ψ y (γ ; γ')}]

with proves_admissible_rw_prt_proj Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ
                                   (X : w' ||- {{ϕ}} e {{ψ}}) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w ||- {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}}

with proves_admissible_rw_tot_proj Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ
                                   (X : w' ||- [{ϕ}] e [{ψ}]) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w ||- [{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}] e [{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}].
Proof.
  +
    dependent induction X.

    pose proof (proves_admissible_ro_prt_proj _ _ _ _ w w' _ _ X) as X0.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X0).
    intros h1 [x h2].
    exists x.
    apply a; auto.
    intros h1 h2 [x h3].
    exists x.
    apply a0; auto.

    pose proof (ro_exfalso_prt _ _ _ w (fun y => (fun γ : sem_ro_ctx Γ => exists γ' : sem_ro_ctx Γ', ψ y (γ; γ')))).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 [x h2].
    auto.
    intros h1 h2 [x h3].
    exists x.
    auto.

    pose proof (proves_admissible_ro_prt_proj _ _ _ _ w w' _ _ X1) as Y1.
    pose proof (proves_admissible_ro_prt_proj _ _ _ _ w w' _ _ X2) as Y2.
    pose proof (ro_conj_prt _ _ _ _ _ _ _ Y1 Y2).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 [x h2].
    exists x; auto.
    intros h1 h2 [[x h3] [y h4]].
    exists x.
    
    auto.

    


    
    
Admitted.



Fixpoint proves_admissible_ro_prt_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- {{ϕ}} e {{ψ}}) {struct X} :
  w |- {{ϕ /\\ θ}} e {{ψ /\\\ fun _ => θ}}
with proves_admissible_ro_tot_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- [{ϕ}] e [{ψ}]) {struct X} :
  w |- [{ϕ /\\ θ}] e [{ψ /\\\ fun _ => θ}]
with proves_admissible_rw_prt_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- {{ϕ}} e {{ψ}}) {struct X} :
  w ||- {{ϕ /\\ fun δγ => θ (snd δγ) }} e {{ψ /\\\ fun _ δγ => θ (snd δγ)}}
with proves_admissible_rw_tot_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} :
  w ||- [{ϕ /\\ fun δγ => θ (snd δγ)}] e [{ψ /\\\ fun _ δγ => θ (snd δγ)}].
Proof.
  +
    dependent induction X.
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (ro_exfalso_prt Γ e τ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    assert (((fun _ : sem_ro_ctx Γ => False) /\\ θ) ->> (fun _ : sem_ro_ctx Γ => False)).
    intros a [b c]; contradict b.
    assert ((ψ /\\\ (fun _ : sem_datatype τ => θ)) ->>> (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    intros a b; auto.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ H X H0).

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_conj_prt _ _ _ _ _ _ _  X X0).
    apply (proves_admissible_ro_prt_post_weaken X3).
    intros a b [[c d] [f g]]; repeat split; auto.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_disj_prt _ _ _ _ _ _ _  X X0).
    apply (proves_admissible_ro_prt_pre_strengthen X3).
    intros a b.
    destruct b.
    destruct H.
    left; split; auto.
    right; split; auto.

    pose proof (ro_var_prt _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (proves_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_skip_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (ro_true_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_false_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_int_prt _ _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ p).
    pose proof (rw_ro_prt _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun x => (θ (fst_app x))) X).
    pose proof (ro_proj_prt _ _ _ _ w _ _ _ X0).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2.
    destruct H.
    exists x.
    split; auto.
    unfold fst_app; rewrite tedious_equiv_1.
    exact H0.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split.
    exists x; auto.
    unfold fst_app in H0; rewrite tedious_equiv_1 in H0.
    exact H0.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_coerce_prt _ _ w _ _ w').
    apply (proves_admissible_ro_prt_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_exp_prt _ _ w _ _ w').
    apply (proves_admissible_ro_prt_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_recip_prt _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    split.
    apply a.
    split.
    destruct H; auto.
    auto.
    destruct H; auto.
    
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.
    auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ro_ctx (INTEGER :: Γ) => θ (snd x)) p).
    apply (ro_lim_prt _ _ _ _ _ _ _ X).
    intros.
    destruct H.
    pose proof (e0 _ H).
    destruct H1.
    exists x.
    split.
    split; auto.
    destruct H1; auto.
    intros.
    destruct H2.
    destruct H1.
    pose proof (H4 x0 z H2).
    exact H5.

  +
    dependent induction X.
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (ro_imply_tot _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (ro_exfalso_tot Γ e τ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    assert (((fun _ : sem_ro_ctx Γ => False) /\\ θ) ->> (fun _ : sem_ro_ctx Γ => False)).
    intros a [b c]; contradict b.
    assert ((ψ /\\\ (fun _ : sem_datatype τ => θ)) ->>> (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    intros a b; auto.
    apply (ro_imply_tot _ _ _ _ _ _ _ _ H X H0).

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_conj_tot _ _ _ _ _ _ _  X X0).
    apply (proves_admissible_ro_tot_post_weaken X3).
    intros a b [[c d] [f g]]; repeat split; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_disj_tot _ _ _ _ _ _ _  X X0).
    apply (proves_admissible_ro_tot_pre_strengthen X3).
    intros a b.
    destruct b.
    destruct H.
    left; split; auto.
    right; split; auto.

    pose proof (ro_var_tot _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (proves_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_skip_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (ro_true_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_false_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_int_tot _ _  w (ψ /\\\ (fun _ => θ))).
    apply (proves_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ p).
    pose proof (rw_ro_tot _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => (θ (fst_app x))) X).
    pose proof (ro_proj_tot _ _ _ _ w _ _ _ X0).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2.
    destruct H.
    exists x.
    split; auto.
    unfold fst_app; rewrite tedious_equiv_1.
    exact H0.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split.
    exists x; auto.
    unfold fst_app in H0; rewrite tedious_equiv_1 in H0.
    exact H0.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_coerce_tot _ _ w _ _ w').
    apply (proves_admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_exp_tot _ _ w _ _ w').
    apply (proves_admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_recip_tot _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    destruct (a _ _ H).
    
    split; auto.
    split; auto.
    
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_eq_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    destruct (a _ _ _ H H0).
    split; auto.
    split; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ro_ctx (INTEGER :: Γ) => θ (snd x)) X).
    apply (ro_lim_tot _ _ _ _ _ _ _ X0).
    intros.
    destruct H.
    pose proof (e0 _ H).
    destruct H1.
    exists x.
    split.
    split; auto.
    destruct H1; auto.
    intros.
    destruct H2.
    destruct H1.
    pose proof (H4 x0 z H2).
    exact H5.

    
  +
    dependent induction X.
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (rw_exfalso_prt _ _ _ _ w (ψ /\\\ fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))).    
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_conj_prt _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H, H0; split; auto. 
    destruct H, H0;  auto.

    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_disj_prt _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    destruct h2.
    destruct H.
    left; split; auto.
    right; split; auto.
    intros h1 h2 h3; auto.

    
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) p).
    pose proof (ro_rw_prt _ _ _ _ _ _ _ w' X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    split; auto.
    destruct h1.
    simpl in H0.
    unfold snd_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h2, h3.
    split; auto.
    simpl.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ (fun δγγ' : sem_ro_ctx (Γ ++ Γ') => θ (fst_app ( δγγ'))) X).
    pose proof (rw_proj_prt _ _ _ _ _ w _ _ _ X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2.
    destruct H.
    exists x; split; auto.
    simpl.
    unfold fst_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split; auto.
    exists x; auto.
    simpl in H0; unfold fst_app in H0; rewrite tedious_equiv_1 in H0.
    auto.

    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) p).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (rw_new_var_prt Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (rw_assign_prt _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_cond_prt _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p0).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_case_prt _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.


    apply (rw_case_list_prt _ _ _ _ wty_l wty (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app x))) θ0)).
    clear wty.
    dependent induction f.
    apply ForallT2_nil.
    simpl.
    apply ForallT2_cons.
    apply IHf.
    destruct p.
    simpl.
    destruct r.
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ p0).
    split.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).    
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; destruct h3; split; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).    
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    auto.
    intros h1 h2 h3; auto.
    assert
      (wty ||- {{(ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ)))}} (WHILE e DO c END) {{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}}).
    apply (rw_while_prt _ _ _ _ wty_e wty_c wty).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.
    pose proof (proves_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1; rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3.
    auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.


  +
    dependent induction X.
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (rw_exfalso_tot _ _ _ _ w (ψ /\\\ fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))).    
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_conj_tot _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H, H0; split; auto. 
    destruct H, H0;  auto.

    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_disj_tot _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    destruct h2.
    destruct H.
    left; split; auto.
    right; split; auto.
    intros h1 h2 h3; auto.

    
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) p).
    pose proof (ro_rw_tot _ _ _ _ _ _ _ w' X).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    split; auto.
    destruct h1.
    simpl in H0.
    unfold snd_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h2, h3.
    split; auto.
    simpl.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ (fun δγγ' : sem_ro_ctx (Γ ++ Γ') => θ (fst_app ( δγγ'))) X).
    pose proof (rw_proj_tot _ _ _ _ _ w _ _ _ X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2.
    destruct H.
    exists x; split; auto.
    simpl.
    unfold fst_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split; auto.
    exists x; auto.
    simpl in H0; unfold fst_app in H0; rewrite tedious_equiv_1 in H0.
    auto.

    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_sequence_tot _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) p).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (rw_new_var_tot Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (rw_assign_tot _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_cond_tot _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p0).
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p1).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p2).

    apply (rw_case_tot _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))
                       _
                       (ϕ1 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ)))      
                       (ϕ2 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ)))
          ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X5).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    destruct h3.
    auto.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X6).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    destruct h3.
    auto.
    intros.
    destruct H.
    destruct (o _ H). 
    left; split; auto.
    right; split; auto.

    
    apply (rw_case_list_tot _ _ _ _ wty_l wty
                            (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app x))) θ0)
                            (ForallT_map (fun _ p => p /\\ (fun x => θ (snd_app x))) ϕi)
          ).
    clear wty.
    clear f0.
    dependent induction f.
    apply ForallT3_nil.
    simpl.
    apply ForallT3_cons.
    simpl.
    apply IHf.
    repeat split.
    destruct j as [[j _] _].
    pose proof (proves_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct j as [[_ j] _].
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _  θ j) as i.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    destruct h2; split; auto.
    destruct h1; unfold snd_app in H0;  auto.
    rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.
    destruct j as [_ j].
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct h3; auto.
    intros.
    destruct H.
    pose proof (f0 x H).
    clear f f0 wty wty_l θ0.

    induction ϕi.
    simpl in H1; simpl; auto.
    simpl.
    simpl in H1.
    destruct H1.
    left; split; auto.
    right.
    apply IHϕi.
    exact H1.

    assert
      (wty ||- [{(ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ)))}] (WHILE e DO c END) [{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}]).
    apply (rw_while_tot _ _ _ _ wty_e wty_c wty _ _ ψ0).
    pose proof (proves_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.
    pose proof (proves_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ (fun x => θ ((fst_app x))) X).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    destruct H; split; auto.
    destruct H.
    unfold snd_app in H1.
    rewrite tedious_equiv_1 in H1.
    exact H1.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split; auto.
    split; auto.
    intros.
    destruct H.
    apply n; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.
Defined.






Fixpoint proves_admissible_ro_tot_prt Γ e τ (w : Γ |- e : τ) ϕ ψ (X : w |- [{ϕ}] e [{ψ}]) {struct X} : w |- {{ϕ}} e {{ψ}}
with proves_admissible_rw_tot_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} : w ||- {{ϕ}} e {{ψ}}.
Proof.
  +
    intros.
    dependent induction X.
    
    apply (ro_imply_prt _ _ _ _ _ _ _ _ a (proves_admissible_ro_tot_prt _ _ _ _ _ _ X) a0).
    apply ro_exfalso_prt.
    apply (ro_conj_prt _ _ _ _ _ _ _  (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply (ro_disj_prt _ _ _ _ _ _ _  (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply ro_var_prt.
    apply ro_skip_prt.
    apply ro_true_prt.
    apply ro_false_prt.
    apply ro_int_prt.
    apply (rw_ro_prt _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ p)).
    apply (ro_proj_prt _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_coerce_prt _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_exp_prt _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    assert (sc:  (θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> Rdefinitions.IZR BinNums.Z0)) ->>>
                                                                                                               (fun x : sem_datatype REAL => ψ (Rdefinitions.RinvImpl.Rinv x))).
    {
      intros γ δ [m1 m2].
      apply a; auto.
    }
    apply (ro_recip_prt _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X) sc).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).

    assert (sc : (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ),
                     ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ)).
    {
      intros; apply a; auto.
    }
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) sc).

    apply (ro_lim_prt _ _ _ _ _ _ _ X e0).

  +
    dependent induction X.
    
    
    apply (rw_imply_prt _ _ _ _ _ _ _ _ _ a (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X) a0).
    apply rw_exfalso_prt.
    apply (rw_conj_prt _ _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).

    apply (rw_disj_prt _ _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (ro_rw_prt _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p)).

    apply (rw_proj_prt _ _ _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X)).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _  (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X)).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) ψ0).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p p0 (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).



    {
      (* case list *)
      apply (rw_case_list_prt _ _ _ _ wty_l wty θ).
      clear f0 wty.
      dependent induction f.
      simpl.
      apply ForallT2_nil.
      apply ForallT2_cons.
      apply IHf.
      destruct j.
      destruct p0.
      split.
      exact p0.
      exact ((proves_admissible_rw_tot_prt _ _ _ _ _ _ _ p2)).      
    }


    
    {
      pose proof (has_type_while_inv_body _ _ _ _ wty).
      apply (rw_while_prt _ _ _ _ wty_e H wty ϕ _ (
                            (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) 
                          )

            ).
      apply proves_admissible_rw_tot_prt in X.
      pose proof (rw_proj_prt Γ Δ Δ c DUnit H wty_c _ _ X).
      assert (ro_to_rw_pre (θ true) ->> (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ =>
                                           exists γ' : sem_ro_ctx Δ,
                                             (fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) =>
                                                ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ'))
                                               (fst δγ, (snd δγ; γ')))).
      {
        simpl.
        intros δγ h.
        exists (fst δγ); auto.
        unfold snd_app.
        unfold fst_app.
        rewrite tedious_equiv_1.
        destruct δγ; split; auto.
      }
      assert ((fun y => (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ =>
                           exists γ' : sem_ro_ctx Δ,
                             (fun (_ : sem_datatype UNIT) (δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ)) =>
                                ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ0 δγδ') y (fst δγ, (snd δγ; γ')))) ->>>
                                                                                                        fun _ => ϕ).

      {
        simpl.
        intros _ δγ [γ' [h1 h2]].
        unfold fst_app in h1.
        rewrite tedious_equiv_1 in h1.
        destruct δγ; auto.
      }
      exact (rw_imply_prt _ _ _ _ _ _ _ _ _ H0 X0 H1).
    }
    
Defined.


