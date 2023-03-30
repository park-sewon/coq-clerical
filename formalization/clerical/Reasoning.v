Require Import Clerical.
Require Import Typing.
Require Import Semantics.
Require Import Specification.
Require Import Reals.
Require Import List.

Reserved Notation " w |- [ P ] e [ y : T | Q ]t " (at level 50, P, e, y, T, Q at next level).
Reserved Notation " w |- [ P ] e [ y : T | Q ]p " (at level 50, P, e, y, T, Q at next level).
Reserved Notation " w ||- { P } e { y : T | Q }t " (at level 50, P, e, y, T, Q at next level).
Reserved Notation " w ||- { P } e { y : T | Q }p " (at level 50, P, e, y, T, Q at next level).



Reserved Notation " w |- {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w |- {{ P }} e {{ y | Q }} " (at level 50, P, e,y, Q at next level).
Reserved Notation " w |- [[ P ]] e [[ Q ]] " (at level 50, P, e, Q at next level).
Reserved Notation " w ||- {{ P }} e {{ Q }} " (at level 50, P, e, Q at next level).
Reserved Notation " w ||- [[ P ]] e [[ Q ]] " (at level 50, P, e, Q at next level).
Reserved Notation " w |- [[ P ]] e [[ y | Q ]] " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||- {{ P }} e {{ y | Q }} " (at level 50, P, e, y, Q at next level).
Reserved Notation " w ||- [[ P ]] e [[ y | Q ]] " (at level 50, P, e, y, Q at next level).


Definition mk_ro_prt {Γ} {e} {τ} (w : Γ |- e : τ) P Q : ro_prt w
  := {| ro_prt_pre := P ; ro_prt_post := Q |}.

Definition mk_ro_tot {Γ} {e} {τ} (w : Γ |- e : τ) P Q : ro_tot w
  := {| ro_tot_pre := P ; ro_tot_post := Q |}.

Definition mk_rw_prt {Γ Δ} {e} {τ} (w : Γ ;;; Δ ||- e : τ) P Q : rw_prt w
  := {| rw_prt_pre := P ; rw_prt_post := Q |}.

Definition mk_rw_tot {Γ Δ} {e} {τ} (w : Γ ;;; Δ ||- e : τ) P Q : rw_tot w
  := {| rw_tot_pre := P ; rw_tot_post := Q |}.

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

Infix "∧" := asrt_and (at level 80).
Infix "∨" := asrt_or (at level 80).

Fixpoint ro_access  Γ k τ (w: Γ |- Var k : τ) : sem_ro_ctx Γ -> sem_datatype τ.
Proof.
  inversion w.
  inversion H.
  simpl in H7.
  exact (ro_access _ _ _ H7).
  intro.
  simpl in X.
  destruct X.
  exact s.
  intro.
  apply (ro_access _ _ _ H1).
  destruct X.
  exact s0.
Defined.

Definition rw_to_ro_pre {Γ Δ} (ϕ : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop) :=
                        fun δγ => ϕ (tedious_sem_concat _ _ δγ).

Definition ro_to_rw_pre {Γ Δ} (ϕ : sem_ro_ctx (Δ ++ Γ) -> Prop) : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop := fun δγ => ϕ (tedious_prod_sem Δ Γ δγ) .

Definition fst_concat {Γ Δ} : sem_ro_ctx (Γ ++ Δ) -> sem_ro_ctx Γ.
Proof.
  intro γδ.
  destruct (tedious_sem_concat _ _ γδ) as [γ _].
  exact γ.
Defined.

Definition snd_concat {Γ Δ} : sem_ro_ctx (Γ ++ Δ) -> sem_ro_ctx Δ.
Proof.
  intro γδ.
  destruct (tedious_sem_concat _ _ γδ) as [_ δ].
  exact δ.
Defined.

Definition pair_concat {Γ Δ} : sem_ro_ctx Γ -> sem_ro_ctx Δ -> sem_ro_ctx (Γ ++ Δ).
Proof.
  intros γ δ.
  apply tedious_prod_sem.
  exact (γ, δ).
Defined.

Notation " ( γ ; δ ) " := (pair_concat γ δ).

Inductive proves_ro_prt : forall Γ e τ (w : Γ |- e : τ), ro_prt w -> Type :=
(** logical rules *)
  
| ro_imply_prt : forall Γ e τ (w : Γ |- e : τ) P Q P' Q',
    P' ->> P -> w |- {{ P }} e {{ Q }} -> Q ->>> Q' -> w |- {{ P'}}  e {{ Q' }}

| ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q,
    w |- {{ (fun _ => False) }} e {{ Q }}

| ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q Q',
    w |- {{P}} e {{Q}} -> w |- {{P}} e {{Q'}} -> w |- {{P}} e {{Q /\\\ Q'}}

| ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P P' Q,
    w |- {{P}} e {{Q}} -> w |- {{P'}} e {{Q}} -> w |- {{P ∨ P'}} e {{Q}}

(** variables and constants *)

| ro_var_prt : forall Γ k τ (w : Γ |- Var k : τ) Q,
    w |- {{fun γ => Q (ro_access Γ k τ w γ) γ}} Var k {{Q}}

| ro_skip_prt : forall Γ (w : Γ |- Skip : DUnit) Q,
    w |- {{Q tt}} Skip {{Q}}

| ro_true_prt : forall Γ (w : Γ |- TRUE : DBoolean) Q,
    w |- {{Q true}} TRUE {{Q}}

| ro_false_prt : forall Γ (w : Γ |- FALSE : DBoolean) Q,
    w |- {{Q false}} FALSE {{Q}}

| ro_int_prt : forall Γ k (w : Γ |- INT k : DInteger) Q,
    w |- {{Q k}} INT k {{Q}}

(** passage between read-only and read-write correctness *)

| rw_ro_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    w ||- {{P}} c {{Q}} -> w' |- {{fun γ => P (tt, γ)}} c {{fun v w => Q v (tt, w)}}

(** coercion and exponentiation *)

| ro_coerce_prt : forall Γ e (w : Γ |- e : DInteger) P Q (w' : Γ |- UniOp OpZRcoerce e : DReal),
    w |- {{P}} e {{y | Q (IZR y)}} -> w' |- {{P}} UniOp OpZRcoerce e {{Q}}

| ro_exp_prt : forall Γ e (w : Γ |- e : DInteger) P Q (w' : Γ |- UniOp OpZRexp e : DReal),
    w |- {{P}} e {{y | Q (powerRZ 2 y)}} -> w' |- {{P}} UniOp OpZRexp e {{Q}}

(** integer arithmetic  *)
| ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                          (w' : Γ |- (BinOp OpZplus e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zplus y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpZplus e1 e2) {{Q}}
| ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                          (w' : Γ |- (BinOp OpZmult e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zmult y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpZmult e1 e2) {{Q}}

| ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                          (w' : Γ |- (BinOp OpZminus e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zminus y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpZminus e1 e2) {{Q}}

(** real arithmetic  *)
| ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                          (w' : Γ |- (BinOp OpRplus e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rplus y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpRplus e1 e2) {{Q}}
| ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                          (w' : Γ |- (BinOp OpRmult e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rmult y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpRmult e1 e2) {{Q}}
| ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                          (w' : Γ |- (BinOp OpRminus e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rminus y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpRminus e1 e2) {{Q}}
(** reciprocal *)
| ro_recip_prt : forall Γ e (w : Γ |- e : DReal) ϕ θ (w' : Γ |- UniOp OpRrecip e : DReal) ψ,
    w |- {{ϕ}} e {{θ}} -> (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) -> w' |- {{ϕ}} UniOp OpRrecip e {{ψ}}

(** integer comparison  *)
| ro_int_comp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                          (w' : Γ |- (BinOp OpZeq e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Z.eqb y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpZeq e1 e2) {{Q}}

| ro_int_comp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                          (w' : Γ |- (BinOp OpZlt e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Z.ltb y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpZlt e1 e2) {{Q}}

(** real comparison  *)
| ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                          (w' : Γ |- (BinOp OpRlt e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- {{P}} e1 {{Q1}} -> w2 |- {{P}} e2 {{Q2}} -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> y1 <> y2 -> Q (Rltb'' y1 y2) γ)
                                   -> w' |- {{P}} (BinOp OpRlt e1 e2) {{Q}}

(* Limit *)
| ro_lim_prt : forall Γ e (w : (DInteger :: Γ) |- e : DReal) ϕ θ (w' : Γ |- Lim e : DReal) ψ,
    w |- [[fun γ' => ϕ (snd γ')]] e [[θ]] ->
         (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
         w' |- {{ϕ}} Lim e {{ψ}}
                                                        
with proves_ro_tot : forall Γ e τ (w : Γ |- e : τ), ro_tot w -> Type :=
(** logical rules *)
  
| ro_imply_tot : forall Γ e τ (w : Γ |- e : τ) P Q P' Q',
    P' ->> P -> w |- [[ P ]] e [[ Q ]] -> Q ->>> Q' -> w |- [[ P']]  e [[ Q' ]]

| ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q,
    w |- [[ (fun _ => False) ]] e [[ Q ]]

| ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q Q',
    w |- [[P]] e [[Q]] -> w |- [[P]] e [[Q']] -> w |- [[P]] e [[Q /\\\ Q']]

| ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P P' Q,
    w |- [[P]] e [[Q]] -> w |- [[P']] e [[Q]] -> w |- [[P ∨ P']] e [[Q]]

(* variables and constants *)

| ro_var_tot : forall Γ k τ (w : Γ |- Var k : τ) Q,
    w |- [[fun γ => Q (ro_access Γ k τ w γ) γ]] Var k [[Q]]

| ro_skip_tot : forall Γ (w : Γ |- Skip : DUnit) Q,
    w |- [[Q tt]] Skip [[Q]]

| ro_true_tot : forall Γ (w : Γ |- TRUE : DBoolean) Q,
    w |- [[Q true]] TRUE [[Q]]

| ro_false_tot : forall Γ (w : Γ |- FALSE : DBoolean) Q,
    w |- [[Q false]] FALSE [[Q]]

| ro_int_tot : forall Γ k (w : Γ |- INT k : DInteger) Q,
    w |- [[Q k]] INT k [[Q]]

(* passage between read-only and read-write correctness *)

| rw_ro_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ),
    w ||- [[P]] c [[Q]] -> w' |- [[fun γ => P (tt, γ)]] c [[fun v w => Q v (tt, w)]]                                           
                                                        
(** coercion and exponentiation *)

| ro_coerce_tot : forall Γ e (w : Γ |- e : DInteger) P Q (w' : Γ |- UniOp OpZRcoerce e : DReal),
    w |- [[P]] e [[y | Q (IZR y)]] -> w' |- [[P]] UniOp OpZRcoerce e [[Q]]

| ro_exp_tot : forall Γ e (w : Γ |- e : DInteger) P Q (w' : Γ |- UniOp OpZRexp e : DReal),
    w |- [[P]] e [[y | Q (powerRZ 2 y)]] -> w' |- [[P]] UniOp OpZRexp e [[Q]]

(** integer arithmetic  *)
| ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                              (w' : Γ |- (BinOp OpZplus e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zplus y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpZplus e1 e2) [[Q]]
| ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                              (w' : Γ |- (BinOp OpZmult e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zmult y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpZmult e1 e2) [[Q]]

| ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                               (w' : Γ |- (BinOp OpZminus e1 e2) : DInteger) (Q : sem_datatype DInteger -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Zminus y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpZminus e1 e2) [[Q]]

(** real arithmetic  *)
| ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                               (w' : Γ |- (BinOp OpRplus e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rplus y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpRplus e1 e2) [[Q]]
| ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                               (w' : Γ |- (BinOp OpRmult e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rmult y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpRmult e1 e2) [[Q]]
| ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                                (w' : Γ |- (BinOp OpRminus e1 e2) : DReal) (Q : sem_datatype DReal -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Rminus y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpRminus e1 e2) [[Q]]
(** reciprocal *)
| ro_recip_tot : forall Γ e (w : Γ |- e : DReal) ϕ θ (w' : Γ |- UniOp OpRrecip e : DReal) ψ,
    w |- [[ϕ]] e [[θ]] -> (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) -> w' |- [[ϕ]] UniOp OpRrecip e [[ψ]]

(** integer comparison  *)
| ro_int_comp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                              (w' : Γ |- (BinOp OpZeq e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Z.eqb y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpZeq e1 e2) [[Q]]

| ro_int_comp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DInteger) (w2 : Γ |- e2 : DInteger) P Q1 Q2
                              (w' : Γ |- (BinOp OpZlt e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> Q (Z.ltb y1 y2) γ)
                                   -> w' |- [[P]] (BinOp OpZlt e1 e2) [[Q]]

(** real comparison  *)
| ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : DReal) (w2 : Γ |- e2 : DReal) P Q1 Q2
                          (w' : Γ |- (BinOp OpRlt e1 e2) : DBoolean) (Q : sem_datatype DBoolean -> sem_ro_ctx Γ -> Prop),
    w1 |- [[P]] e1 [[Q1]] -> w2 |- [[P]] e2 [[Q2]] -> (forall y1 y2 γ, Q1 y1 γ -> Q2 y2 γ -> (y1 <> y2 /\ Q (Rltb'' y1 y2) γ))
                                   -> w' |- [[P]] (BinOp OpRlt e1 e2) [[Q]]

(* Limit *)
| ro_lim_tot : forall Γ e (w : (DInteger :: Γ) |- e : DReal) ϕ θ (w' : Γ |- Lim e : DReal) ψ,
    w |- [[fun γ' => ϕ (snd γ')]] e [[θ]] ->
         (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) ->
         w' |- [[ϕ]] Lim e [[ψ]]

                                                        
                                                        
with proves_rw_prt : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_prt w -> Type :=
(** logical rules *)
  
| rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P Q P' Q',
    P' ->> P -> w ||- {{ P }} e {{ Q }} -> Q ->>> Q' -> w ||- {{ P'}}  e {{ Q' }}

| rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) Q,
    w ||- {{ (fun _ => False) }} e {{ Q }}

| rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P Q Q',
    w ||- {{P}} e {{Q}} -> w ||- {{P}} e {{Q'}} -> w ||- {{P}} e {{Q /\\\ Q'}}

| rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P P' Q,
    w ||- {{P}} e {{Q}} -> w ||- {{P'}} e {{Q}} -> w ||- {{P ∨ P'}} e {{Q}}

(** passage between read-only and read-write correctness *)

| ro_rw_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) P Q (w' : Γ ;;; Δ ||- e : τ),
    w |- {{P}} e {{Q}} -> w' ||- {{fun γδ => P (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => Q v (tedious_prod_sem _ _ γδ)}}

(** operational proof rules  *)
                             
| rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- Seq c1 c2 : τ),
    w1 ||- {{ϕ}} c1 {{θ}} -> w2 ||- {{θ tt}} c2 {{ψ}} -> w' ||- {{ϕ}} Seq c1 c2 {{ψ}}

| rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ)
                          (ϕ : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop)
                          θ (w' : Γ ;;; Δ ||- Newvar e c : τ)
                          (ψ : sem_datatype τ -> (sem_ro_ctx Δ * sem_ro_ctx Γ) -> Prop),
    w1 |- {{fun γδ => (ϕ (tedious_sem_concat _ _ γδ))}} e {{θ}}
          -> w2 ||- {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}}
          -> w' ||- {{ϕ}} Newvar e c {{ψ}}

| rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ
                         (ψ : sem_datatype (DUnit) -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop)
                         (w' : Γ ;;; Δ ||- Assign k e: DUnit),
    w |- {{fun δγ => ϕ (tedious_sem_concat _ _ δγ)}} e {{θ}}
         -> (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ))
         -> w' ||- {{ϕ}} Assign k e {{ψ}}

| rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : DBoolean) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,
    w |- {{rw_to_ro_pre ϕ}} e {{θ}} ->
         w1 ||- {{ro_to_rw_pre (θ true)}} c1 {{ψ}} ->
         w2 ||- {{ro_to_rw_pre (θ false)}} c2 {{ψ}} ->
         w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}

| rw_case_prt : forall Γ Δ e1 e2 c1 c2 τ
                       (wty_e1 : (Δ ++ Γ) |- e1 : DBoolean)
                       (wty_e2 : (Δ ++ Γ) |- e2 : DBoolean)
                       (wty_c1 : Γ ;;; Δ ||- c1 : τ)
                       (wty_c2 : Γ ;;; Δ ||- c2 : τ)
                       (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ)
                       ϕ θ1 θ2 ψ,
    wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}}
              -> wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}}
                           -> wty_c1 ||- {{ro_to_rw_pre (θ1 true)}} c1 {{ψ}}
                           -> wty_c2 ||- {{ro_to_rw_pre (θ2 true)}} c2 {{ψ}}
                           -> wty ||- {{ϕ}} Case e1 c1 e2 c2 {{ψ}}
                                  
| rw_while_prt : forall Γ Δ e c
                        (wty_e : (Δ ++ Γ) |- e : DBoolean)
                        (wty_c : Γ ;;; Δ ||- c : DUnit)
                        (wty : Γ ;;; Δ ||- While e c : DUnit)
                        ϕ θ,
    wty_e |- {{rw_to_ro_pre ϕ}} e {{θ}} -> wty_c ||- {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} -> wty ||- {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}}
                        

                                  
with proves_rw_tot : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_tot w -> Type :=
(** logical rules *)
  
| rw_imply_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P Q P' Q',
    P' ->> P -> w ||- [[ P ]] e [[ Q ]] -> Q ->>> Q' -> w ||- [[ P']]  e [[ Q' ]]

| rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) Q,
    w ||- [[ (fun _ => False) ]] e [[ Q ]]

| rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P Q Q',
    w ||- [[P]] e [[Q]] -> w ||- [[P]] e [[Q']] -> w ||- [[P]] e [[Q /\\\ Q']]

| rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) P P' Q,
    w ||- [[P]] e [[Q]] -> w ||- [[P']] e [[Q]] -> w ||- [[P ∨ P']] e [[Q]]

(** operational proof rules  *)
                                                                                  
| rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- Seq c1 c2 : τ),
    w1 ||- [[ϕ]] c1 [[θ]] -> w2 ||- [[θ tt]] c2 [[ψ]] -> w' ||- [[ϕ]] Seq c1 c2 [[ψ]]

| rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ)
                          (ϕ : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop)
                          θ (w' : Γ ;;; Δ ||- Newvar e c : τ)
                          (ψ : sem_datatype τ -> (sem_ro_ctx Δ * sem_ro_ctx Γ) -> Prop),
    w1 |- [[fun γδ => (ϕ (tedious_sem_concat _ _ γδ))]] e [[θ]]
          -> w2 ||- [[fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))]] c [[fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)]]
          -> w' ||- [[ϕ]] Newvar e c [[ψ]]

| rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ
                         (ψ : sem_datatype (DUnit) -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop)
                         (w' : Γ ;;; Δ ||- Assign k e: DUnit),
    w |- [[fun δγ => ϕ (tedious_sem_concat _ _ δγ)]] e [[θ]]
         -> (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ))
         -> w' ||- [[ϕ]] Assign k e [[ψ]]

| rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : DBoolean) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ,
    w |- [[rw_to_ro_pre ϕ]] e [[θ]] ->
         w1 ||- [[ro_to_rw_pre (θ true)]] c1 [[ψ]] ->
         w2 ||- [[ro_to_rw_pre (θ false)]] c2 [[ψ]] ->
         w' ||- [[ϕ]] Cond e c1 c2 [[ψ]]

| rw_case_tot : forall Γ Δ e1 e2 c1 c2 τ
                       (wty_e1 : (Δ ++ Γ) |- e1 : DBoolean)
                       (wty_e2 : (Δ ++ Γ) |- e2 : DBoolean)
                       (wty_c1 : Γ ;;; Δ ||- c1 : τ)
                       (wty_c2 : Γ ;;; Δ ||- c2 : τ)
                       (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ)
                       ϕ θ1 θ2 ψ ϕ1 ϕ2,
    wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} -> wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}}
                                                        -> wty_c1 ||- [[ro_to_rw_pre (θ1 true)]] c1 [[ψ]]
                                                        -> wty_c2 ||- [[ro_to_rw_pre (θ2 true)]] c2 [[ψ]]
                                                        -> wty_e1 |- [[ϕ1]] e1 [[b |fun _ => b = true]]
                                                                     -> wty_e2 |- [[ϕ2]] e2 [[b | fun _ => b = true]]
                                                                                  -> (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x))
                                                                                  -> wty ||- [[ϕ]] Case e1 c1 e2 c2 [[ψ]]
                                                                                         
| rw_while_tot : forall Γ Δ e c
                        (wty_e : (Δ ++ Γ) |- e : DBoolean)
                        (wty_c : (Γ ++ Δ) ;;; Δ ||- c : DUnit)
                        (wty : Γ ;;; Δ ||- While e c : DUnit)
                        ϕ θ ψ,
    wty_e |- [[rw_to_ro_pre ϕ]] e [[θ]] ->
             wty_c ||- [[fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_concat (snd δγδ')) /\ fst δγδ' = snd_concat (snd δγδ')]] c [[fun _ δγδ' => ϕ (fst δγδ', fst_concat (snd δγδ')) /\ ψ δγδ' ]] ->
             (
               forall δ γ, ϕ (δ, γ) ->  
                           ~exists f : nat -> sem_ro_ctx Δ,
                               f 0 = δ /\ forall n, ψ (f (S n), (γ ; f n))) ->
                     
             wty ||- [[ϕ]] While e c [[fun _ => (ϕ /\\ ro_to_rw_pre (θ false))]]

                                                                                                       
where
" w |- {{ P }} e {{ Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P Q)) and  " w |- {{ P }} e {{ y | Q }} " := (proves_ro_prt _ e _ w (mk_ro_prt w P (fun y => Q))) and " w |- [[ P ]] e [[ y | Q ]] " := (proves_ro_tot _ e _ w (mk_ro_tot w P (fun y => Q))) and " w ||- {{ P }} e {{ y | Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P (fun y => Q))) and " w ||- [[ P ]] e [[ y | Q ]] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P (fun y => Q))) and " w |- [[ P ]] e [[ Q ]] " := (proves_ro_tot _ e _ w (mk_ro_tot w P Q)) and " w ||- {{ P }} e {{ Q }} " := (proves_rw_prt _ _ e _ w (mk_rw_prt w P Q)) and " w ||- [[ P ]] e [[ Q ]] " := (proves_rw_tot _ _ e _ w (mk_rw_tot w P Q)).


