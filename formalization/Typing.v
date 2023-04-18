(** Clerical typing judgment rules defined here *)
Require Import Clerical.Syntax.
Require Import List.
Reserved Notation " Γ |- t : T " (at level 50, t, T at next level). 
Reserved Notation " Γ ;;; Δ ||- t : T " (at level 50, Δ, t, T at next level). 

(* A typing context. *)
Definition ro_ctx := list datatype.
Structure rw_ctx := {
  ctx_rw : ro_ctx ;
  ctx_ro : ro_ctx
}.

Definition mk_rw_ctx Γ Δ := {| ctx_ro := Γ ; ctx_rw := Δ|}.

Inductive assignable : ro_ctx -> datatype -> nat -> Type :=
  assignable_0 : forall Δ τ, assignable (τ :: Δ) τ 0
| assignable_S : forall Δ τ σ k, assignable Δ τ k -> assignable (σ :: Δ) τ (S k). 

(* List forall in type level; cf. the Forall in List library is for Prop-level type families *)
Inductive ForallT {A} (P : A -> Type): list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).

Inductive has_type_ro : ro_ctx -> exp -> datatype -> Type :=
(* from readwrite *)
| has_type_ro_rw : forall Γ e τ, Γ ;;; nil ||- e : τ -> Γ |- e : τ 

(* variables *)
| has_type_ro_Var_0 : forall Γ τ,  ((τ :: Γ) |- (VAR 0) : τ)
| has_type_ro_Var_S : forall Γ σ τ k, Γ |- Var k : τ -> (σ :: Γ) |- VAR (S k) : τ

(* constants *)
| has_type_ro_True : forall Γ, Γ |- TRUE : DBoolean
| has_type_ro_False : forall Γ, Γ |- FALSE : DBoolean
| has_type_ro_Skip : forall Γ, Γ |- SKIP : DUnit
| has_type_ro_Int : forall Γ k, Γ |- INT k : DInteger

(* unary ops *)
| has_type_ro_OpRrecip : forall Γ e, Γ |- e : DReal -> Γ |- (UniOp OpRrecip e) : DReal
| has_type_ro_OpZRcoerce : forall Γ e, Γ |- e : DInteger -> Γ |- (UniOp OpZRcoerce e) : DReal
| has_type_ro_OpZRexp : forall Γ e, Γ |- e : DInteger -> Γ |- (UniOp OpZRexp e) : DReal

(* binary ops *)
| has_type_ro_OpZplus : forall Γ e1 e2, Γ |- e1 : DInteger -> Γ |- e2 : DInteger -> Γ |- (BinOp OpZplus e1 e2) : DInteger
| has_type_ro_OpZminus : forall Γ e1 e2, Γ |- e1 : DInteger -> Γ |- e2 : DInteger -> Γ |- (BinOp OpZminus e1 e2) : DInteger
| has_type_ro_OpZmult : forall Γ e1 e2, Γ |- e1 : DInteger -> Γ |- e2 : DInteger -> Γ |- (BinOp OpZmult e1 e2) : DInteger
| has_type_ro_OpZlt : forall Γ e1 e2, Γ |- e1 : DInteger -> Γ |- e2 : DInteger -> Γ |- (BinOp OpZlt e1 e2) : DBoolean
| has_type_ro_OpZeq : forall Γ e1 e2, Γ |- e1 : DInteger -> Γ |- e2 : DInteger -> Γ |- (BinOp OpZeq e1 e2) : DBoolean 
| has_type_ro_OpRplus : forall Γ e1 e2, Γ |- e1 : DReal -> Γ |- e2 : DReal -> Γ |- (BinOp OpRplus e1 e2) : DReal
| has_type_ro_OpRminus : forall Γ e1 e2, Γ |- e1 : DReal -> Γ |- e2 : DReal -> Γ |- (BinOp OpRminus e1 e2) : DReal
| has_type_ro_OpRmult : forall Γ e1 e2, Γ |- e1 : DReal -> Γ |- e2 : DReal -> Γ |- (BinOp OpRmult e1 e2) : DReal
| has_type_ro_OpRlt : forall Γ e1 e2, Γ |- e1 : DReal -> Γ |- e2 : DReal -> Γ |- (BinOp OpRlt e1 e2) : DBoolean

(* limit *)
| has_type_ro_Lim : forall Γ e, (DInteger :: Γ) |- e : DReal -> Γ |- Lim e : DReal
                                                                                                         
with has_type_rw : rw_ctx -> exp -> datatype -> Type :=
(* from readonly *)
| has_type_rw_ro : forall Γ Δ e τ, (Δ ++ Γ) |- e : τ -> Γ ;;; Δ ||- e : τ

(* sequential *)
| has_type_rw_Seq : forall Γ Δ c1 c2 τ, Γ ;;; Δ ||- c1 : DUnit -> Γ;;; Δ ||- c2 : τ -> Γ ;;; Δ ||- (Seq c1 c2) : τ 
                                                                        
(* assignment *)
| has_type_rw_Assign : forall Γ Δ e τ k, assignable Δ τ k -> (Δ ++ Γ) |- e : τ -> Γ ;;; Δ ||- Assign k e : DUnit

(* newvar *)
| has_type_rw_Newvar : forall Γ Δ e c σ τ, (Δ ++ Γ) |- e : σ -> Γ ;;; σ :: Δ ||- c : τ -> Γ ;;; Δ ||- Newvar e c : τ

(* cond *)
| has_type_rw_Cond : forall Γ Δ e c1 c2 τ, (Δ ++ Γ) |- e : DBoolean -> Γ ;;; Δ ||- c1 : τ -> Γ ;;; Δ ||- c2 : τ -> Γ ;;; Δ ||- Cond e c1 c2 : τ

(* case *)
| has_type_rw_Case : forall Γ Δ e1 c1 e2 c2 τ, (Δ ++ Γ) |- e1 : DBoolean -> Γ ;;; Δ ||- c1 : τ -> (Δ ++ Γ) |- e2 : DBoolean -> Γ ;;; Δ ||- c2 : τ -> Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ

(* case list *)
| has_type_rw_CaseList : forall Γ Δ l τ,
    (1 <= length l)%nat -> 
    ForallT (fun ec => ((Δ ++ Γ) |- fst ec : DBoolean) * (Γ ;;; Δ ||- snd ec : τ))%type l ->
    Γ ;;; Δ ||- CaseList l : τ
                               
(* while *)
| has_type_rw_While : forall Γ Δ e c, (Δ ++ Γ) |- e : DBoolean -> Γ ;;; Δ ||- c : DUnit -> Γ ;;; Δ ||- While e c : DUnit
                                                                                                                                                                 
                                                                                                             
where " Γ |- c : τ " := (has_type_ro Γ c τ) and " Γ ;;; Δ ||- c : τ " := (has_type_rw (mk_rw_ctx Γ Δ) c τ).
