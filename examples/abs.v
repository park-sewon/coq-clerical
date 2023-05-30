(* From Clerical Require Import Clerical. *)



From Clerical Require Import Clerical.
Require Import ZArith.


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
  apply has_type_ro_Lim.
  apply has_type_ro_rw.
  apply has_type_rw_Case.
  simpl.
  apply has_type_ro_OpRlt.
  apply has_type_ro_Var_S.
  exact H.
  apply has_type_ro_OpZRexp.
  apply has_type_ro_OpZminus.
  apply has_type_ro_OpZminus.
  apply has_type_ro_Int.
  apply has_type_ro_Var_0.
  apply has_type_ro_Int.
  apply has_type_rw_ro.
  apply has_type_ro_OpRminus.
  apply has_type_ro_OpZRcoerce.
  apply has_type_ro_Int.
  apply has_type_ro_Var_S.
  exact H.

  apply has_type_ro_OpRlt.
  apply has_type_ro_OpRminus.
  apply has_type_ro_OpZRcoerce.
  apply has_type_ro_Int.
  apply has_type_ro_OpZRexp.
  apply has_type_ro_OpZminus.
  apply has_type_ro_OpZminus.
  apply has_type_ro_Int.
  apply has_type_ro_Var_0.
  apply has_type_ro_Int.
  apply has_type_ro_Var_S.
  exact H.

  apply has_type_rw_ro.
  apply has_type_ro_Var_S.
  exact H.
Defined.

Require Import Reals.
Open Scope R.



Lemma exp_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    (exp_abs_wty Γ k w) |-
      [{fun _ => True}]
        exp_abs k 
        [{y | fun x => y = Rabs (ro_access Γ k REAL w x) }].
Proof.
  intros.
  Close Scope detail_scope.
  apply (ro_lim_tot_util (fun x =>  Rabs (ro_access Γ k REAL w x)));
    try (intros h1 h2 [_ h3]; auto; fail).
  apply (ro_rw_tot_util).
  
  
  Check rw_ro_tot.
