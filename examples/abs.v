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
           (θ2 := ( fun b x => b = true -> (ro_access _ _ _ w (snd (snd_app x))) <
                                      pow2 (- ((fst (snd_app x))) - 1)%Z))
           
           (ϕ1 := ( fun x =>  (ro_access _ _ _ w (snd (snd_app x))) <
                         pow2 (- ((fst (snd_app x))) - 1)%Z))
           (ϕ2 := ( fun x =>  (ro_access _ _ _ w (snd (snd_app x))) <
                         pow2 (- ((fst (snd_app x))) - 1)%Z))
        ); simpl.
  apply (pp_ro_real_comp_lt_prt
           (Γ := (INTEGER :: Γ))%list
           ((fun y x =>
                     y = (ro_access _ _ _ w (snd x)) ))
           ((fun y x =>
                     y = pow2 (- (fst x) - 1)%Z )))
  .
  apply (pp_ro_var_prt_back (has_type_ro_Var_S _  INTEGER _  k w)).
  intros [x γ] h.
  rewrite ro_access_Var_S.
  apply ro_access_typing_irrl.
  
  
  Search ro_access.
  simpl.
  
  intros a 
  apply (pp_ro_var_prt (has_type_ro_Var_S _  INTEGER _  k w)) . 
  
