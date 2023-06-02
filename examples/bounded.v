From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

From Examples Require Import abs.

(* computing the absolute value of variable k *)
Definition clerical_bounded k δ :=  
  CASE
    clerical_abs k  ;<; (VAR δ)  
    ==> TRUE
    OR
    (VAR δ) ;*; EXP (INT -1) ;<; clerical_abs k
    ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) 
    ==> FALSE
  END.

Lemma clerical_abs_correct :
  forall Γ k δ (wk : Γ |- VAR k : REAL) (wδ : Γ |- VAR δ : REAL),
    Γ |--
      [{fun x => 0 < (ro_access Γ δ REAL wδ x)}]
      clerical_bounded k δ 
      [{y : BOOL | fun x =>
                     (y = true -> Rabs (ro_access Γ k REAL wk x) < (ro_access Γ δ REAL wδ x)) /\
                       (y = false -> Rabs (ro_access Γ k REAL wk x) < (ro_access Γ δ REAL wδ x))    
        }].
Proof.
  intros.
  apply (pp_ro_rw_tot_back).
  apply (pp_rw_case_tot
           (θ1 := (fun b x => b = true ->
                              Rabs (ro_access _ _ _ wk (snd_app x)) <
                                (ro_access _ _ _ wδ (snd_app x))))
           (θ2 := (fun b x => b = true ->
                              (ro_access _ _ _ wδ (snd_app x)) / 2 < 
                                Rabs (ro_access _ _ _ wk (snd_app x))))           
           (ϕ1 := (fun x => 
                      Rabs (ro_access _ _ _ wk (snd_app x)) <
                        (ro_access _ _ _ wδ (snd_app x))))
           (ϕ2 := (fun x => 
                     (ro_access _ _ _ wδ (snd_app x)) / 2 < 
                       Rabs (ro_access _ _ _ wk (snd_app x))))); simpl.

  
  apply pp_ro_real_comp_lt_prt.

  proves_simple_arithmetical.


  intro e.
  rewrite e in val.
  apply eq_sym in val.
  apply (proj1 (Rltb''_prop _ _)) in val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S, ro_access_Var_0 in val.

