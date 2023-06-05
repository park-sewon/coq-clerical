From Clerical Require Import Clerical.

Definition clerical_neg e :=  
  IF e THEN FALSE ELSE TRUE END.

Lemma clerical_neg_correct_tot :
  forall Γ e ϕ ψ,
    Γ |-- [{ϕ}] e [{y : BOOL | ψ (negb y)}] ->
    Γ |-- [{ϕ}] clerical_neg e [{y : BOOL | ψ y}].
Proof.
  intros.

  apply (pp_ro_rw_tot_back).

  apply (pp_rw_cond_tot
           (θ :=
              (fun y x => ψ (negb y) (snd_app x))) ). 
  (* condition on the condition *)
  exact X.
  (* condition on the first branch *)
  proves_simple_arithmetical.
  rewrite val.
  exact pre.
  (* condition on the second branch *)
  proves_simple_arithmetical.
  rewrite val.
  exact pre.
Defined.

Lemma clerical_neg_correct_prt :
  forall Γ e ϕ ψ,
    Γ |-- {{ϕ}} e {{y : BOOL | ψ (negb y)}} ->
    Γ |-- {{ϕ}} clerical_neg e {{y : BOOL | ψ y}}.
Proof.
  intros.

  apply (pp_ro_rw_prt_back).

  apply (pp_rw_cond_prt
           (θ :=
              (fun y x => ψ (negb y) (snd_app x))) ). 
  (* condition on the condition *)
  exact X.
  (* condition on the first branch *)
  proves_simple_arithmetical.
  rewrite val.
  exact pre.
  (* condition on the second branch *)
  proves_simple_arithmetical.
  rewrite val.
  exact pre.
Defined.

  
