From Clerical Require Import Clerical.

Definition clerical_neg e :=  
  IF e THEN FALSE ELSE TRUE END.

Lemma clerical_neg_correct_tot :
  forall Γ e ϕ ψ,
    [x : Γ] |- {{ϕ x}} e {{y : BOOL | ψ x y}}ᵗ ->
    [x : Γ] |- {{ϕ x}} clerical_neg e {{y : BOOL | ψ x (negb y)}}ᵗ.
Proof.
  intros.

  apply (pp_ro_rw_tot_back).

  apply (pp_rw_cond_tot
           (θ :=
              (fun x y => ψ (snd_app x) y)) ). 
  (* clondition on the condition *)
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


Lemma clerical_neg_correct_tot_back :
  forall Γ e ϕ ψ,
    [x : Γ] |- {{ϕ x}} e {{y : BOOL | ψ x (negb y)}}ᵗ ->
    [x : Γ] |- {{ϕ x}} clerical_neg e {{y : BOOL | ψ x y}}ᵗ.
Proof.
  intros.

  apply (pp_ro_rw_tot_back).

  apply (pp_rw_cond_tot
           (θ :=
              (fun x y => ψ (snd_app x) (negb y)))). 
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
    [x : Γ] |- {{ϕ x}} e {{y : BOOL | ψ x y}}ᵖ ->
    [x : Γ] |- {{ϕ x}} clerical_neg e {{y : BOOL | ψ x (negb y)}}ᵖ.
Proof.
  intros.

  apply (pp_ro_rw_prt_back).

  apply (pp_rw_cond_prt
           (θ :=
              (fun x y => ψ (snd_app x) y)) ). 
  (* clondition on the condition *)
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


Lemma clerical_neg_correct_prt_back :
  forall Γ e ϕ ψ,
    [x : Γ] |- {{ϕ x}} e {{y : BOOL | ψ x (negb y)}}ᵖ ->
    [x : Γ] |- {{ϕ x}} clerical_neg e {{y : BOOL | ψ x y}}ᵖ.
Proof.
  intros.

  apply (pp_ro_rw_prt_back).

  apply (pp_rw_cond_prt
           (θ :=
              (fun x y => ψ (snd_app x) (negb y)))). 
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
