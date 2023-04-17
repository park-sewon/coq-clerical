Require Import List.
Require Import Clerical.
Require Import Typing.
Require Import TypingProperties.
Require Import Semantics.
Require Import Specification.
Require Import ReasoningRules.
Arguments existT {_} {_}.
Require Import Coq.Program.Equality.
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
                                                ro_to_rw_pre (θ true) (fst δγδ', fst_concat (snd δγδ')) /\ fst δγδ' = snd_concat (snd δγδ'))
                                               (fst δγ, (snd δγ; γ')))).
      {
        simpl.
        intros δγ h.
        exists (fst δγ); auto.
        unfold snd_concat.
        unfold fst_concat.
        rewrite tedious_equiv_1.
        destruct δγ; split; auto.
      }
      assert ((fun y => (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ =>
                        exists γ' : sem_ro_ctx Δ,
                          (fun (_ : sem_datatype UNIT) (δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ)) =>
                             ϕ (fst δγδ', fst_concat (snd δγδ')) /\ ψ0 δγδ') y (fst δγ, (snd δγ; γ')))) ->>>
                                                                                                       fun _ => ϕ).

      {
        simpl.
        intros _ δγ [γ' [h1 h2]].
        unfold fst_concat in h1.
        rewrite tedious_equiv_1 in h1.
        destruct δγ; auto.
      }
      exact (rw_imply_prt _ _ _ _ _ _ _ _ _ H0 X0 H1).
    }
    
Defined.


