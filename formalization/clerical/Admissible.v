Require Import Clerical.
Require Import Typing.
Require Import Semantics.
Require Import Specification.
Require Import Reasoning.
Arguments existT {_} {_}.
Require Import Coq.Program.Equality.

(* rw_while_tot *)
(*      : forall (Γ Δ : list datatype) (e c : comp) (wty_e : (Δ ++ Γ)%list |- e : BOOL) *)
(*          (wty_c : (Γ ++ Δ);;; Δ ||- c : UNIT) (wty : Γ;;; Δ ||- (WHILE e DO c END) : UNIT) *)
(*          (ϕ : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop) (θ : sem_datatype BOOL -> sem_ro_ctx (Δ ++ Γ) -> Prop) *)
(*          (ψ : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) -> Prop), *)
(*        wty_e |- [{rw_to_ro_pre ϕ}] e [{y | θ y}] -> *)
(*        wty_c *)
(*        ||- [{(fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => *)
(*               ro_to_rw_pre (θ true) (fst δγδ', fst_concat (snd δγδ')) /\ fst δγδ' = snd_concat (snd δγδ'))}] c [{_ *)
(*        | (fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => ϕ (fst δγδ', fst_concat (snd δγδ')) /\ ψ δγδ')}] -> *)
(*        (forall (δ : sem_ro_ctx Δ) (γ : sem_ro_ctx Γ), *)
(*         ϕ (δ, γ) -> ~ (exists f : nat -> sem_ro_ctx Δ, f 0 = δ /\ (forall n : nat, ψ (f (S n), (γ; f n))))) -> *)
(*        wty ||- [{ϕ}] (WHILE e DO c END) [{_ | (ϕ /\\ ro_to_rw_pre (θ false))}] *)

           
Lemma proves_admissible_ro_prt_remove_copy :
  forall Γ Δ' Δ e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Δ') ;;; Δ ||- e : τ) ϕ ψ,
    w' ||- {{ϕ}} e {{ψ}} -> w ||- {{fun δγ => exists δ', ϕ (fst δγ, (snd δγ ; δ'))}} e {{fun y δγ => exists δ', ψ y (fst δγ, (snd δγ ; δ')) }}.
Proof.
  intros.
  induction Δ'.
  simpl.
Admitted.

  


Lemma proves_admissible_ro_tot_prt : forall Γ e τ (w : Γ |- e : τ) ϕ ψ,
    w |- [{ϕ}] e [{ψ}] -> w |- {{ϕ}} e {{ψ}}
with proves_admissible_rw_tot_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ,
    w ||- [{ϕ}] e [{ψ}] -> w ||- {{ϕ}} e {{ψ}}.
Proof.
  +
    intros.
    dependent destruction X.
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
    apply (ro_coerce_prt _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_exp_prt _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    assert (sc:  (θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> Rdefinitions.IZR BinNums.Z0)) ->>>
                                                                                                               (fun x : sem_datatype REAL => ψ (Rdefinitions.RinvImpl.Rinv x))).
    {
      intros γ δ [m1 m2].
      apply a; auto.
    }
    apply (ro_recip_prt _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X) sc).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ3).

    assert (sc : (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ),
                     ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ)).
    {
      intros; apply a; auto.
    }
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ X1) (proves_admissible_ro_tot_prt _ _ _ _ _ _ X2) sc).

    apply (ro_lim_prt _ _ _ _ _ _ _ X e0).

  +
    intros.
    dependent destruction X.
    apply (rw_imply_prt _ _ _ _ _ _ _ _ _ a (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X) a0).
    apply rw_exfalso_prt.
    apply (rw_conj_prt _ _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_disj_prt _ _ _ _ _ _ _ _ (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (ro_rw_prt _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p)).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _  (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X)).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) ψ1).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ (proves_admissible_ro_tot_prt _ _ _ _ _ _ p) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p p0 (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (proves_admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).

Admitted.
