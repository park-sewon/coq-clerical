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
Require Import Clerical.ReasoningAdmissibleRes0.


Fixpoint r_proves_ro_prt_proves_ro_prt {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} (p : w |~ {{ϕ}} e {{ψ}}) {struct p} : w |- {{ϕ}} e {{ψ}}
with r_proves_ro_tot_proves_ro_tot {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} (p : w |~ [{ϕ}] e [{ψ}]) {struct p} : w |- [{ϕ}] e [{ψ}]
with r_proves_rw_prt_proves_rw_prt {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} {ϕ} {ψ} (p : w ||~ {{ϕ}} e {{ψ}}) {struct p} : w ||- {{ϕ}} e {{ψ}}
with r_proves_rw_tot_proves_rw_tot {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} {ϕ} {ψ} (p : w ||~ [{ϕ}] e [{ψ}]) {struct p} : w ||- [{ϕ}] e [{ψ}].
Proof.
  +
    
    dependent induction p; try (constructor; fail); try (apply r_proves_ro_prt_proves_ro_prt in p); try (apply r_proves_ro_prt_proves_ro_prt in p1, p2).

    apply (fun k => ro_imply_prt _ _ _ _ _ _ _ _ _ k p); auto.

    apply r_proves_rw_prt_proves_rw_prt in r.
    apply (rw_ro_prt _ _ _ w _ _ _ r).

    apply (ro_coerce_prt _ _ w).
    exact p.

    apply (ro_exp_prt _ _ w).
    exact p.

    apply (ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_recip_prt _ _ w _ _ _ _ p).
    exact a.

    apply (ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (ro_lim_prt _ _ w _ _ _ _ r).
    exact e0.

  +

    dependent induction p; try (constructor; fail); try (apply r_proves_ro_tot_proves_ro_tot in p); try (apply r_proves_ro_tot_proves_ro_tot in p1, p2).

    apply (fun k => ro_imply_tot _ _ _ _ _ _ _ _ _ k p); auto.

    apply r_proves_rw_tot_proves_rw_tot in r.
    apply (rw_ro_tot _ _ _ w _ _ _ r).

    apply (ro_coerce_tot _ _ w).
    exact p.

    apply (ro_exp_tot _ _ w).
    exact p.

    apply (ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_recip_tot _ _ w _ _ _ _ p).
    exact a.

    apply (ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact ψ0.

    apply (ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2).
    exact a.

    apply (ro_lim_tot _ _ w _ _ _ _ p).
    exact e0.
    
  +
    dependent induction p; try (constructor; fail); try (apply r_proves_rw_prt_proves_rw_prt in p); try (apply r_proves_rw_prt_proves_rw_prt in p1, p2).
    
    apply (fun k => rw_imply_prt _ _ _ _ _ _ _ _ _ _ k p); auto.

    apply r_proves_ro_prt_proves_ro_prt in r.
    apply (ro_rw_prt _ _ _ _ w _ _ _ r).
    
    apply (rw_sequence_prt _ _ _ _ _ w1 w2 _ _ _ _ p1 p2).

    apply r_proves_ro_prt_proves_ro_prt in r.
    apply (rw_new_var_prt _ _ _ _ _ _ w1 w2 _ _ _ _ r p).

    apply r_proves_ro_prt_proves_ro_prt in r.
    apply (rw_assign_prt _ _ _ _ _ w _ _ _ _ r ψ0).

    apply r_proves_ro_prt_proves_ro_prt in r.
    apply (rw_cond_prt _ _ _ _ _ _ w w1 w2 _ _ _ _ r p1 p2).

    apply r_proves_ro_prt_proves_ro_prt in r, r0.
    apply (rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r r0 p1 p2).

    apply (rw_case_list_prt _ _ l τ wty_l wty θ ϕ ψ).
    clear wty.
    dependent induction f.
    
    apply ForallT2_nil.
    apply ForallT2_cons.
    apply IHf.
    destruct r.
    split.
    apply r_proves_ro_prt_proves_ro_prt in r.
    exact r.
    apply r_proves_rw_prt_proves_rw_prt in r0.
    exact r0.

    apply r_proves_ro_prt_proves_ro_prt in r.
    apply (rw_while_prt _ _ _ _ _ _ _ _ _ r p).


  +
    dependent induction p; try (constructor; fail); try (apply r_proves_rw_tot_proves_rw_tot in p); try (apply r_proves_rw_tot_proves_rw_tot in p1, p2).
    
    apply (fun k => rw_imply_tot _ _ _ _ _ _ _ _ _ _ k p); auto.

    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (ro_rw_tot _ _ _ _ w _ _ _ r).
    
    apply (rw_sequence_tot _ _ _ _ _ w1 w2 _ _ _ _ p1 p2).

    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (rw_new_var_tot _ _ _ _ _ _ w1 w2 _ _ _ _ r p).

    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (rw_assign_tot _ _ _ _ _ w _ _ _ _ r ψ0).

    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (rw_cond_tot _ _ _ _ _ _ w w1 w2 _ _ _ _ r p1 p2).

    apply r_proves_ro_prt_proves_ro_prt in r, r0.
    apply r_proves_ro_tot_proves_ro_tot in r1, r2.
    apply (rw_case_tot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r r0 p1 p2 r1 r2 o).
    apply (rw_case_list_tot _ _ l τ wty_l wty θ ϕi ϕ ψ).
    clear wty f0.
    dependent induction f.
    
    apply ForallT3_nil.
    apply ForallT3_cons.
    apply IHf.
    destruct j as [[j1 j2] j3].
    repeat split.
    apply r_proves_ro_prt_proves_ro_prt in j1.
    exact j1.
    apply r_proves_rw_tot_proves_rw_tot in j2.
    exact j2.
    apply r_proves_ro_tot_proves_ro_tot in j3.
    exact j3.
    exact f0.
    
    apply r_proves_ro_tot_proves_ro_tot in r.
    apply (rw_while_tot _ _ _ _ _ _ _ _ _ _ r p).
    exact n.
Defined.

