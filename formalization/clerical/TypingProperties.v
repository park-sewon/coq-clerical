Require Import Clerical.
Require Import Typing.

Lemma has_type_ro_unambiguous : forall Γ e τ σ, Γ |- e : τ -> Γ |- e : σ -> τ = σ
with has_type_rw_unambiguous : forall Γ Δ e τ σ, Γ ;;; Δ ||- e : τ -> Γ ;;; Δ ||- e : σ -> τ = σ.
Admitted.


Fixpoint ro_assign_absurd Γ k e (w : Γ |- Assign k e : DUnit) : False.
Proof.
  inversion w.
  inversion H.
  simpl in H7.
  apply (ro_assign_absurd Γ k e H7) .
  contradict H6.
  intro.
  inversion H6.
Defined.


