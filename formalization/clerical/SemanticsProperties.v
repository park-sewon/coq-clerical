Require Import List.

Require Import Clerical.
Require Import Typing.
Require Import TypingProperties.
Require Import Powerdomain.
Require Import Semantics.
Require Import Reals.



(* semantics is unique *)
Lemma sem_ro_comp_unique : forall Γ e τ (w1 w2 : Γ |- e : τ), sem_ro_comp Γ e τ w1 = sem_ro_comp Γ e τ w2
with sem_rw_comp_unique : forall Γ Δ e τ (w1 w2 : Γ ;;; Δ ||- e : τ), sem_rw_comp Γ Δ e τ w1 = sem_rw_comp Γ Δ e τ w2.
Proof.
  Admitted.
  
Lemma sem_ro_comp_auxiliary_ctx : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) γ γ', sem_ro_comp Γ e τ w γ = sem_ro_comp (Γ ++ Γ') e τ w' (γ; γ')
with sem_rw_comp_auxiliary_ctx : forall Γ Γ' Δ e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) γ γ' δ, sem_rw_comp Γ Δ e τ w γ δ = sem_rw_comp (Γ ++ Γ') Δ e τ w' (γ ; γ') δ.
Proof.
Admitted.
  
