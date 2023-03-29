Require Import Typing.
Require Import Specification.


Reserved Notation " w |- { P } e { y : T | Q }t " (at level 50, P, e, y, T, Q at next level).
Reserved Notation " w |- { P } e { y : T | Q }p " (at level 50, P, e, y, T, Q at next level).

Reserved Notation " w ||- { P } e { y : T | Q }t " (at level 50, P, e, y, T, Q at next level).
Reserved Notation " w ||- { P } e { y : T | Q }p " (at level 50, P, e, y, T, Q at next level).

Inductive proves_ro_prt : forall Γ e τ (w : Γ |- e : τ), ro_prt w -> Type :=

with proves_ro_tot : forall Γ e τ (w : Γ |- e : τ), ro_tot w -> Type :=

with proves_rw_prt : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_prt w -> Type :=

with proves_rw_tot : forall Γ Δ c τ (w : Γ ;;; Δ ||- c : τ), rw_tot w -> Type :=

where
" w |- { P } e { y : τ | Q }p " := (proves_ro_prt _ e τ w ) and
" w |- { P } e { y : τ | Q }t " := (proves_ro_tot Γ e τ) and
" w ||- { P } e { y : τ | Q }o " := (proves_rw_prt Γ Δ e τ) and
" w ||- { P } e { y : τ | Q }t " := (proves_ro_prt Γ Δ e τ)


                                                         " Γ ;;; Δ ||- c : τ " := (has_type_rw (mk_rw_ctx Γ Δ) c τ).

. 
      
