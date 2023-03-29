Require Import Clerical.
Require Import Semantics.
Require Import Nondeterminism.
Require Import Typing.

Structure ro_prt {Γ : ro_ctx} {e : comp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_prt_pre : sem_ro_ctx Γ -> Prop ;
    ro_prt_post : sem_ro_ctx Γ * sem_datatype τ -> Prop
  }.

Structure ro_tot {Γ : ro_ctx} {e : comp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_tot_pre : sem_ro_ctx Γ -> Prop ;
    ro_tot_post : sem_ro_ctx Γ * sem_datatype τ -> Prop
  }.

Structure rw_prt {Γ Δ: ro_ctx} {c : comp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_prt_pre : sem_ro_ctx Γ -> sem_ro_ctx Δ -> Prop ;
    rw_prt_post : sem_ro_ctx Γ * (sem_ro_ctx Δ * sem_datatype τ) -> Prop
  }.

Structure rw_tot {Γ Δ : ro_ctx} {c : comp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_tot_pre : sem_ro_ctx Γ -> sem_ro_ctx Δ -> Prop ;
    rw_tot_post : sem_ro_ctx Γ * (sem_ro_ctx Δ * sem_datatype τ) -> Prop
  }.

Definition sem_ro_prt {Γ} {e} {τ} {wty} (t : ro_prt wty) :=
  let P := ro_prt_pre _ t in
  let Q := ro_prt_post _ t in
  forall γ, P γ ->
            let V := sem_ro_comp Γ e τ wty γ in
            pdom_nempty V /\ forall v, pdom_char V v -> forall v', v = total v' -> Q (γ, v').


Definition sem_ro_tot {Γ} {e} {τ} {wty} (t : ro_tot wty) :=
  let P := ro_tot_pre _ t in
  let Q := ro_tot_post _ t in
  forall γ, P γ ->
            let V := sem_ro_comp Γ e τ wty γ in
            pdom_nempty V /\ forall v, pdom_char V v -> exists v', v = total v' /\ Q (γ, v').


Definition sem_rw_prt {Γ Δ} {c} {τ} {wty} (t : rw_prt wty) :=
  let P := rw_prt_pre _ t in
  let Q := rw_prt_post _ t in
  forall γ δ, P γ δ ->
            let V := sem_rw_comp Γ Δ c τ wty γ δ in
            pdom_nempty V /\ forall v, pdom_char V (total v) -> Q (γ, v).

Definition sem_rw_tot {Γ Δ} {c} {τ} {wty} (t : rw_tot wty) :=
  let P := rw_tot_pre _ t in
  let Q := rw_tot_post _ t in
  forall γ δ, P γ δ ->
            let V := sem_rw_comp Γ Δ c τ wty γ δ in
            pdom_nempty V /\ exists v, pdom_char V (total v) /\ Q (γ, v).

