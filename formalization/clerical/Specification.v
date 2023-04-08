Require Import Clerical.
Require Import Semantics.
Require Import Powerdomain.
Require Import Typing.

Structure ro_prt {Γ : ro_ctx} {e : comp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_prt_pre : sem_ro_ctx Γ -> Prop ;
    ro_prt_post : sem_datatype τ -> sem_ro_ctx Γ -> Prop
  }.

Structure ro_tot {Γ : ro_ctx} {e : comp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_tot_pre : sem_ro_ctx Γ -> Prop ;
    ro_tot_post : sem_datatype τ-> sem_ro_ctx Γ ->  Prop
  }.

Structure rw_prt {Γ Δ: ro_ctx} {c : comp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_prt_pre :  sem_ro_ctx Δ  * sem_ro_ctx Γ -> Prop ;
    rw_prt_post : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ ->  Prop
  }.

Structure rw_tot {Γ Δ : ro_ctx} {c : comp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_tot_pre : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop ;
    rw_tot_post :  sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop
  }.

Definition sem_ro_prt {Γ} {e} {τ} {wty} (t : ro_prt wty) :=
  let P := ro_prt_pre _ t in
  let Q := ro_prt_post _ t in
  forall γ, P γ ->
            let V := sem_ro_comp Γ e τ wty γ in
            pdom_neg_is_empty V /\ forall v, v ∈ V -> forall v', v = total v' -> Q v' γ.

Definition sem_ro_tot {Γ} {e} {τ} {wty} (t : ro_tot wty) :=
  let P := ro_tot_pre _ t in
  let Q := ro_tot_post _ t in
  forall γ, P γ ->
            let V := sem_ro_comp Γ e τ wty γ in
            pdom_neg_is_empty    V /\ forall v, v ∈ V -> exists v', v = total v' /\ Q v' γ.


(* Definition sem_rw_prt {Γ Δ} {c} {τ} {wty} (t : rw_prt wty) := *)
(*   let P := rw_prt_pre _ t in *)
(*   let Q := rw_prt_post _ t in *)
(*   forall γ δ, P (δ, γ) -> *)
(*             let V := sem_rw_comp Γ Δ c τ wty γ δ in *)
(*             pdom_neg_is_empty V /\ forall v, (total v) ∈ V -> Q (snd v) (fst v, γ). *)

Definition sem_rw_prt {Γ Δ} {c} {τ} {wty} (t : rw_prt wty) :=
  let P := rw_prt_pre _ t in
  let Q := rw_prt_post _ t in
  forall γ δ, P (δ, γ) ->
            let V := sem_rw_comp Γ Δ c τ wty γ δ in
            pdom_neg_is_empty V /\ forall v, v ∈ V -> forall v', v = total v' -> Q (snd v') (fst v', γ).

Definition sem_rw_tot {Γ Δ} {c} {τ} {wty} (t : rw_tot wty) :=
  let P := rw_tot_pre _ t in
  let Q := rw_tot_post _ t in
  forall γ δ, P (δ, γ) ->
              let V := sem_rw_comp Γ Δ c τ wty γ δ in
              pdom_neg_is_empty V /\ forall v, v ∈ V -> exists v', v = total v' /\ Q (snd v') (fst v', γ).

Definition mk_ro_prt {Γ} {e} {τ} (w : Γ |- e : τ) P Q : ro_prt w
  := {| ro_prt_pre := P ; ro_prt_post := Q |}.

Definition mk_ro_tot {Γ} {e} {τ} (w : Γ |- e : τ) P Q : ro_tot w
  := {| ro_tot_pre := P ; ro_tot_post := Q |}.

Definition mk_rw_prt {Γ Δ} {e} {τ} (w : Γ ;;; Δ ||- e : τ) P Q : rw_prt w
  := {| rw_prt_pre := P ; rw_prt_post := Q |}.

Definition mk_rw_tot {Γ Δ} {e} {τ} (w : Γ ;;; Δ ||- e : τ) P Q : rw_tot w
  := {| rw_tot_pre := P ; rw_tot_post := Q |}.


Notation " w |= {{ ϕ }} e {{ ψ }} ":= (sem_ro_prt (@mk_ro_prt _ e _ w ϕ ψ)) (at level 85).
Notation " w |= [{ ϕ }] e [{ ψ }] ":= (sem_ro_tot (@mk_ro_tot _ e _ w ϕ ψ)) (at level 85).
Notation " w ||= {{ ϕ }} e {{ ψ }} ":= (sem_rw_prt (@mk_rw_prt _ _ e _ w ϕ ψ)) (at level 85).
Notation " w ||= [{ ϕ }] e [{ ψ }] ":= (sem_rw_tot (@mk_rw_tot _ _ e _ w ϕ ψ)) (at level 85).
