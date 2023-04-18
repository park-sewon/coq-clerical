Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.


Structure ro_prt {Γ : ro_ctx} {e : exp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_prt_pre : sem_ro_ctx Γ -> Prop ;
    ro_prt_post : sem_datatype τ -> sem_ro_ctx Γ -> Prop
  }.

Structure ro_tot {Γ : ro_ctx} {e : exp} {τ : datatype} (wty : Γ |- e : τ) :=
  {
    ro_tot_pre : sem_ro_ctx Γ -> Prop ;
    ro_tot_post : sem_datatype τ-> sem_ro_ctx Γ ->  Prop
  }.

Structure rw_prt {Γ Δ: ro_ctx} {c : exp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_prt_pre :  sem_ro_ctx Δ  * sem_ro_ctx Γ -> Prop ;
    rw_prt_post : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ ->  Prop
  }.

Structure rw_tot {Γ Δ : ro_ctx} {c : exp} {τ : datatype} (wty : Γ ;;; Δ ||- c : τ) :=
  {
    rw_tot_pre : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop ;
    rw_tot_post :  sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop
  }.

Definition sem_ro_prt {Γ} {e} {τ} {wty} (t : ro_prt wty) :=
  let P := ro_prt_pre _ t in
  let Q := ro_prt_post _ t in
  forall γ, P γ ->
            let V := sem_ro_exp Γ e τ wty γ in
            pdom_neg_is_empty V /\ forall v, v ∈ V -> forall v', v = total v' -> Q v' γ.

Definition sem_ro_tot {Γ} {e} {τ} {wty} (t : ro_tot wty) :=
  let P := ro_tot_pre _ t in
  let Q := ro_tot_post _ t in
  forall γ, P γ ->
            let V := sem_ro_exp Γ e τ wty γ in
            pdom_neg_is_empty    V /\ forall v, v ∈ V -> exists v', v = total v' /\ Q v' γ.


(* Definition sem_rw_prt {Γ Δ} {c} {τ} {wty} (t : rw_prt wty) := *)
(*   let P := rw_prt_pre _ t in *)
(*   let Q := rw_prt_post _ t in *)
(*   forall γ δ, P (δ, γ) -> *)
(*             let V := sem_rw_exp Γ Δ c τ wty γ δ in *)
(*             pdom_neg_is_empty V /\ forall v, (total v) ∈ V -> Q (snd v) (fst v, γ). *)

Definition sem_rw_prt {Γ Δ} {c} {τ} {wty} (t : rw_prt wty) :=
  let P := rw_prt_pre _ t in
  let Q := rw_prt_post _ t in
  forall γ δ, P (δ, γ) ->
            let V := sem_rw_exp Γ Δ c τ wty γ δ in
            pdom_neg_is_empty V /\ forall v, v ∈ V -> forall v', v = total v' -> Q (snd v') (fst v', γ).

Definition sem_rw_tot {Γ Δ} {c} {τ} {wty} (t : rw_tot wty) :=
  let P := rw_tot_pre _ t in
  let Q := rw_tot_post _ t in
  forall γ δ, P (δ, γ) ->
              let V := sem_rw_exp Γ Δ c τ wty γ δ in
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

(* Now let us prove some properties *)

Lemma sem_ro_prt_excludes_bot_is_tot : forall Γ e τ ϕ ψ (w : Γ |- e : τ), 
    w |= {{ϕ}} e {{ψ}} -> 
    (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ w γ) ->
    w |= [{ϕ}] e [{ψ}].
Proof.
  intros Γ e τ ϕ ψ w h1 h2 γ m; simpl; simpl in m.
  destruct (h1 γ m) as [h3 h4]; split; auto.
  intros v m'.
  destruct v.
  contradict (h2 _ m m').
  exists s; split; auto.
  apply (h4 _ m' _ eq_refl).
Qed.

Lemma sem_rw_prt_excludes_bot_is_tot : forall Γ Δ e τ ϕ ψ (w : Γ ;;; Δ ||- e : τ), 
    w ||= {{ϕ}} e {{ψ}} -> 
    (forall γ δ, ϕ (δ, γ) -> ⊥ ∉ sem_rw_exp _ _ _ _ w γ δ) ->
    w ||= [{ϕ}] e [{ψ}].
Proof.
  intros Γ Δ e τ ϕ ψ w h1 h2 γ δ m; simpl; simpl in m.
  destruct (h1 γ δ m) as [h3 h4]; split; auto.
  intros v m'.
  destruct v.
  contradict (h2 _ _ m m').
  exists p; split; auto.
  apply (h4 _ m' _ eq_refl).
Qed.

Lemma sem_ro_tot_is_prt_excludes_bot : forall Γ e τ ϕ ψ (w : Γ |- e : τ), 
    w |= [{ϕ}] e [{ψ}] ->
    w |= {{ϕ}} e {{ψ}} /\ 
    (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ w γ).
Proof.
  intros Γ e τ ϕ ψ w h1.
  split.
  intros γ m; simpl; simpl in m.
  destruct (h1 γ m) as [h3 h4]; split; auto.
  intros.
  pose proof (h4 v H).
  destruct H1.
  destruct H1.
  rewrite H0 in H1.
  apply total_is_injective in H1.
  rewrite H1; auto.
  intros.
  destruct (h1 γ H) as [_ h4].
  intro h.
  pose proof (h4 ⊥ h) as [j [i _]].
  contradict (flat_bot_neq_total _ i).
Qed.

Lemma sem_ro_tot_excludes_bot : forall Γ e τ ϕ ψ (w : Γ |- e : τ), 
    w |= [{ϕ}] e [{ψ}] ->
    (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ w γ).
Proof.
  apply sem_ro_tot_is_prt_excludes_bot.
Defined.
    
Lemma sem_rw_tot_is_prt_excludes_bot : forall Γ Δ e τ ϕ ψ (w : Γ ;;; Δ ||- e : τ), 
    w ||= [{ϕ}] e [{ψ}] ->
    w ||= {{ϕ}} e {{ψ}} /\ 
    (forall γ δ, ϕ (δ, γ) -> ⊥ ∉ sem_rw_exp _ _ _ _ w γ δ).
Proof.
  intros Γ Δ e τ ϕ ψ w h1.
  split.
  intros γ δ m; simpl; simpl in m.
  destruct (h1 γ δ m) as [h3 h4]; split; auto.
  intros.
  pose proof (h4 v H).
  destruct H1.
  destruct H1.
  rewrite H0 in H1.
  apply total_is_injective in H1.
  rewrite H1; auto.
  intros.
  destruct (h1 γ δ H) as [_ h4].
  intro h.
  pose proof (h4 ⊥ h) as [j [i _]].
  contradict (flat_bot_neq_total _ i).
Qed.

Lemma sem_rw_tot_excludes_bot : forall Γ Δ e τ ϕ ψ (w : Γ ;;; Δ ||- e : τ), 
    w ||= [{ϕ}] e [{ψ}] ->
    (forall γ δ, ϕ (δ, γ) -> ⊥ ∉ sem_rw_exp _ _ _ _ w γ δ).
Proof.
  apply sem_rw_tot_is_prt_excludes_bot.
Defined.

    
Lemma ro_prt_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    (w |= {{ϕ}} e {{ψ}}) ->
    forall y,
    forall γ, ϕ γ -> total y ∈ sem_ro_exp _ _ _ w γ -> ψ y γ.
Proof.
  intros.
  pose proof (H γ H0) as [H2 H3].
  exact (H3 (total y) H1 y eq_refl).
Defined.

Lemma ro_tot_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    (w |= [{ϕ}] e [{ψ}]) ->
    forall y,
    forall γ, ϕ γ -> total y ∈ sem_ro_exp _ _ _ w γ -> ψ y γ.
Proof.
  intros.
  pose proof (H γ H0) as [H3 H4].
  pose proof (H4 _ H1) as [v [p q] ].
  injection p; intro j; rewrite j; exact q.
Defined.
  
Lemma trip_ro_prt_sem_typing_irrl : forall Γ e τ ϕ ψ (w1 w2 : Γ |- e : τ), (w1 |= {{ϕ}} e {{ψ}}) -> (w2 |= {{ϕ}} e {{ψ}}).
Proof.
  intros.
  intros γ m.
  rewrite (sem_ro_exp_unique _ _ _ w2 w1).
  apply H; auto.
Defined.

Lemma trip_rw_prt_sem_typing_irrl : forall Γ Δ e τ ϕ ψ (w1 w2 : Γ ;;; Δ ||- e : τ), (w1 ||= {{ϕ}} e {{ψ}}) -> (w2 ||= {{ϕ}} e {{ψ}}).
Proof.
  intros.
  intros γ m.
  rewrite (sem_rw_exp_unique _ _ _ _ w2 w1).
  apply H; auto.
Defined.

Lemma trip_ro_tot_sem_typing_irrl : forall Γ e τ ϕ ψ (w1 w2 : Γ |- e : τ), (w1 |= [{ϕ}] e [{ψ}]) -> (w2 |= [{ϕ}] e [{ψ}]).
Proof.
  intros.
  intros γ m.
  rewrite (sem_ro_exp_unique _ _ _ w2 w1).
  apply H; auto.
Defined.

Lemma trip_rw_tot_sem_typing_irrl : forall Γ Δ e τ ϕ ψ (w1 w2 : Γ ;;; Δ ||- e : τ), (w1 ||= [{ϕ}] e [{ψ}]) -> (w2 ||= [{ϕ}] e [{ψ}]).
Proof.
  intros.
  intros γ m.
  rewrite (sem_rw_exp_unique _ _ _ _ w2 w1).
  apply H; auto.
Defined.
