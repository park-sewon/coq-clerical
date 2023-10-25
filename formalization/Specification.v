Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.


Structure ro_prt (Γ : ctx) (e : exp) (τ : datatype) :=
  {
    ro_prt_pre : sem_ctx Γ -> Prop ;
    ro_prt_post : sem_ctx Γ * sem_datatype τ -> Prop
  }.

Structure ro_tot (Γ : ctx) (e : exp) (τ : datatype) :=
  {
    ro_tot_pre : sem_ctx Γ -> Prop ;
    ro_tot_post : sem_ctx Γ * sem_datatype τ ->  Prop
  }.

Structure rw_prt (Γ Δ : ctx) (c : exp) (τ : datatype) :=
  {
    rw_prt_pre :  sem_ctx Γ * sem_ctx Δ -> Prop ;
    rw_prt_post : sem_ctx Γ * (sem_ctx Δ * sem_datatype τ) -> Prop
  }.

Structure rw_tot (Γ Δ : ctx) (c : exp) (τ : datatype) :=
  {
    rw_tot_pre : sem_ctx Γ * sem_ctx Δ -> Prop ;
    rw_tot_post : sem_ctx Γ * (sem_ctx Δ * sem_datatype τ) -> Prop
  }.

Definition sem_ro_prt {Γ} {e} {τ} (t : ro_prt Γ e τ) :=
  {w : (Γ |- e : τ) &
    let P := ro_prt_pre _ _ _ t in
    let Q := ro_prt_post _ _ _ t in
    forall γ, P γ ->
              let V := sem_ro_exp Γ e τ w γ in
              pdom_neg_is_empty V /\
                forall v, v ∈ V -> forall v', v = total v' -> Q (γ, v')}.

Definition sem_ro_tot {Γ} {e} {τ} (t : ro_tot Γ e τ) :=
  {w : (Γ |- e : τ) &
    let P := ro_tot_pre _ _ _ t in
    let Q := ro_tot_post _ _ _ t in
    forall γ, P γ ->
              let V := sem_ro_exp Γ e τ w γ in
              pdom_neg_is_empty V /\
                forall v, v ∈ V -> exists v', v = total v' /\ Q (γ, v')}.

Definition sem_rw_prt {Γ Δ} {c} {τ} (t : rw_prt Γ Δ c τ) :=
  {w : (Γ ;;; Δ ||- c : τ) &    
    let P := rw_prt_pre _ _ _ _ t in
    let Q := rw_prt_post _ _ _ _ t in
    forall γ δ, P (γ, δ) ->
                let V := sem_rw_exp Γ Δ c τ w γ δ in
                pdom_neg_is_empty V /\
                  forall v, v ∈ V -> forall v',
                      v = total v' -> Q (γ, v')}.

Definition sem_rw_tot {Γ Δ} {c} {τ} (t : rw_tot Γ Δ c τ) :=
  {w : (Γ ;;; Δ ||- c : τ) &    
    let P := rw_tot_pre _ _ _ _ t in
    let Q := rw_tot_post _ _ _ _ t in
    forall γ δ, P (γ, δ) ->
                let V := sem_rw_exp Γ Δ c τ w γ δ in
                pdom_neg_is_empty V /\
                  forall v, v ∈ V -> exists v',
                      v = total v' /\ Q (γ, v')}.

Definition mk_ro_prt {Γ} {e} {τ} P Q : ro_prt Γ e τ
  := {| ro_prt_pre := P ; ro_prt_post := Q |}.

Definition mk_ro_tot {Γ} {e} {τ} P Q : ro_tot Γ e τ
  := {| ro_tot_pre := P ; ro_tot_post := Q |}.

Definition mk_rw_prt {Γ Δ} {e} {τ} P Q : rw_prt Γ Δ e τ
  := {| rw_prt_pre := P ; rw_prt_post := Q |}.

Definition mk_rw_tot {Γ Δ} {e} {τ} P Q : rw_tot Γ Δ e τ
  := {| rw_tot_pre := P ; rw_tot_post := Q |}.

Declare Scope clerical_soundness_scope.
Notation " [| x ':' Γ |] '|=' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵖ' " 
  := (sem_ro_prt (@mk_ro_prt Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)))
       (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_soundness_scope.
Notation " [| x ':' Γ |] '|=' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵗ' "
  := (sem_ro_tot (@mk_ro_tot Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)))
       (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_soundness_scope.
Notation " [| x ':' Γ  ';;;'   y ':' Δ |] '||=' '{{' ϕ '}}' e '{{' z ':' τ '|' ψ '}}ᵖ' "
  := (sem_rw_prt (@mk_rw_prt Γ Δ e τ (fun '(x, y) => ϕ) (fun '(x, (y, z)) => ψ)))
       (at level 50, Γ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern) : clerical_soundness_scope.
Notation " [| x ':' Γ  ';;;'   y ':' Δ |] '||=' '{{' ϕ '}}' e '{{' z ':' τ '|' ψ '}}ᵗ' "
  := (sem_rw_tot (@mk_rw_tot Γ Δ e τ (fun '(x, y) => ϕ) (fun '(x, (y, z)) => ψ)))
       (at level 50, Γ, ϕ, e, z, τ, ψ at next level, x pattern, y pattern) : clerical_soundness_scope.
Open Scope clerical_soundness_scope.

(* Now let us prove some properties *)
Notation " [ x : Γ ] |- {{ y : τ | ϕ }} "
  := (fun '((x, y) : sem_ctx Γ * sem_datatype τ) =>  ϕ)
       (at level 50,  Γ, ϕ, y, τ at next level, x pattern) : clerical_scope.
Notation " [ x : Γ ;;; y : Δ ] ||- {{ z : τ | ϕ }} "
  := (fun '((x, (y, z)) : sem_ctx Γ * (sem_ctx Δ * sem_datatype τ)) =>  ϕ)
       (at level 50,  Γ, Δ, ϕ, z, τ at next level, x pattern, y pattern) : clerical_scope.
Notation " [ x : Γ ] |- {{ ϕ }} "
  := (fun x : sem_ctx Γ => ϕ)
       (at level 50,  Γ, ϕ at next level, x pattern) : clerical_scope.
Notation " [ x : Γ ;;; y : Δ ] ||- {{ ϕ }} "
  := (fun '((x, y) :  sem_ctx Γ * sem_ctx Δ) => ϕ)
       (at level 50,  Γ, Δ, ϕ at next level, x pattern, y pattern) : clerical_scope.

Lemma sem_ro_prt_excludes_bot_is_tot : forall Γ e τ ϕ ψ (w : Γ |- e : τ), 
    [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ -> 
    (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ w γ) ->
    [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ.
Proof.
  intros Γ e τ ϕ ψ w [w' h1] h2.
  simpl in h1.
  exists w'.
  simpl.
  intros γ m; simpl; simpl in m.
  
  destruct (h1 γ m) as [h3 h4]; split; auto.
  intros v m'.
  destruct v.
  rewrite (sem_ro_exp_unique _ _ _ w' w) in m'.
  contradict (h2 _ m m').
  exists s; split; auto.
  apply (h4 _ m' _ eq_refl).
Qed.

Lemma sem_rw_prt_excludes_bot_is_tot : forall Γ Δ e τ ϕ ψ (w : Γ ;;; Δ ||- e : τ), 
    [|γ : Γ ;;; δ : Δ|] ||= {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵖ -> 
    (forall γ δ, ϕ γ δ -> ⊥ ∉ sem_rw_exp _ _ _ _ w γ δ) ->
    [|γ : Γ ;;; δ : Δ|] ||= {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵗ. 
Proof.
  intros Γ Δ e τ ϕ ψ w [w' h1] h2.
  exists w'.
  simpl.
  intros γ δ m; simpl; simpl in m.
  destruct (h1 γ δ m) as [h3 h4]; split; auto.
  intros v m'.
  destruct v.
  rewrite (sem_rw_exp_unique _ _ _ _ w' w) in m'.
  contradict (h2 _ _ m m').
  exists p; split; auto.
  apply (h4 _ m' _ eq_refl).
Qed.

Lemma sem_ro_tot_is_prt_excludes_bot : forall Γ e τ ϕ ψ, 
    forall t : [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ,
      ([|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ * 
         (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ (projT1 t) γ)).
Proof.
  intros Γ e τ ϕ ψ [w' h1].
  split.
  simpl in h1.
  exists w'.
  simpl.
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
  simpl in h.
  simpl in h1.
  pose proof (h4 ⊥ h) as [j [i _ ] ].
  contradict (flat_bot_neq_total _ i).
Qed.

(* Lemma sem_ro_tot_excludes_bot : forall Γ e τ ϕ ψ (w : Γ |- e : τ),  *)
(*     [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ -> *)
(*          (forall γ, ϕ γ -> ⊥ ∉ sem_ro_exp _ _ _ w γ). *)
(* Proof. *)
(*   apply sem_ro_tot_is_prt_excludes_bot. *)
(* Defined. *)
    
Lemma sem_rw_tot_is_prt_excludes_bot : forall Γ Δ e τ ϕ ψ, 
    forall t : [|γ : Γ ;;; δ : Δ|] ||=  {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵗ,
    ([|γ : Γ ;;; δ : Δ|] ||=  {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵖ * 
                      (forall γ δ, ϕ γ δ -> ⊥ ∉ sem_rw_exp _ _ _ _ (projT1 t) γ δ)).
Proof.
  intros Γ Δ e τ ϕ ψ [w' h1].
  split.
  exists w'; simpl; simpl in h1.
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
  pose proof (h4 ⊥ h) as [j [i _ ] ].
  contradict (flat_bot_neq_total _ i).
Qed.

(* Lemma sem_rw_tot_excludes_bot : forall Γ Δ e τ ϕ ψ (w : Γ ;;; Δ ||- e : τ),  *)
(*     [|γ : Γ ;;; δ : Δ|] ||= {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵗ -> *)
(*     (forall γ δ, ϕ γ δ -> ⊥ ∉ sem_rw_exp _ _ _ _ w γ δ). *)
(* Proof. *)
(*   apply sem_rw_tot_is_prt_excludes_bot. *)
(* Defined. *)

    
Lemma ro_prt_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ ->
    forall y γ, ϕ γ -> total y ∈ sem_ro_exp _ _ _ w γ -> ψ γ y.
Proof.
  intros.
  destruct H as [w' H].
  pose proof (H γ H0) as [H2 H3].
  simpl in H3.
  rewrite (sem_ro_exp_unique _ _ _ w' w) in H3.
  exact (H3 (total y) H1 y eq_refl).
Defined.

Lemma ro_tot_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    [|γ : Γ|] |= {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ ->
         forall y,
         forall γ, ϕ γ -> total y ∈ sem_ro_exp _ _ _ w γ -> ψ γ y.
Proof.
  intros.
  destruct H as [w' H].
  simpl in H.
  rewrite (sem_ro_exp_unique _ _ _ w' w) in H.
  pose proof (H γ H0) as [H3 H4].
  pose proof (H4 _ H1) as [v [p q] ].
  injection p; intro j; rewrite j; exact q.
Defined.
  
