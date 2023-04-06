Require Import List.

Require Import Clerical.
Require Import Typing.
Require Import Powerdomain.
Require Import Semantics.
Require Import Specification.
Require Import Reasoning.
Require Import Reals.

Notation " w |= {{ ϕ }} e {{ ψ }} ":= (sem_ro_prt (@mk_ro_prt _ e _ w ϕ ψ)) (at level 85).
Notation " w |= [{ ϕ }] e [{ ψ }] ":= (sem_ro_tot (@mk_ro_tot _ e _ w ϕ ψ)) (at level 85).
Notation " w ||= {{ ϕ }} e {{ ψ }} ":= (sem_rw_prt (@mk_rw_prt _ _ e _ w ϕ ψ)) (at level 85).
Notation " w ||= [{ ϕ }] e [{ ψ }] ":= (sem_rw_tot (@mk_rw_tot _ _ e _ w ϕ ψ)) (at level 85).

Lemma ro_prt_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    (w |= {{ϕ}} e {{ψ}}) ->
    forall y,
    forall γ, ϕ γ -> total y ∈ sem_ro_comp _ _ _ w γ -> ψ y γ.
Proof.
  intros.
  pose proof (H γ H0) as [H2 H3].
  exact (H3 (total y) H1 y eq_refl).
Defined.

Lemma ro_tot_post_pre : forall Γ e τ ϕ ψ (w : Γ |- e : τ),
    (w |= [{ϕ}] e [{ψ}]) ->
    forall y,
    forall γ, ϕ γ -> total y ∈ sem_ro_comp _ _ _ w γ -> ψ y γ.
Proof.
  intros.
  pose proof (H γ H0) as [H3 H4].
  pose proof (H4 _ H1) as [v [p q] ].
  injection p; intro j; rewrite j; exact q.
Defined.
  
Axiom magic : forall A, A.

(* semantics is unique *)
Lemma sem_ro_comp_unique : forall Γ e τ (w1 w2 : Γ |- e : τ), sem_ro_comp Γ e τ w1 = sem_ro_comp Γ e τ w2
with sem_rw_comp_unique : forall Γ Δ e τ (w1 w2 : Γ ;;; Δ ||- e : τ), sem_rw_comp Γ Δ e τ w1 = sem_rw_comp Γ Δ e τ w2.
Proof.
  intros.

  induction w1; apply magic.

  intros.
  induction e; apply magic.
Qed.

Lemma flat_to_pdom_neg_empty : forall X (x : flat X), pdom_neg_is_empty (flat_to_pdom x).
Proof.
  intros.
  destruct x.
  apply (pdom_is_neg_empty_by_evidence _ (bot X)).
  simpl; auto.
  apply (pdom_is_neg_empty_by_evidence _ (total x)).
  simpl; auto.
Qed.

Lemma total_is_injective : forall {X} {x y : X}, total x = total y -> x = y.
Proof.
  intros.
  injection H; auto.
Defined.

Lemma Rlim_def_never_bot : forall f, ~ (Rlim_def f (bot R)).
Proof.
Admitted.

  
Lemma proves_ro_prt_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- {{ϕ}} e {{ψ}} -> w |= {{ϕ}} e {{ψ}}
with proves_ro_tot_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- [{ϕ}] e [{ψ}] -> w |= [{ϕ}] e [{ψ}]
with proves_rw_prt_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- {{ϕ}} e {{ψ}} -> w ||= {{ϕ}} e {{ψ}}
with proves_rw_tot_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- [{ϕ}] e [{ψ}] -> w ||= [{ϕ}] e [{ψ}].
Proof.
  + (*  partial correctness triple for read only expressions *)
    intros Γ e τ w ϕ ψ trip.
    induction trip.
    (** logical rules *)
    (* (*  partial correctness triple for read only expressions *) *)
    (* (** logical rules *) *)

    ++
      (* | ro_imply_prt : forall Γ e τ (w : Γ |- e : τ) P Q P' Q', *)
      
      (*     P' ->> P ->  *)
      (*     w |- {{ P }} e {{ Q }} ->  *)
      (*     Q ->>> Q' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{ P'}}  e {{ Q' }} *)


      intros γ m.
      simpl; simpl in m.
      apply a in m.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as H.
      simpl in H.
      split; destruct H as [h1 h2]; auto.
      intros t1 t2 t3 t4.
      apply a0, (h2 _ t2 _ t4).
      
    ++
      (* | ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- {{ (fun _ => False) }} e {{ Q }} *)
      intros γ m.
      simpl in m.
      contradict m; auto.
      
    ++
      (* | ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P}} e {{Q'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P}} e {{Q /\\\ Q'}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as H1; simpl in H1.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as H2; simpl in H2.
      destruct H1 as [a p1]; destruct H2 as [_ p2]; split; auto.
      intros v p v' p'.
      split; try apply (p1 v p v' p'); try apply (p2 v p v' p').

    ++
      (* | ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P'}} e {{Q}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P \// P'}} e {{Q}} *)
    
      intros γ m; simpl in m; simpl.
      destruct m as [m|m]. 
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2]; split; auto.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [p1 p2]; split; auto.

    ++
      (* (** variables and constants *) *)
      (* | ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{fun γ => Q (ro_access Γ k τ w γ) γ}} VAR k {{Q}} *)

      intros γ m; simpl in m; simpl.
      apply magic.

    ++
      (* | ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q tt}} SKIP {{Q}} *)
      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique Γ SKIP UNIT w (has_type_ro_Skip _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      destruct p3; auto.
      
    ++
      (* | ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q true}} TRUE {{Q}} *)
      
      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique _ _ _ w (has_type_ro_True _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* | ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q false}} FALSE {{Q}} *)


      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique _ _ _ w (has_type_ro_False _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* | ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q k}} INT k {{Q}} *)


      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique _ _ _ w (has_type_ro_Int _ _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | rw_ro_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ), *)
      
      (*     w ||- {{P}} c {{Q}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{fun γ => P (tt, γ)}} c {{fun v w => Q v (tt, w)}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p γ tt m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_rw _ _ _ w)).
      simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (p1 h).
      intros x1 [x2 [q1 q2]] x3 x4.
      apply (p2 x2 q1 (tt, x3)).
      destruct x1.
      contradict (flat_bot_neq_total _ x4).
      destruct x2.
      simpl in q2.
      contradict (flat_bot_neq_total _ q2).
      injection x4; intro i.
      simpl in q2; injection q2; intro j.
      rewrite i in j.
      rewrite <- j.
      destruct p0, u; simpl; auto.
      
    ++
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL), *)
      
      (*     w |- {{P}} e {{y | Q (IZR y)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} RE e {{Q}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZRcoerce  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      injection H0; intro j; clear H0.
      induction j.
      destruct H as [a [b c]].
      destruct a.
      simpl in c.
      contradict (flat_bot_neq_total _ c).
      pose proof (p2 _ b z (eq_refl)) as h.
      simpl in h.
      simpl in c.
      injection c; intro i; rewrite <- i; exact h.

    ++
      (* | ro_exp_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL), *)
      
      (*     w |- {{P}} e {{y | Q (powerRZ 2 y)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} EXP e {{Q}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZRexp  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      injection H0; intro j; clear H0.
      induction j.
      destruct H as [a [b c]].
      destruct a.
      simpl in c.
      contradict (flat_bot_neq_total _ c).
      pose proof (p2 _ b z (eq_refl)) as h.
      simpl in h.
      simpl in c.
      injection c; intro i; rewrite <- i; exact h.
      
    ++
      (* (** integer arithmetic  *) *)
      (* | ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)-> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*      w' |- {{ϕ}} e1 :+: e2 {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ (e1 :+: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Z.add) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).
               
      
    ++
      (* | ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :*: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ (e1 :*: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Zmult) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :-: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ (e1 :-: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Zminus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;+; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ (e1 ;+; e2) REAL w' γ
              =
                pdom_lift2 (Rplus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;*; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ _ _ w' γ
              =
                pdom_lift2 (Rmult) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;-; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ _ _ w' γ
              =
                pdom_lift2 (Rminus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** reciprocal *) *)
      (* | ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- {{ϕ}} e {{θ}} ->  *)
      (*     (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} UniOp OpRrecip e {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      split.
      {
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)).
        simpl.
        intro.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (p1 H).
        destruct H as [x p].
        destruct p as [p q].
        unfold Rrecip in q.
        contradict q.
        destruct (Rrecip' x).
        apply (pdom_is_neg_empty_by_evidence _ (bot R)); simpl; auto.
        apply (pdom_is_neg_empty_by_evidence _ (total r)); simpl; auto.
      }
      intros v h1 h2 h3.
      assert (sem_ro_comp Γ (;/; e) REAL w' γ =
                pdom_bind Rrecip (sem_ro_comp Γ e REAL w γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)); simpl; auto.
      rewrite H in h1; clear H.
      simpl in p2.
      rewrite h3 in h1; rename h3 into j.
      apply pdom_bind_total_2 in h1.
      destruct h1 as [_ h1].
      destruct h1 as [x h].
      destruct h as [h1 h3].
      unfold Rrecip in h3.
      unfold Rrecip' in h3.
      destruct (total_order_T x 0).
      destruct s.
      {
        (* when x < 0 *)     
        unfold asrt_and2 in a.
        assert (H : x <> 0%R) by (apply Rlt_not_eq, r). 
        pose proof (a x γ (conj (p2 _ h1 x eq_refl) H)) as jj.
        simpl in jj; simpl in H; simpl in h3.
        injection h3; intro i; rewrite i in jj; auto.
      }
      {
        (* when x = 0 *)
        simpl in h3.
        contradict (flat_bot_neq_total _ h3).
      }
      {
        (* when x > 0 *)     
        unfold asrt_and2 in a.
        assert (H : x <> 0%R) by (apply Rgt_not_eq, r). 
        pose proof (a x γ (conj (p2 _ h1 x eq_refl) H)) as jj.
        simpl in jj; simpl in H; simpl in h3.
        injection h3; intro i; rewrite i in jj; auto.
      }

    ++
      (* (** integer comparison  *) *)
      (* | ro_int_comp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post), *)

      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :=: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ _ _ w' γ
              =
                pdom_lift2 (BinInt.Z.eqb) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_int_comp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 :<: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_comp Γ _ _ w' γ
              =
                pdom_lift2 (BinInt.Z.ltb) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** real comparison  *) *)
      (* | ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) P ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 ;<; e2) {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl.      
        intro.
        unfold pdom_bind2 in H.
        apply pdom_bind_empty_2 in H.
        unfold pdom_prod in H.
        destruct H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H.
        destruct H.
        apply pdom_lift_empty_2 in H0.
        apply (p1 H0).
        destruct H.
        destruct H.
        unfold Rltb in H0.
        contradict H0.
        apply flat_to_pdom_neg_empty.
      }
      
      intros v h1 h2 h3.
      assert (sem_ro_comp Γ _ _ w' γ  = pdom_bind2 Rltb (sem_ro_comp Γ e1 REAL w1 γ) (sem_ro_comp Γ e2 REAL w2 γ)).
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl; auto.
      rewrite H in h1; clear H.
      rewrite h3 in h1.
      unfold pdom_bind2 in h1.
      apply pdom_bind_total_2 in h1.
      destruct h1.
      destruct H0.
      destruct H0.
      destruct x.
      unfold pdom_prod in H0.
      apply pdom_bind_total_2 in H0.
      destruct H0.
      destruct H2.
      destruct H2.
      simpl in H3.
      destruct H3.
      simpl in H1.
      unfold Rltb' in H1.
      unfold Rltb'' in ψ3.
      clear H H0.
      destruct H3.
      destruct x0.
      simpl in H0.
      contradict (flat_bot_neq_total _ H0).
      simpl in H0.
      injection H0; intros i j.
      induction i, j.
      
      pose proof (ψ3 r1 x γ (p2 _ H _ eq_refl) (q2 _ H2 _ eq_refl)).
      destruct (total_order_T r1 x).
      destruct s.
      injection H1; intro i; rewrite <- i; apply H3; apply Rlt_not_eq; apply r.
      contradict (flat_bot_neq_total _ H1).
      injection H1; intro i; rewrite <- i; apply H3; apply Rgt_not_eq; apply r.
      
    ++
      (* (* Limit *) *)
      (* | ro_lim_prt : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ, *)

      (*     w |- [{fun γ' => ϕ (snd γ')}] e [{θ}] -> *)
      (*     (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} Lim e {{ψ}} *)

      intros γ m; simpl; simpl in m.
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_Lim _ _ w)).
      simpl.
      pose proof (fun z => proves_ro_tot_sound _ _ _ w (fun zγ => ϕ0 (snd zγ)) θ p (z, γ) m).
      simpl in H.
      pose proof (e0 γ m).
      destruct H0 as [y h1].
      destruct h1 as [h1 h2].
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; split; auto.
        intros.
        destruct z.
        destruct (H x) as [_ h].
        pose proof (h (bot R) H0).
        destruct H1.
        destruct H1.
        contradict (flat_bot_neq_total _ H1).
        exists r; split; auto.
        destruct (H x) as [_ h].
        pose proof (h _ H0).
        destruct H1.

        destruct H1.
        injection H1; intro j; rewrite <- j in H2; clear j.
        apply (h2 x r H2).
      }
      intros.
      assert (total y = total v').
      apply (Rlim_def_unique ((fun x : Z => sem_ro_comp (INTEGER :: Γ) e REAL w (x, γ)))); auto.
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      destruct z.
      destruct (H x) as [_ h].
      pose proof (h (bot R) H2).
      destruct H3.
      destruct H3.
      contradict (flat_bot_neq_total _ H3).
      exists r; split; auto.
      destruct (H x) as [_ h].
      pose proof (h _ H2).
      destruct H3.
      destruct H3.
      apply h2.
      injection H3; intro j; rewrite j; auto.
      rewrite <- H1; auto.
      injection H2; intro j; rewrite <- j; auto.


  + (*  total correctness triple for read only expressions *)
    intros Γ e τ w ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | ro_imply_tot : forall Γ e τ (w : Γ |- e : τ) P Q P' Q', *)

      (*     P' ->> P ->  *)
      (*     w |- [{ P }] e [{ Q }] ->  *)
      (*     Q ->>> Q' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{ P'}]  e [{ Q' }] *)

      intros γ m; simpl; simpl in m.
      apply a in m.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as H.
      simpl in H.
      split; destruct H as [h1 h2]; auto.
      intros t1 t2.
      pose proof (h2 _ t2) as [p1 p2].
      destruct p2 as [p2 p3].
      exists p1; split; auto; try apply a0; auto.
      
    ++
      (* | ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- [{ (fun _ => False) }] e [{ Q }] *)

      intros γ m; simpl; simpl in m.
      contradict m.

    ++
      (* | ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)
      

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P}] e [{Q'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P}] e [{Q /\\\ Q'}] *)
      intros γ m; simpl; simpl in m.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [_ q2].
      split.
      intro.
      apply (p1 H).
      intros v i.
      pose proof (p2 _ i).
      pose proof (q2 _ i).
      destruct H, H0.
      destruct H, H0.
      exists x.
      split; auto.
      split; auto.
      rewrite H in H0; injection H0; intro j; rewrite j; auto.
      
    ++
      (* | ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P'}] e [{Q}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P \// P'}] e [{Q}] *)
      intros γ m; simpl; simpl in m.
      destruct m as [m|m].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      split; auto.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [p1 p2].
      split; auto.
      
    ++
      (* (** variables and constants *) *)
      (* | ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{fun γ => Q (ro_access Γ k τ w γ) γ}] VAR k [{Q}] *)

      apply magic.

    ++
      (* | ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q tt}] SKIP [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique Γ SKIP UNIT w (has_type_ro_Skip _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists tt; split; auto.

    ++
      (* | ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q true}] TRUE [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique Γ _ _ w (has_type_ro_True _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists true; split; auto.

    ++
      (* | ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q false}] FALSE [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique Γ _ _ w (has_type_ro_False _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists false; split; auto.

    ++
      (* | ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q k}] INT k [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_comp_unique Γ _ _ w (has_type_ro_Int _ _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists k; split; auto.

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | rw_ro_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ), *)
      
      (*     w ||- [{P}] c [{Q}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{fun γ => P (tt, γ)}] c [{fun v w => Q v (tt, w)}] *)
      
      intros γ m; simpl in m; simpl.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ p γ tt m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_rw _ _ _ w)).
      simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (p1 h).
      intros x1 [x2 [x3 x4] ].
      destruct (p2 x2 x3) as [[u v] [h1 h2]].
      exists v.
      simpl in h2.
      rewrite h1 in x4; simpl in x4; rewrite <- x4; destruct u; split; auto.
      
    ++
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- RE e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (IZR y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] RE e [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZRcoerce  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros y [x [h1 h2]].
      destruct (p2 x h1) as [x' [h3 h4]].
      rewrite h3 in h2.
      simpl in h2.
      exists (IZR x'); split; auto; simpl in h4; auto.

    ++
      (* | ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- EXP e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (powerRZ 2 y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] EXP e [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZRexp  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros y [x [h1 h2]].
      destruct (p2 x h1) as [x' [h3 h4]].
      rewrite h3 in h2.
      simpl in h2.
      exists (powerRZ 2 x'); split; auto; simpl in h4; auto.

    ++
      (* (** integer arithmetic  *) *)
      (* | ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)-> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*      w' |- [{ϕ}] e1 :+: e2 [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZplus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp Γ (e1 :+: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Z.add) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
      
    ++
      (* | ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :*: e2) [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZmult _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp Γ (e1 :*: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Zmult) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* | ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :-: e2) [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZminus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp Γ (e1 :-: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Zminus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;+; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRplus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_lift2 (Rplus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* | ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;*; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRmult _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_lift2 (Rmult) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.

    ++
      (* | ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;-; e2) [{ψ}] *)
      
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRminus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_lift2 (Rminus) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.

    ++

      (* (** reciprocal *) *)
      (* | ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- [{ϕ}] e [{θ}] ->  *)
      (*     (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] ;/; e [{ψ}] *)

      apply magic.

    ++
      (* (** integer comparison  *) *)
      (* | ro_int_comp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post), *)

      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :=: e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZeq _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_lift2 (Z.eqb) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists b; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.


    ++
      (* | ro_int_comp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- [{P}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{P}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{P}] (e1 :<: e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZlt _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_lift2 (Z.ltb) (sem_ro_comp _ _ _ w1 γ) (sem_ro_comp _ _ _ w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists b; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* (** real comparison  *) *)
      (* | ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2  (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;<; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRlt _  _ _ w1 w2)); simpl.
        intro.
        unfold pdom_bind2 in H.
        apply pdom_bind_empty_2 in H.
        unfold pdom_prod in H.
        destruct H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
        destruct H as [[x1 x2] [h1 h2]].
        unfold Rltb in h2.
        apply flat_to_pdom_neg_empty in h2.
        auto.
      }
      replace (sem_ro_comp _ _ _ w' γ) with
        (pdom_bind2 Rltb (sem_ro_comp Γ e1 REAL w1 γ) (sem_ro_comp Γ e2 REAL w2 γ))
        by (rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_bind2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_bind_bot_2 in H.
        destruct H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
        destruct H as [[x1 x2] [h1 h2]].
        apply pdom_bind_total_2 in h1 as [_ [x2' [h1 h3]]].
        apply pdom_lift_total_2 in h3 as [x1' [h3 h4]].
        rewrite h4 in h2.
        simpl in h2.
        unfold Rltb' in h2.
        destruct (total_order_T x1' x2').
        destruct s.
        contradict (flat_total_neq_bot _ h2).
        pose proof (p2 _ h3) as [x1'' [e1'' h1'']]; apply total_is_injective in e1''.
        pose proof (q2 _ h1) as [x2'' [e2'' h2'']]; apply total_is_injective in e2''.
        induction e1'', e2''.
        contradict (proj1 (a _ _ _ h1'' h2'') e).
        contradict (flat_total_neq_bot _ h2).
      }
      exists b; split; auto.
      apply pdom_bind_total_2 in H as [_ [[x1 x2] [h1 h2]]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (a _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      unfold Rltb'' in H.
      unfold Rltb' in h2.
      destruct H as [p H].
      destruct (total_order_T x2' x1') as [[s | s]| s].
      apply total_is_injective in h2; rewrite<- h2; auto.
      contradict (p s).
      apply total_is_injective in h2; rewrite<- h2; auto.
      
    ++
      (* (* Limit *) *)
      (* | ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ, *)

      (*     w |- [{fun γ' => ϕ (snd γ')}] e [{θ}] -> *)
      (*     (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] Lim e [{ψ}] *)
      intros γ m; simpl; simpl in m.
      rewrite (sem_ro_comp_unique _ _ _ w' (has_type_ro_Lim _ _ w)).
      simpl.
      pose proof (fun z => proves_ro_tot_sound _ _ _ w (fun zγ => ϕ0 (snd zγ)) θ trip (z, γ) m).
      simpl in H.
      pose proof (e0 γ m).
      destruct H0 as [y h1].
      destruct h1 as [h1 h2].
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; split; auto.
        intros.
        destruct z.
        destruct (H x) as [_ h].
        pose proof (h (bot R) H0).
        destruct H1.
        destruct H1.
        contradict (flat_bot_neq_total _ H1).
        exists r; split; auto.
        destruct (H x) as [_ h].
        pose proof (h _ H0).
        destruct H1.

        destruct H1.
        injection H1; intro j; rewrite <- j in H2; clear j.
        apply (h2 x r H2).
      }
      intros.
      destruct v.
      contradict (Rlim_def_never_bot _ H0).
      exists r; split; auto.      
      replace r with y; auto.
      apply total_is_injective.
      apply (Rlim_def_unique ((fun x : Z => sem_ro_comp (INTEGER :: Γ) e REAL w (x, γ)))); auto.
      
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      destruct z.
      destruct (H x) as [_ h].
      pose proof (h (bot R) H1).
      destruct H2.
      destruct H2.
      contradict (flat_bot_neq_total _ H2).
      exists r0; split; auto.
      destruct (H x) as [_ h].
      pose proof (h _ H1).
      destruct H2.
      destruct H2.
      apply h2.
      injection H2; intro j; rewrite j; auto.
      
  + (*  partial correctness triple for read write expressions *)
    intros Γ Δ e τ w ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- {{ ϕ }} e {{ ψ }} ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ ϕ'}}  e {{ ψ' }} *)
      apply magic.

    ++
      (* | rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ (fun _ => False) }} e {{ ψ }} *)
      apply magic.

    ++
      (* | rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ}} e {{ψ'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ}} e {{ψ /\\\ ψ'}} *)
      apply magic.

    ++
      (* | rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ'}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ \// ϕ'}} e {{ψ}} *)
      apply magic.

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- {{ϕ}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}} *)
      apply magic.

    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- {{ϕ}} c1 {{θ}} ->  *)
      (*     w2 ||- {{θ tt}} c2 {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} c1 ;; c2 {{ψ}} *)
      apply magic.

    ++
      (* | rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- {{fun γδ => (ϕ (tedious_sem_concat _ _ γδ))}} e {{θ}} ->  *)
      (*     w2 ||- {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} NEWVAR e IN c {{ψ}} *)
      apply magic.

    ++
      (* | rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- {{fun δγ => ϕ (tedious_sem_concat _ _ δγ)}} e {{θ}} ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} LET k := e {{ψ}} *)
      apply magic.

    ++
      (* | rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- {{rw_to_ro_pre ϕ}} e {{θ}} -> *)
      (*     w1 ||- {{ro_to_rw_pre (θ true)}} c1 {{ψ}} -> *)
      (*     w2 ||- {{ro_to_rw_pre (θ false)}} c2 {{ψ}} -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} Cond e c1 c2 {{ψ}} *)
      apply magic.

    ++
      (* | rw_case_prt : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ, *)

      (*     wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} ->  *)
      (*     wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} ->  *)
      (*     wty_c1 ||- {{ro_to_rw_pre (θ1 true)}} c1 {{ψ}} ->  *)
      (*     wty_c2 ||- {{ro_to_rw_pre (θ2 true)}} c2 {{ψ}} -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- {{ϕ}} Case e1 c1 e2 c2 {{ψ}} *)
      apply magic.

    ++
      (* | rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ, *)

      (*     wty_e |- {{rw_to_ro_pre ϕ}} e {{θ}} ->  *)
      (*     wty_c ||- {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}} *)
      

      apply magic.

  + (*  total correctness triple for read write expressions *)
    intros Γ Δ e τ w ϕ ψ trip.
    induction trip.

    ++
      (* (** logical rules *) *)
      (* | rw_imply_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- [{ ϕ }] e [{ ψ }] ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ ϕ'}]  e [{ ψ' }] *)
      apply magic.

    ++
      (* | rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ (fun _ => False) }] e [{ ψ }] *)
      apply magic.

    ++
      (* | rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ}] e [{ψ'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ}] e [{ψ /\\\ ψ'}] *)
      apply magic.

    ++
      (* | rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ'}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ \// ϕ'}] e [{ψ}] *)
      apply magic.

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- [{ϕ}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}] e [{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}] *)
      apply magic.

    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : UNIT) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- [{ϕ}] c1 [{θ}] ->  *)
      (*     w2 ||- [{θ tt}] c2 [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] c1 ;; c2 [{ψ}] *)
      apply magic.

    ++
      (* | rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- [{fun γδ => (ϕ (tedious_sem_concat _ _ γδ))}] e [{θ}] ->  *)
      (*     w2 ||- [{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}] c [{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] NEWVAR e IN c [{ψ}] *)
      apply magic.

    ++
      (* | rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- [{fun δγ => ϕ (tedious_sem_concat _ _ δγ)}] e [{θ}] ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] LET k := e [{ψ}] *)
      apply magic.

    ++
      (* | rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     w1 ||- [{ro_to_rw_pre (θ true)}] c1 [{ψ}] -> *)
      (*     w2 ||- [{ro_to_rw_pre (θ false)}] c2 [{ψ}] -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] Cond e c1 c2 [{ψ}] *)
      apply magic.

    ++

      (* | rw_case_tot : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ ϕ1 ϕ2, *)
      
      (*     wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} ->  *)
      (*     wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} ->  *)
      (*     wty_c1 ||- [{ro_to_rw_pre (θ1 true)}] c1 [{ψ}] ->  *)
      (*     wty_c2 ||- [{ro_to_rw_pre (θ2 true)}] c2 [{ψ}] ->  *)
      (*     wty_e1 |- [{ϕ1}] e1 [{b |fun _ => b = true}] ->  *)
      (*     wty_e2 |- [{ϕ2}] e2 [{b | fun _ => b = true}] ->  *)
      (*     (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x)) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- [{ϕ}] Case e1 c1 e2 c2 [{ψ}] *)
      apply magic.

    ++
      (* | rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ, *)
      
      (*     wty_e |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     wty_c ||- [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_concat (snd δγδ')) /\ fst δγδ' = snd_concat (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_concat (snd δγδ')) /\ ψ δγδ' }] -> *)
      (*              (forall δ γ, ϕ (δ, γ) ->   *)
      (*                            ~exists f : nat -> sem_ro_ctx Δ, *)
      (*                                f 0 = δ /\ forall n, ψ (f (S n), (γ ; f n))) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}] *)

      apply magic.
Qed.

