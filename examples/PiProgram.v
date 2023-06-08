From Clerical Require Import Clerical.

Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra Lia List.
Open Scope R.
From Examples Require Import AbsProgram BoundedProgram LogicProgram SineProgram.

Definition clerical_pi :=
  Lim (
      NEWVAR INT 0 IN (* k *)
      NEWVAR RE (INT 3) IN (* l *)
      NEWVAR RE (INT 4) IN (* u *)
      WHILE VAR 2 :<: VAR 3 DO
        (NEWVAR (VAR 0 ;+; VAR 1) ;*; EXP (INT -1) IN
          IF RE (INT 0) ;<; clerical_sine 0
          THEN
            LET 2 := VAR 0
          ELSE
            LET 1 := VAR 0
                       END) ;; LET 2 := VAR 2 :+: INT 1 END ;; (VAR 1 ;+; VAR 0) ;*; EXP (INT -1)).

Definition is_rational x : Prop :=
  exists p q, x = IZR p / IZR q. 

Lemma Z_is_rational : forall z, is_rational (IZR z).
Proof.
  intros.
  exists z.
  exists 1%Z.
  unfold Rdiv.
  replace (/1) with 1 by auto with real.
  ring.
Defined.

Lemma pow2_increasing : forall a b, (a < b)%Z -> pow2 a < pow2 b.
Proof.
Admitted.

Lemma pow2_monotone : forall a b, (a <= b)%Z -> pow2 a <= pow2 b.
Proof.
Admitted.

  
Lemma ratoinals_midpoint_is_rational :
  forall x y, is_rational x -> is_rational y -> is_rational ((x + y) / 2).
Admitted.

Lemma midpoint_in_interval :
  forall x y, x < y -> x < (x + y)/2 < y.
Admitted.

Lemma PI_in_34 : 3 < PI < 4.
Admitted.


Lemma PI_unique_in_34 :
  forall s, 3<s<4 -> sin s = 0 -> s = PI.
Admitted.

Lemma PI_simple_in_34 :
  forall s, 3<s<4 -> (sin s < 0 -> PI < s) /\ (0 < sin s ->  s < PI).
Admitted.

Lemma PI_irrational :
  is_rational PI -> False.
Admitted.

Lemma dist_between_points_in_interval : forall a b c d,
    a < b -> a < c < b -> a < d < b ->
    Rabs (c - d) < b - a.
Admitted.

  
Lemma Rltb''_prop_false : forall x y,
    Rltb'' x y = false <-> y <= x.
Proof.
  intros.
  unfold Rltb''.
  destruct (total_order_T x y).
  destruct s.
  split.
  intro.
  contradict H; discriminate.
  intro.
  contradict (Rle_not_lt _ _ H r).
  split; intro; auto.
  right; auto.
  split; intro; auto.
  left; auto.
Defined.

Lemma pow2_minus_one : forall x,
    pow2 x / 2 = pow2 (x - 1).
Proof.
  intro.
  unfold Zminus.
  rewrite pow2_add.
  simpl.
  replace (2 * 1) with 2 by ring.
  unfold Rdiv; ring.
Defined.
  
Lemma pp_rw_cond_tot_util {Γ Δ} {τ} {e c1 c2} {ϕ} θ {ψ}
     : (Δ ++ Γ) |-- [{rw_to_ro_pre ϕ}] e [{y : BOOL | θ y}] ->
       Γ;;; Δ ||-- [{ϕ /\\ ro_to_rw_pre (θ true)}] c1 [{y : τ | ψ y}] ->
       Γ;;; Δ ||-- [{ϕ /\\ ro_to_rw_pre (θ false)}] c2 [{y : τ | ψ y}] ->
       Γ;;; Δ ||-- [{ϕ}] (IF e THEN c1 ELSE c2 END) [{y : τ | ψ y}].
Proof.
  intros.
  apply (pp_rw_cond_tot (θ := fun y x => rw_to_ro_pre ϕ x /\ θ y x)) .
  apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  apply (pp_rw_imply_tot X0).
  intros h1 [h2 h3]; split; auto.
  unfold rw_to_ro_pre in h2.
  rewrite tedious_equiv_0 in h2.
  exact h2.
  intros h1 h2 h3; auto.
  apply (pp_rw_imply_tot X1).
  intros h1 [h2 h3]; split; auto.
  unfold rw_to_ro_pre in h2.
  rewrite tedious_equiv_0 in h2.
  exact h2.
  intros h1 h2 h3; auto.
Defined.

Lemma pp_ro_real_comp_lt_tot_util {Γ} {e1 e2} {ϕ} ψ1 ψ2 {ψ} :
  Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
  Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
  (forall y1 y2 x, (ϕ x /\ ψ1 y1 x /\ ψ2 y2 x) -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) x)) ->
  Γ |-- [{ϕ}] e1 ;<; e2 [{y : BOOL | ψ y}].
Proof.
  intros.
  apply
    (pp_ro_real_comp_lt_tot
       ψ1
       (fun y x => ϕ x /\ ψ2 y x)).
  exact X.
  apply (pp_ro_tot_pose_readonly ϕ) in X0.
  apply (pp_ro_imply_tot X0).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  intros.
  apply H.
  repeat split; destruct H1 as [h1 h2]; auto.
Defined.

    

Lemma clerical_pi_correct :
  nil |--
    [{fun _ => True}]
    clerical_pi
    [{y : REAL | fun _ => y = PI}].
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun _ => PI));
    try (intros h1 h2 [_ h3]; auto; fail).

  apply pp_ro_rw_tot_back.
  
  apply (pp_rw_new_var_tot_util2 INTEGER (fun y _ => y = 0%Z)).
  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot_util2 REAL (fun y _ => y = 3)).
  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot_util2 REAL (fun y _ => y = 4)).
  proves_simple_arithmetical.

  apply (pp_rw_sequence_tot
           (θ := fun _ (δγ : sem_ro_ctx (REAL :: REAL :: INTEGER :: nil) * sem_ro_ctx (INTEGER :: nil))  => 
                   let p := fst (snd δγ) in
                   let l := fst (snd (fst δγ)) in
                   let u := fst (fst δγ) in 
                   Rabs (PI - (l + u) / 2) < pow2 (- p))).
  {
    
    pose (ϕ :=  fun (δγ : sem_ro_ctx (REAL :: REAL :: INTEGER :: nil) * sem_ro_ctx (INTEGER :: nil))  => 
                  let p := fst (snd δγ) in
                  let k := fst (snd (snd (fst δγ))) in
                  let l := fst (snd (fst δγ)) in
                  let u := fst (fst δγ) in 
                  is_rational l /\ is_rational u /\
                    3 <= l /\ l < PI < u /\ u <= 4 /\ u - l = pow2 (- k)).

    pose (θ :=
            fun (y : bool) (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil))) => 
              let p := fst (snd_app δγ) in
              let k := fst (snd (snd (fst_app δγ))) in
              let l := fst (snd (fst_app δγ)) in
              let u := fst (fst_app δγ) in 
              ϕ (fst_app δγ, snd_app δγ) /\
                (y = true <-> k < p)%Z).
    
    pose (ψ := fun (δγδ : sem_ro_ctx (REAL :: REAL :: INTEGER :: nil) * sem_ro_ctx ((INTEGER :: nil) ++ REAL :: REAL :: INTEGER :: nil)) => 
                 let p := fst (fst_app (snd δγδ)) in

                 let k := fst (snd (snd (fst δγδ))) in
                 let l := fst (snd (fst δγδ)) in
                 let u := fst (fst δγδ) in 
                 let k' := fst (snd (snd (snd_app (snd δγδ)))) in
                 let l' := fst (snd (snd_app (snd δγδ))) in
                 let u' := fst (snd_app (snd δγδ)) in 

                 (k = k' + 1 /\ k' < p)%Z).

    
    apply (pp_rw_while_tot_back (θ := θ) (ϕ := ϕ) (ψ := ψ)).
    {
      (* loop condition *)
      proves_simple_arithmetical.
      destruct x as [u [l [j [p t]]]].
      split.
      unfold fst_app, snd_app; simpl.
      unfold rw_to_ro_pre in pre.
      simpl in pre.
      exact pre.
      rewrite val.
      reduce_ro_access.
      lia.      
    }

    {
      (* loop invariant *)
      apply (pp_rw_sequence_tot
               (θ := fun _ (δγ : sem_ro_ctx (REAL :: REAL :: INTEGER :: nil) * sem_ro_ctx (INTEGER :: nil))  => 
                       let p := fst (snd δγ) in
                       let k := fst (snd (snd (fst δγ))) in
                       let l := fst (snd (fst δγ)) in
                       let u := fst (fst δγ) in 
                       is_rational l /\ is_rational u /\
                         3 <= l /\ l < PI < u /\ u <= 4 /\ u - l = pow2 (- (k + 1)))).
      
      apply (pp_rw_new_var_tot_util2 REAL (fun y (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  =>
                                             let p := fst (snd_app δγ) in
                                             let k := fst (snd (snd (fst_app δγ))) in
                                             let l := fst (snd (fst_app δγ)) in
                                             let u := fst (fst_app δγ) in 
                                             y = (l + u) / 2)).
      
      {
        (* assigned expression *)
        proves_simple_arithmetical.
        rewrite val.
        destruct x as [u [l [j [p t]]]].
        reduce_ro_access.
        replace (2 * 1) with 2 by ring.
        unfold Rdiv.
        ring.
      }

      {
        (* conditional *)
        apply (pp_rw_cond_tot_util
                 (fun y (δγ : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  =>
                    let x := fst (fst_app δγ) in 
                    (y = true -> 0 < sin x) /\ (y= false -> sin x < 0))).
        {
          (* branch condition *)
          apply (pp_ro_real_comp_lt_tot_util
                   (fun y _ => y = 0)
                   (fun y (δγ : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  =>
                      let x := fst (fst_app δγ) in 
                      y = sin x)).
          
          proves_simple_arithmetical.

          assert (((REAL :: REAL :: REAL :: INTEGER :: nil) ++ INTEGER :: nil) |- VAR 0 : REAL) by auto_typing. 
          pose proof (clerical_sine_correct ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ INTEGER :: nil) 0 H).
          apply (pp_ro_imply_tot X).
          intros h1 h2.
          auto.
          intros h1 h2 h3.
          rewrite h3.
          destruct h2.
          rewrite tedious_equiv_2_fst.
          simpl.
          reduce_ro_access.
          reflexivity.

          intros.
          destruct x.
          rewrite tedious_equiv_2_fst.
          simpl.
          destruct s0 as [u [l [j [p t]]]].
          unfold ro_to_rw_pre, rw_to_ro_pre in H.
          simpl in H.
          destruct H as [[h1 h2] [h3 h4]].
          rewrite h3, h4; clear h3 h4.
          destruct h2.
          unfold ϕ in H; simpl in H.
          simpl in H0.
          destruct H as [h3 [h4 h5]].
          (* prove that the mid point cannot be a root of sin(x) *)
          assert (0 <> sin s).
          {
            assert (is_rational s).
            {
              rewrite h1; apply ratoinals_midpoint_is_rational; auto.
            }
            assert (3 < s < 4).
            {
              assert (l < u) by lra.
              pose proof (midpoint_in_interval l u H1).
              rewrite <- h1 in H2.
              lra.
            }
            intro.
            pose proof (PI_unique_in_34 _ H1 (eq_sym H2)).
            rewrite H3 in H.
            contradict (PI_irrational H).
          }
          repeat split; auto.
          
          intro.
          apply Rltb''_prop in H1; auto.
          intro.
          apply Rltb''_prop_false in H1.
          destruct H1; auto.
          rewrite H1 in H.
          contradict H; auto.
        }

        {
          (* first branch *)
          assert (assignable (REAL :: REAL :: REAL :: INTEGER :: nil) REAL 2) as a by repeat constructor.
          apply (pp_rw_assign_tot_util REAL
                   (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  => y = fst x)) a).
          
          proves_simple_arithmetical.
          rewrite val; reduce_ro_access; auto.

          intros x' [p t]  [x [u [l [k t']]]] [[h1 h2] [h3 h4]] eqn.
          simpl in h1, h2, h3, h4, eqn.
          simpl.
          reduce_update.
          induction eqn.
          destruct h2 as [[q1 [q2 q3]] [p1 p2]].
          simpl in q1, q2, q3, p1, p2.
          assert (l < u) by lra.
          pose proof (midpoint_in_interval l u H).
          rewrite <- h1 in H0.
          repeat split; auto; try lra.
          rewrite h1; apply ratoinals_midpoint_is_rational; auto.
          assert (3 < x' < 4) by lra.
          apply (PI_simple_in_34 _ H1).
          auto.
          destruct q3 as [q31 [q32 [q33 q34]]].
          rewrite h1.
          field_simplify.
          rewrite q34.
          rewrite pow2_minus_one.
          apply lp.
          ring.
        }

        {
          (* second branch *)
          assert (assignable (REAL :: REAL :: REAL :: INTEGER :: nil) REAL 1) as a by repeat constructor.
          apply (pp_rw_assign_tot_util REAL
                   (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  => y = fst x)) a).
          
          proves_simple_arithmetical.
          rewrite val; reduce_ro_access; auto.

          intros x' [p t]  [x [u [l [k t']]]] [[h1 h2] [h3 h4]] eqn.
          simpl in h1, h2, h3, h4, eqn.
          simpl.
          reduce_update.
          induction eqn.
          destruct h2 as [[q1 [q2 q3]] [p1 p2]].
          simpl in q1, q2, q3, p1, p2.
          assert (l < u) by lra.
          pose proof (midpoint_in_interval l u H).
          rewrite <- h1 in H0.
          repeat split; auto; try lra.
          rewrite h1; apply ratoinals_midpoint_is_rational; auto.
          assert (3 < x' < 4) by lra.
          apply (PI_simple_in_34 _ H1).
          auto.
          destruct q3 as [q31 [q32 [q33 q34]]].
          rewrite h1.
          field_simplify.
          replace (-l + u) with (u - l) by ring.
          rewrite q34.
          rewrite pow2_minus_one.
          apply lp.
          ring.
        }
      }
      {
        (* after the local variable creatation, increase the counter *)
        assert (assignable (REAL :: REAL :: INTEGER :: nil) INTEGER 2) as a by repeat constructor.
        apply (pp_rw_assign_tot_util INTEGER
                 (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)))  => y = fst (snd (snd x)) + 1)%Z) a).
        
        proves_simple_arithmetical.
        rewrite val; reduce_ro_access; auto.

        intros k' [p t]  [u [l [k t']]] [h1 [h2 [h3 [[h4 h4'] [h5 h6]]]]] eqn.
        simpl in h1, h2, h3, eqn, h4, h5, h6.
        simpl.
        reduce_update.
        rewrite eqn.
        repeat split; simpl; auto.
      }
    }
    {
      (* loop invariant *)
      apply (pp_rw_sequence_tot
               (θ := fun _
                         (δγ : sem_ro_ctx (REAL :: REAL :: INTEGER :: nil) * sem_ro_ctx ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil)))  => 

                       let p := fst (fst_app (snd δγ)) in
                       let k := fst (snd (snd (fst δγ))) in
                       let l := fst (snd (fst δγ)) in
                       let u := fst (fst δγ) in 

                       let k' := fst (snd (snd (snd_app (snd δγ)))) in
                       let l' := fst (snd (snd_app (snd δγ))) in
                       let u' := fst (snd_app (snd δγ)) in 

                       (k < p /\ k = k')%Z)).
      
      apply (pp_rw_new_var_tot_util2 REAL
               (fun y (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil))))  => 
                  
                  let p := fst (fst_app (snd_app δγ)) in
                  let k := fst (snd (snd (fst_app δγ))) in
                  let l := fst (snd (fst_app δγ)) in
                  let u := fst (fst_app δγ) in 
                  
                  let k' := fst (snd (snd (snd_app (snd_app δγ)))) in
                  let l' := fst (snd (snd_app (snd_app δγ))) in
                  let u' := fst (snd_app (snd_app δγ)) in
                  
                  y = (l + u) / 2)).
      
      {
        (* assigned expression *)
        proves_simple_arithmetical.
        rewrite val.
        destruct x as [u [l [j [p t]]]].
        reduce_ro_access.
        replace (2 * 1) with 2 by ring.
        unfold Rdiv.
        ring.
      }

      {
        (* conditional *)
        apply (pp_rw_cond_tot_util
                 (fun y (δγ : sem_ro_ctx ((REAL ::REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ ( REAL :: REAL :: INTEGER :: nil))))  => 
                  let p := fst (fst_app (snd_app δγ)) in

                  let k := fst (snd (snd (snd (fst_app δγ)))) in
                  let l := fst (snd (snd (fst_app δγ))) in
                  let u := fst (snd (fst_app δγ)) in 
                  let x := fst (fst_app δγ) in 
                  
                  let k' := fst (snd (snd (snd_app (snd_app δγ)))) in
                  let l' := fst (snd (snd_app (snd_app δγ))) in
                  let u' := fst (snd_app (snd_app δγ)) in
                  
                  (y = true -> 0 < sin x) /\ (y= false -> sin x < 0))).
        {
          (* branch condition *)
          apply (pp_ro_real_comp_lt_tot_util
                   (fun y _ => y = 0)
                   (fun y (δγ : sem_ro_ctx ((REAL ::REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ ( REAL :: REAL :: INTEGER :: nil))))  => 
                  let p := fst (fst_app (snd_app δγ)) in

                  let k := fst (snd (snd (snd (fst_app δγ)))) in
                  let l := fst (snd (snd (fst_app δγ))) in
                  let u := fst (snd (fst_app δγ)) in 
                  let x := fst (fst_app δγ) in 
                  
                  let k' := fst (snd (snd (snd_app (snd_app δγ)))) in
                  let l' := fst (snd (snd_app (snd_app δγ))) in
                  let u' := fst (snd_app (snd_app δγ)) in
                  
                  y = sin x)).
          
          proves_simple_arithmetical.

          assert ((((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil) ++ REAL :: REAL :: INTEGER :: nil) |- VAR 0 : REAL)) by auto_typing. 
          pose proof (clerical_sine_correct _ 0 H).
          apply (pp_ro_imply_tot X).
          intros h1 h2.
          auto.
          intros h1 h2 h3.
          rewrite h3.
          destruct h2.
          rewrite tedious_equiv_2_fst.
          simpl.
          reduce_ro_access.
          reflexivity.

          intros.
          destruct x.
          rewrite tedious_equiv_2_fst.
          simpl.
          destruct s0 as [u [l [j [p [u' [l' [j' t]]]]]]].
          unfold ro_to_rw_pre, rw_to_ro_pre in H; simpl in H.
          destruct H as [[h1 h2] [h3 h4]].
          rewrite h3, h4; clear h3 h4.
          destruct h2.
          destruct H.
          unfold ϕ in H; simpl in H.
          simpl in H1.
          destruct H as [h3 [h4 h5]].
          (* prove that the mid point cannot be a root of sin(x) *)
          assert (0 <> sin s).
          {
            assert (is_rational s).
            {
              rewrite h1; apply ratoinals_midpoint_is_rational; auto.
            }
            assert (3 < s < 4).
            {
              assert (l < u) by lra.
              pose proof (midpoint_in_interval l u H2).
              rewrite <- h1 in H3.
              lra.
            }
            intro.
            pose proof (PI_unique_in_34 _ H2 (eq_sym H3)).
            rewrite H4 in H.
            contradict (PI_irrational H).
          }
          repeat split; auto.
          
          intro.
          apply Rltb''_prop in H2; auto.
          intro.
          apply Rltb''_prop_false in H2.
          destruct H2; auto.
          rewrite H2 in H.
          contradict H; auto.
        }

        {
          (* first branch *)
          assert (assignable (REAL :: REAL :: REAL :: INTEGER :: nil) REAL 2) as a by repeat constructor.
          apply (pp_rw_assign_tot_util REAL
                   (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil ++ _)))  => y = fst x)) a).
          
          proves_simple_arithmetical.
          rewrite val; reduce_ro_access; auto.

          intros x' [p [u' [l' [j' t]]]]  [x [u [l [k t']]]] [[h1 h2] [h3 h4]] eqn.
          simpl in h1, h2, h3, h4, eqn.
          simpl.
          reduce_update.
          induction eqn.
          unfold ro_to_rw_pre in h2.
          repeat rewrite tedious_equiv_2_fst, tedious_equiv_2_snd in h2.
          simpl in h2.
          destruct h2.
          unfold snd_app in H0.
          simpl in H0.
          split.
          destruct H as  [_ [H _]].
          simpl in H.
          apply H; auto.
          injection H0; intros; auto.
        }

        {
          (* second branch *)
          assert (assignable (REAL :: REAL :: REAL :: INTEGER :: nil) REAL 1) as a by repeat constructor.
          apply (pp_rw_assign_tot_util REAL
                   (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil ++ _)))  => y = fst x)) a).
          
          proves_simple_arithmetical.
          rewrite val; reduce_ro_access; auto.

          intros x' [p [u' [l' [j' t]]]]  [x [u [l [k t']]]] [[h1 h2] [h3 h4]] eqn.
          simpl in h1, h2, h3, h4, eqn.
          simpl.
          reduce_update.
          induction eqn.
          unfold ro_to_rw_pre in h2.
          repeat rewrite tedious_equiv_2_fst, tedious_equiv_2_snd in h2.
          simpl in h2.
          destruct h2.
          unfold snd_app in H0.
          simpl in H0.
          split.
          destruct H as  [_ [H _]].
          simpl in H.
          apply H; auto.
          injection H0; intros; auto.        
        }
      }
               
      {
        (* after the local variable creatation, increase the counter *)
        assert (assignable (REAL :: REAL :: INTEGER :: nil) INTEGER 2) as a by repeat constructor.
        apply (pp_rw_assign_tot_util INTEGER
                 (θ := (fun y (x : sem_ro_ctx ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil ++ _)))  => y = fst (snd (snd x)) + 1)%Z) a).
        
        proves_simple_arithmetical.
        rewrite val; reduce_ro_access; auto.

        intros k' [p t]  [u [l [k t']]] [h1 h2] eqn.
        simpl in h1, h2, eqn.
        simpl.
        reduce_update.
        rewrite eqn.
        rewrite h2.
        repeat split; simpl; auto.
        rewrite <- h2.
        auto.
      }

    }

    {
      (* loop invariant is wellfounded *)
      intros [u0 [l0 [k0 t']]] [p t] [h1 [h2 h3]] .
      simpl in h1, h2, h3.
      intros [f [p1 p2]].
      assert (k0 < p)%Z.
      {
        pose proof (p2 O).
        destruct H.
        simpl in H0.
        rewrite p1 in H0.
        repeat rewrite tedious_equiv_2_snd in H0.
        simpl in H0.
        exact H0.
      }
      assert (forall n : nat,
                 fst (snd (snd (f n))) = k0 + Z.of_nat n)%Z.
      {
        intro.
        induction n.
        rewrite p1 ; simpl.
        rewrite Z.add_0_r.
        reflexivity.
        destruct (p2 n) as [h _].
        simpl in h.
        simpl.
        simpl in h.
        rewrite h.
        repeat rewrite tedious_equiv_2_snd.
        simpl.
        unfold snd_app; simpl.
        simpl in IHn; rewrite IHn.
        lia.
      }
      
      pose proof (p2 (Z.to_nat (p - k0))).
      destruct H1 as [_ H1].      
      simpl in H1.
      repeat rewrite tedious_equiv_2_snd in H1.
      simpl in H1.
      unfold snd_app in H1; simpl in H1.
      rewrite H0 in H1.
      assert (0 <= p - k0)%Z by lia.
      rewrite (Z2Nat.id _ H2) in H1.
      lia.
    }
    
    {
      (* loop variant holds when enterring the loop *)

      intros [[u [l [k t]]] [p tt]] [h1 [h2 [h3 _]]] .
      simpl in h1, h2, h3.
      rewrite h1, h2, h3.
      repeat split; simpl; auto; try lia; try ring.
      apply Z_is_rational.
      apply Z_is_rational.
      right; auto.
      apply PI_in_34.
      apply PI_in_34.
      right; auto.
    }
    
    {
      (* loop exiting situation satisfies the desired postcondition of the loop *)
      intros _ [[u [l [k t]]] [p tt]] [h3 h4].
      simpl.
      destruct h3 as [h1 [h2 h3]]; simpl in h1, h2, h3.
      destruct h4 as [_ [_ h4]].
      simpl in h4.
      assert (p <= k)%Z.
      {
        destruct (Z.le_gt_cases p k); auto.
        pose proof (h4 H).
        discriminate H0.
      }
      clear h4.
      assert (Rabs (PI - (l + u) / 2) < pow2 (- k)).
      assert (l < u) by lra.
      assert (l < PI < u) by lra.
      assert (l < (l + u) /2 < u) by (apply midpoint_in_interval; auto).
      destruct h3 as [_ [_ [_ h3]]].
      rewrite <- h3.
      apply dist_between_points_in_interval; auto.
      assert (pow2 (- k) <= pow2 (- p)) by (apply pow2_monotone; lia).
      lra.
    }
    
  }
  
  {
    
    (* the final return value (l + u) / 2 is a valid approx.   *)
    proves_simple_arithmetical.
    
    rewrite <- Rabs_Ropp.
    replace (- (y - PI)) with (PI - y) by ring.
    rewrite val.
    reduce_ro_access.
    replace (2 * 1) with 2 by ring.
    destruct x as [u [l [j [p t]]]].
    simpl.
    simpl in pre.
    exact pre.
  }
  
Defined.
