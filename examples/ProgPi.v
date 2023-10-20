From Clerical Require Import Clerical.

Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra Lia List.
Open Scope R.
From Examples Require Import ProgAbs ProgSine.
From Examples Require Import Mathematics.

Definition clerical_pi :=
  Lim (
      NEWVAR INT 0 IN (* k *)
      NEWVAR RE (INT 3) IN (* l *)
      NEWVAR RE (INT 4) IN (* u *)
      WHILE VAR 2 :<: VAR 3 DO
        (NEWVAR (VAR 0 ;+; VAR 1) ;*; EXP (INT -1) IN
          IF RE (INT 0) ;<; clerical_sin 0
          THEN
            LET 2 := VAR 0
          ELSE
            LET 1 := VAR 0
                       END) ;; LET 2 := VAR 2 :+: INT 1 END ;; (VAR 1 ;+; VAR 0) ;*; EXP (INT -1)).

Lemma clerical_pi_correct :
  [_ : nil] |- {{True}} clerical_pi {{y : REAL | y = PI}}ᵗ.
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun _ => PI));
    try (intros [h1 h2] [_ h3]; auto; fail).

  apply pp_ro_rw_tot_back.
  
  apply (pp_rw_new_var_tot_util2 INTEGER (fun '(_, y) => y = 0%Z)).
  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot_util2 REAL (fun '(_, y) => y = 3)).
  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot_util2 REAL (fun '(_, y) => y = 4)).
  proves_simple_arithmetical.

  apply (pp_rw_sequence_tot
           (θ :=  [(_, p) : (INTEGER :: nil) ;;; (((_, k), l), u) : (REAL :: REAL :: INTEGER :: nil)] ||-
                   {{_ : UNIT | Rabs (PI - (l + u) / 2) < pow2 (- p)}})).
  {
    
    pose (ϕ := [(_, p) : (INTEGER :: nil) ;;; (((_, k), l), u) : (REAL :: REAL :: INTEGER :: nil)] ||-
               {{is_rational l /\ is_rational u /\ 3 <= l /\ l < PI < u /\ u <= 4 /\ u - l = pow2 (- k)}}).           

    pose (θ := [((((_, p), k), l), u) : ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)) ] |-
                 {{b : BOOL |  b = true <-> k < p}}%Z).
    
    pose (ψ := [ ((((_, k'), l'), u'), p) : ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil)) ;;;
                (((_, k), l), u) : (REAL :: REAL :: INTEGER :: nil)] ||-
                {{(k = k' + 1 /\ k' < p)%Z}}).                                              
    
    apply (pp_rw_while_tot_back_util ϕ θ ψ). 
    {
      (* loop condition *)
      proves_simple_arithmetical.
      destruct y as [[[[t p] j] l] u].
      simpl in pre.
      rewrite val.
      reduce_var_access.
      lia.      
    }

    {
      (* loop invariant *)
      apply (pp_rw_sequence_tot
               (θ := [(_, p) : (INTEGER :: nil) ;;; (((_, k), l), u) : (REAL :: REAL :: INTEGER :: nil)] ||-
                      {{_ : UNIT | is_rational l /\ is_rational u /\
                         3 <= l /\ l < PI < u /\ u <= 4 /\ u - l = pow2 (- (k + 1))}})).
      
      apply (pp_rw_new_var_tot_util2 _
             ([((((_, p), k), l), u) : ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)) ] |-
               {{y : REAL | y = (l + u) / 2}})).      
      {
        (* assigned expression *)
        proves_simple_arithmetical.
        rewrite val.
        destruct y as [[[[t p] j] l] u].
        reduce_var_access.
        replace (2 * 1) with 2 by ring.
        unfold Rdiv.
        ring.
      }

      {
        (* conditional *)
        apply (pp_rw_cond_tot_util
                 ([(((((_, p), k), l), u), x) : ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)) ] |-
                   {{y : BOOL | (y = true -> 0 < sin x) /\ (y = false -> sin x < 0)}})).
        {
          (* branch condition *)
          apply (pp_ro_real_comp_lt_tot_util
                   (fun '(_, y) => y = 0)
                   (fun '((δγ, y) : sem_ctx ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil)) * R )=>
                      let x := snd (snd_app δγ) in 
                      y = sin x)).
          
          proves_simple_arithmetical.

          assert (((REAL :: REAL :: REAL :: INTEGER :: nil) ++ INTEGER :: nil) |- VAR 0 : REAL) by auto_typing. 
          pose proof (clerical_sin_correct ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ INTEGER :: nil) 0 H).
          apply (pp_ro_imply_tot (ψ := patf) X).
          intros h1 h2; auto.
          intros [h1 h2] h3; auto.
          rewrite h3.
          destruct h1.
          reduce_var_access.
          reduce_tedious.          
          reflexivity.

          intros.
          destruct x as [[[[[t p] j] l] u] x].
          simpl in H. 
          destruct H as [[h1 h2] [h3 h4]].
          rewrite h3, h4; clear h3 h4.
          destruct h2.
          destruct H as [h3 [h4 h5]].
          (* prove that the mid point cannot be a root of sin(x) *)
          assert (0 <> sin x).
          {
            assert (is_rational x).
            {
              rewrite h1; apply ratoinals_midpoint_is_rational; auto.
            }
            assert (3 < x < 4).
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
          proves_assign_simple_arithemtical REAL.

          intros [tmp1 γ]  [[[[tmp2 k] l] u] x] [[h1 [h2 h3]] [h4 _]].
          reduce_update.
          reduce_var_access.
          destruct h2 as [p1 [p2 p3]].
          assert (l < u) by lra.
          pose proof (midpoint_in_interval l u H).
          rewrite <- h1 in H0.
          repeat split; auto; try lra.
          rewrite h1; apply ratoinals_midpoint_is_rational; auto.
          assert (3 < x < 4) by lra.
          apply (PI_simple_in_34 _ H1).
          auto.
          destruct p3 as [q31 [q32 [q33 q34]]].
          rewrite h1.
          field_simplify.
          rewrite q34.
          rewrite pow2_minus_one.
          apply lp.
          ring.
        }

        {
          (* second branch *)
          proves_assign_simple_arithemtical REAL.

          intros [tmp1 γ]  [[[[tmp2 k] l] u] x] [[h1 [h2 h3]] [_ h4]].
          reduce_update.
          reduce_var_access.
          destruct h2 as [p1 [p2 p3]].
          assert (l < u) by lra.
          pose proof (midpoint_in_interval l u H).
          rewrite <- h1 in H0.
          repeat split; auto; try lra.
          rewrite h1; apply ratoinals_midpoint_is_rational; auto.
          assert (3 < x < 4) by lra.
          apply (PI_simple_in_34 _ H1).
          auto.
          destruct p3 as [q31 [q32 [q33 q34]]].
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
        proves_assign_simple_arithemtical INTEGER.
        intros [tmp1 γ] [[[tmp2 k] l] u] h1.
        reduce_update; reduce_var_access; auto.
      }
    }
    {
      (* loop invariant *)
      apply (pp_rw_sequence_tot
               (θ := [ ((((_, k'), l'), u'), p) : ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil)) ;;;
                      (((_, k), l), u) : (REAL :: REAL :: INTEGER :: nil)] ||-
                      {{_ : UNIT | (k < p /\ k = k')%Z}})).
      
      apply (pp_rw_new_var_tot_util2 _
              ([(((((((_, k'), l'), u'), p), k), l), u) :
                  ((REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil)))] |-
                  {{y : REAL | y = (l + u) / 2}})).
      {
        (* assigned expression *)
        proves_simple_arithmetical.
        rewrite val.
        destruct y as [[[[[[[t k'] l'] u'] p] k] l] u].
        reduce_var_access.
        lra.
      }

      {
        (* conditional *)
        apply (pp_rw_cond_tot_util
                 ([((((((((_, k'), l'), u'), p), k), l), u), x) :
                  ((REAL :: REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ (REAL :: REAL :: INTEGER :: nil)))] |- {{y : BOOL | (y = true -> 0 < sin x) /\ (y= false -> sin x < 0)}})).
        {
          (* branch condition *)
          apply (pp_ro_real_comp_lt_tot_util
                   (fun '(_, y) => y = 0)
                   (fun '((δγ, y) :  sem_ctx ((REAL ::REAL :: REAL :: INTEGER :: nil) ++ ((INTEGER :: nil) ++ ( REAL :: REAL :: INTEGER :: nil))) * R)  => 
                      let x := snd (snd_app δγ) in                   
                      y = sin x)).
          
          proves_simple_arithmetical.

          assert ((((REAL :: REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: nil) ++ REAL :: REAL :: INTEGER :: nil) |- VAR 0 : REAL)) by auto_typing. 
          pose proof (clerical_sin_correct _ 0 H).
          apply (pp_ro_imply_tot (ψ := patf) X).
          intros h1 h2; auto.
          intros [h1 h2] h3.
          rewrite h3.
          destruct h1.
          reduce_var_access.
          reduce_tedious.
          reflexivity.

          intros.
          destruct x as [[[[[[[[t k'] l'] u'] p] k] l] u] x].
          simpl in H; destruct H as [[h1 h2] [h3 h4]].
          rewrite h3, h4; clear h3 h4.
          destruct h2 as [[h3 [h4 h5]] [h6 h7]].
          (* prove that the mid point cannot be a root of sin(x) *)
          assert (0 <> sin x).
          {
            assert (is_rational x).
            {
              rewrite h1; apply ratoinals_midpoint_is_rational; auto.
            }
            assert (3 < x < 4).
            {
              assert (l < u) by lra.
              pose proof (midpoint_in_interval l u H0).
              rewrite <- h1 in H1.
              lra.
            }
            intro.
            pose proof (PI_unique_in_34 _ H0 (eq_sym H1)).
            rewrite H2 in H.
            contradict (PI_irrational H).
          }
          repeat split; auto.
          
          intro.
          apply Rltb''_prop in H0; auto.
          intro.
          apply Rltb''_prop_false in H0.
          destruct H0; auto.
          rewrite H0 in H.
          contradict H; auto.
        }

        {
          (* first branch *)
          proves_assign_simple_arithemtical REAL.

          intros [[[[t j'] l'] u'] p] [[[[t' k] l] u] x] [h1 [h2 _]].
          reduce_tedious h1.
          reduce_update.
          destruct h1 as  [_ [_ [h3 h4]]].
          split.
          apply h3; auto.
          injection h4; intros; auto.
        }

        {
          proves_assign_simple_arithemtical REAL.

          intros [[[[t j'] l'] u'] p] [[[[t' k] l] u] x] [h1 [_ h2]].
          reduce_tedious h1.
          reduce_update.
          destruct h1 as  [_ [_ [h3 h4]]].
          split.
          apply h3; auto.
          injection h4; intros; auto.
        }
        
      }
               
      {
        (* after the local variable creatation, increase the counter *)
        proves_assign_simple_arithemtical INTEGER.


        intros [[[[t j'] l'] u'] p] [[[t' k] l] u] [h1 h2].
        reduce_update.
        reduce_var_access.
        rewrite <- h2; split; auto.
      }

    }

    {
      (* loop invariant is wellfounded *)
      intros [t p] [[[t' k0] l0] u0] [h1 [h2 h3]] .
      intros [f [p1 p2]].
      assert (k0 < p)%Z.
      {
        pose proof (p2 O).
        rewrite p1 in H.
        destruct (f 1)%nat as [[[t1' k1] l1] u1].
        simpl in H.
        destruct H; auto.
      }
      assert (forall n : nat,
                 snd (fst (fst (f n))) = k0 + Z.of_nat n)%Z.
      {
        intro n.
        induction n.
        rewrite p1 ; simpl.
        rewrite Z.add_0_r.
        reflexivity.
        pose proof (p2 n).
        destruct (f n)%nat as [[[tn' kn] ln] un].
        simpl in IHn, H0.
        destruct (f (S n))%nat as [[[tn'' kn'] ln'] un']. 
        simpl.
        rewrite (proj1 H0).
        rewrite IHn.
        lia.
      }
      
      pose proof (p2 (Z.to_nat (p - k0))).
      pose proof (H0 (Z.to_nat (p - k0))).
      destruct (f (Z.to_nat (p - k0)))%nat as [[[tn' kn] ln] un].
      destruct (f (S  (Z.to_nat (p - k0))))%nat as [[[tn'' kn'] ln'] un']. 
      simpl in H1, H2.
      destruct H1 as [_ H1].      
      assert (0 <= p - k0)%Z by lia.
      rewrite (Z2Nat.id _ H3) in H2.
      lia.
    }
    
    {
      (* loop variant holds when enterring the loop *)
      intros [[tmp1 γ] [[[t k] l] u] ] [h1 [h2 [h3 _]]] .
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
      
      intros [[tmp p] [[[[tmp2 k] l] u] _]] [h3 h4].
      simpl in h3, h4.
      destruct h3 as [h1 [h2 h3]]; simpl in h1, h2, h3.
      destruct h4 as [_ h4].
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

    destruct y as [[[[t p] k] l] u]. 
    simpl; simpl in pre.
    rewrite <- Rabs_Ropp.
    replace (- (x - PI)) with (PI - x) by ring.
    rewrite val.
    reduce_var_access.
    replace (2 * 1) with 2 by ring.
    exact pre.
  }
Defined.
