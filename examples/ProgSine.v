From Clerical Require Import Clerical.

Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List Lia.
Open Scope R.

From Examples Require Import ProgAbs.
From Examples Require Import Mathematics.

(*
  The specifications of our sine function rely on the theory
  of trigonometric functions in Coq Standard library:

  - sin : R -> R is the sin function
  - sin_n := fun n => (-1) ^ n / INR (fact (2 * n + 1)) : nat -> R
      is the coefficient of the taylor expansion:
      sin x = infinite_sum n => infty. (sin_n n) * x^n  *)

(*
  x : Var k 

  Lim m.

  x : Var (1 + k) | m : Var 0

  Newvar j := 0 in

  x : Var (2 + k) | m : Var 1 | j : Var 0

  Newvar A := x in

  x : Var (3 + k) | m : Var 2 | j : Var 1 | A : Var 0

  Newvar q := - x³ / 6 in

  x : Var (4 + k) | m : Var 3 | j : Var 2 | A : Var 1 | q : Var 0

  * A = A(j, x) /\ q = q (j + 1, x)

  While ¬ bounded q δ
  do
    j := j + 1
    A := A + q
    q := - q * x * x / (2 j + 2) (2 j  + 3) 
  End; A
 *)

(* compute sine(VAR k) *)
Definition clerical_sin k :=
  Lim
    (
      NEWVAR INT 0 IN
      NEWVAR VAR (2 + k) IN
      NEWVAR ;-; VAR (3 + k) ;*; VAR (3 + k) ;*; VAR (3 + k) ;/; RE (INT 6) IN
      WHILE
        CASE EXP (:-: (VAR 3) :-: (INT 1)) ;<; clerical_abs 0 ==> TRUE | clerical_abs 0 ;<; EXP (:-: (VAR 3)) ==> FALSE END
      DO
        LET 2 := VAR 2 :+: INT 1 ;;
        LET 1 := VAR 1 ;+; VAR 0 ;;
        LET 0 := ;-; VAR 0 ;*; VAR (4 + k) ;*; VAR (4 + k) ;/; (RE (INT 2 :*: VAR 2 :+: INT 2)) ;/; (RE (INT 2 :*: VAR 2 :+: INT 3))
      END ;; VAR 1
    ).

      
Lemma clerical_sin_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    [x : Γ] |- {{True}} clerical_sin k {{y : REAL | y = sin (var_access Γ k REAL w x) }}ᵗ.
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun x => sin (var_access Γ k REAL w x)));
    try (intros [h1 h2] [_ h3]; auto; fail).

  apply (pp_ro_rw_tot_back).

  (* (* assert (((Γ ::: INTEGER) +++ nil) |- VAR 0 : INTEGER) as w' by auto_typing. *) *)
  (* apply (pp_rw_new_var_tot_util2 INTEGER (fun '(x, y) => y = 0%Z)). *)
  (* { *)
  (*   (* prove the assigned expression [EXP (:-: (VAR 0))] *) *)
  (*   proves_simple_arithmetical. *)
  (*   reduce_var_access val; reduce_var_access; exact val. *)
  (* } *)
  (* (* prove the rest *) *)
  apply (pp_rw_new_var_tot_util2 INTEGER (fun '(x, y) => y = 0%Z)).
  {
    (* prove the assigned expression [INT 0] *)
    prove_arith.
  }
  (* prove the rest *)
    
  assert ((( Γ ::: INTEGER) +++ (nil ::: INTEGER)) |- VAR (2 + k) : REAL) as w'' by auto_typing.
  apply (pp_rw_new_var_tot_util2 REAL (fun '(x, y) => y = var_access _ _ _ w'' x)).
  {
    (* prove the assigned expression [VAR (3 + k)] *)
    prove_arith.
    rewrite (var_access_typing_irrl _ _ _ w'' tmp1).
    exact val.
  }
  (* prove the rest *)
  
  assert (((REAL :: INTEGER ::  nil)  ++  (INTEGER :: Γ)) |- VAR (3 + k) : REAL) as w''' by auto_typing.
  apply (pp_rw_new_var_tot_util2 REAL (fun '(x, y) => y = sin_q 1 (var_access _ _ _ w''' x))).
  {
    (* prove the assigned expression [;-; VAR (3 + k) ;*; VAR (3 + k) ;*; VAR (3 + k) ;/; RE (INT 6)] *)
    prove_arith.
    simpl.
    destruct y as [[[γ m] j] A].
    simpl in pre, val.
    rewrite val.
    rewrite (var_access_typing_irrl _ _ _  h6 w''').
    rewrite (var_access_typing_irrl _ _ _  h4 w''').
    rewrite (var_access_typing_irrl _ _ _  h2 w''').
    unfold Rdiv.
    repeat rewrite Rmult_assoc. 
    rewrite <- Rinv_mult.
    replace ((1 + 1 + 1) * (1 + 1)) with 6 by ring.
    ring.
  }
  (* prove the rest *)

  apply (pp_rw_sequence_tot
           (θ := [γ : (INTEGER :: Γ) ;;; δ : (REAL :: REAL :: INTEGER :: nil)] ||-
                 {{_ : UNIT | let A := snd (fst δ) in
                   Rabs (A - sin (var_access Γ k REAL w (fst γ))) < pow2 (- snd γ) }} )).

  pose (ϕ := [(γ, m) : (INTEGER :: Γ) ;;; (((_, j), A), q) : (REAL :: REAL :: INTEGER :: nil)] ||-
             {{
                let x := var_access _ _ _ w γ in
                exists n : nat,
                  Z.of_nat n = j /\  q = sin_q (S n) x /\ A = sin_A n x}}).
  
  pose (θ := [ ((((γ, m), j), A), q) : ((REAL :: REAL :: INTEGER :: nil) ++ (INTEGER :: Γ))]
               |- {{y : BOOL | (y = true -> pow2 (- m - 1) < Rabs q) /\ (y = false -> Rabs q < pow2 (- m) )}}).

  pose (ψ := [ (γ', m) : ((INTEGER :: Γ) ++  (REAL :: REAL :: INTEGER :: nil)) ;;;
              (((_, j), A), q) : (REAL :: REAL :: INTEGER :: nil)] ||-
               {{let j' := snd (fst (fst (fst_app γ'))) in
                 let x := var_access _ _ _ w (snd_app γ') in
                 exists n : nat,
                   Z.of_nat n = j' /\ 
                     (j = j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)}}).

  apply (pp_rw_while_tot_back_util ϕ θ ψ).                
  {
    (* proving loop condition θ *)
    clear ψ w'' w'''.
    assert (((Γ ::: INTEGER) +++ (nil ::: INTEGER ::: REAL ::: REAL)) |- VAR 3 : INTEGER) as w3 by auto_typing.
    assert (((Γ ::: INTEGER) +++ (nil ::: INTEGER ::: REAL ::: REAL)) |- VAR 0 : REAL) as w0 by auto_typing.
    apply (pp_ro_rw_tot_back).
    apply (pp_rw_case_tot
           (θ1 := (fun '(x, b) => b = true ->
                                  pow2 (- (var_access _ _ _ w3 (fst_app x)) - 1) <
                                    Rabs (var_access _ _ _ w0 (fst_app x))))
           (θ2 := (fun '(x, b) => b = true ->
                                  Rabs (var_access _ _ _ w0 (fst_app x)) <
                                    pow2 (- (var_access _ _ _ w3 (fst_app x)))))
           (ϕ1 := (fun x => 
                     pow2 (- (var_access _ _ _ w3 (fst_app x)) - 1) <
                       Rabs (var_access _ _ _ w0 (fst_app x))))
           (ϕ2 := (fun x => 
                     Rabs (var_access _ _ _ w0 (fst_app x)) <
                       pow2 (- (var_access _ _ _ w3 (fst_app x)))))); simpl.
  {
    apply (pp_ro_real_comp_lt_prt
             (fun '(x, y) => y = pow2 (- (var_access _ _ _ w3 ( x)) - 1))
             (fun '(x, y) => y = Rabs (var_access _ _ _ w0 ( x)))).
    

    prove_arith.
    rewrite val.
    rewrite (var_access_typing_irrl _ _ _ h2 w3).
    auto.
    

    {
      apply (pp_ro_imply_prt
               (ψ := patf)
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ w0))).
      intros h1 h2; auto.
      intros [h1 h2] h3; auto.
    }

    intros.
    apply (proj1 (Rltb''_prop _ _)) in H2.
    reduce_tedious.
    simpl in H.
    simpl in H0.
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }
  
  {

    apply (pp_ro_real_comp_lt_prt
             (fun '(x, y) => y = Rabs (var_access _ _ _ w0 ( x)))
             (fun '(x, y) => y = pow2 (- (var_access _ _ _ w3 ( x))))).
    {
      apply (pp_ro_imply_prt
               (ψ := patf)
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ w0))).
      intros h1 h2; auto.
      intros [h1 h2] h3; auto.
    }

    
    prove_arith.
    rewrite val.
    rewrite (var_access_typing_irrl _ _ _ h0 w3).
    auto.

    intros.
    apply (proj1 (Rltb''_prop _ _)) in H2.
    reduce_tedious.
    simpl in H.
    simpl in H0.
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }

  {
    prove_arith.
    destruct y as [[[[t1 m] t2] t3] q].
    split; intro h.
    pose proof (pre (eq_refl _)).
    reduce_var_access H.
    exact H.
    rewrite val in h; contradict h; discriminate.
  }

  {
    prove_arith.
    destruct y as [[[[t1 m] t2] t3] q].
    split; intro h.
    rewrite val in h; contradict h; discriminate.
    pose proof (pre (eq_refl _)).
    reduce_var_access H.
    exact H.
  }

  {
    apply (pp_ro_real_comp_lt_tot
             (fun '(x, y) => y = pow2 (- (var_access _ _ _ w3 x) - 1) /\ pow2 (- (var_access _ _ _ w3 x) - 1) < Rabs (var_access _ _ _ w0 x))
             (fun '(x, y) => y = Rabs (var_access _ _ _ w0 x))).
    {
      prove_arith.
      rewrite val.
      split.
      rewrite (var_access_typing_irrl _ _ _ h2 w3).
      auto.
      exact pre.
    }
      apply (pp_ro_imply_tot (ψ := patf)
               (pp_ro_tot_pose_readonly (ψ := patf)
                  (fun x => pow2 (- (var_access _ _ _ w3 x) - 1) < Rabs (var_access _ _ _ w0 x)) 
                  (clerical_abs_correct _ _ w0))).
      intros h1 h2; split; auto.
      intros [h1 h2] h3; auto.
    destruct h3.
    auto.
    intros.
    destruct H.
    rewrite <- H in H1; rewrite <- H0 in H1.
    split.
    lra.
    apply Rltb''_prop.
    exact H1.   
  }

  {
    apply (pp_ro_real_comp_lt_tot
             (fun '(x, y) => y = Rabs (var_access _ _ _ w0 x) /\ Rabs (var_access _ _ _ w0 x) < pow2 (- (var_access _ _ _ w3 x)))
             (fun '(x, y) => y = pow2 (- (var_access _ _ _ w3 x)) )).

    apply (pp_ro_imply_tot (ψ := patf)
             (pp_ro_tot_pose_readonly (ψ := patf)
                (fun x => Rabs (var_access _ _ _ w0 x) < pow2 (- (var_access _ _ _ w3 x))) 
                (clerical_abs_correct _ _ w0))).
    intros h1 h2; split; auto.
    intros [h1 h2] h3; auto.
    prove_arith.
    rewrite val.
    rewrite (var_access_typing_irrl _ _ _ h0 w3).
    auto.

    intros.
    destruct H.
    rewrite <- H in H1; rewrite <- H0 in H1.
    split.
    lra.
    apply Rltb''_prop.
    exact H1.
  }
  
  {
    intros.
    apply overlap_splitting.
    apply pow2_increasing.
    lia.
  }

  }
  {
    (* proving loop invariant ϕ *)
      apply (pp_rw_sequence_tot
            (θ := [(γ, m) : (INTEGER :: Γ) ;;; (((_, j), A), q) : (REAL :: REAL :: INTEGER :: nil)] ||-
            {{_ : UNIT |  let x := var_access _ _ _ w γ in
                          exists n : nat,
                            Z.of_nat n = (j - 1)%Z /\
                               q = sin_q (S n) x /\ A = sin_A n x}})).
      {
        (* j := j + 1 *)
        proves_assign_simple_arithemtical INTEGER.
        intros [γ m] [[[t j] A] q].
        reduce_update.
        reduce_var_access.
        intros [[l [p1 [p2 p4]]] [h1 h2]].
        exists l.
        repeat split; auto.
        rewrite p1.
        ring.
      }
      
      apply (pp_rw_sequence_tot
             (θ := [(γ, m) : (INTEGER :: Γ) ;;; (((_, j), A), q)  : (REAL :: REAL :: INTEGER :: nil)] ||-
                   {{_ : UNIT | 
                    let x := var_access _ _ _ w γ in
                    exists n : nat,
                      Z.of_nat n = (j - 1)%Z /\ q = sin_q (S n) x /\ A = sin_A (S n) x}})).
      {
        (* A := A + q *)
        proves_assign_simple_arithemtical REAL.
        intros [γ m] [[[t j] A] q] [l [p1 [p2 p4]]].
        reduce_update.
        reduce_var_access.
        exists l.
        repeat split; auto.
        rewrite <- p2.
        rewrite <- p4.
        ring.
      }

      {
        (* q := - q * x * x / (2 j + 2) (2 j  + 3)  *)
        proves_assign_simple_arithemtical REAL.

        {
          (* safety condition for evaluating the assigned expression *)
          intros [[[[γ m] j] A] q] [l [p1 [p2 p3]]].
          reduce_var_access.
          repeat split; auto.
          (* prove 2 j + 2 ≠ 0 *)
          enough (IZR (2 * j + 2) <> 0) by auto.
          apply not_0_IZR.
          pose proof (Zle_0_nat l).
          assert (0 < j)%Z by lia.
          lia.
          
          (* prove 2 j + 3 ≠ 0 *)
          enough (IZR (2 * j + 3) <> 0) by auto.
          apply not_0_IZR.
          pose proof (Zle_0_nat l).
          assert (0 < j)%Z by lia.
          lia.
        }
        
        {
          (* condition for the assigned value *)
          intros [γ m] [[[t j] A] q] [l [p1 [p2 p3]]].
          reduce_update.
          reduce_var_access.
          exists (S l).
          repeat split; auto.
          lia.
          rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse ( h4))))) w).
          rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse ( h6))))) w).
          rewrite p2.
          simpl.
          field_simplify.
          repeat apply lp.
          repeat rewrite Rmult_assoc.
          repeat apply lp.
          replace ((l + S (l + 0) + 3)%nat) with (S (l + S (l + 0) + 2)%nat) by ring.
          replace (l + S (l + 0) + 2)%nat with (S (l + S (l + 0) + 1)%nat) by ring.
          replace 1 with (INR 1) by auto.
          repeat rewrite INR_IZR_INZ.
          repeat rewrite <- plus_IZR.
          repeat rewrite <- mult_IZR.
          apply lp.
          replace (match j with
                   | 0 => 0
                   | Z.pos y' => Z.pos y'~0
                   | Z.neg y' => Z.neg y'~0
                   end )%Z with (2 * j)%Z by auto.
          lia.

          repeat split.
          apply not_0_INR; lia.
          apply not_0_INR; lia.
          replace ((l + S (l + 0) + 3)%nat) with (S (l + S (l + 0) + 2)%nat) by ring.
          replace 1 with (INR 1) by auto.
          rewrite <- plus_INR.
          apply not_0_INR; lia.
          replace ((l + S (l + 0) + 2)%nat) with (S (l + S (l + 0) + 1)%nat) by ring.
          replace 1 with (INR 1) by auto.
          rewrite <- plus_INR.
          apply not_0_INR; lia.
        
          assert (0 < j)%Z.
          pose proof (Zle_0_nat l).
          lia.
          repeat split; auto.
          enough (IZR (2 * j + 3) <> 0) by auto.        
          apply not_0_IZR.
          lia.
          enough (IZR (2 * j + 2) <> 0) by auto.        
          apply not_0_IZR.
          lia.
          apply not_0_INR; lia.
          apply not_0_INR; lia.
        }
      }
  }
  {
    (* proving variant *)
    apply (pp_rw_sequence_tot
             (θ :=
                [(γ', m) : ((INTEGER :: Γ) ++ REAL :: REAL :: INTEGER :: nil) ;;;
                        (((_, j), A), q) : (REAL :: REAL :: INTEGER :: nil)]
                  ||- {{_ : UNIT | let j' := snd (fst (fst (fst_app γ'))) in
                                   let x := var_access Γ k REAL w (snd_app γ') in
                                   exists n : nat, Z.of_nat n = j' /\ j = (j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)}})).
    {
      (* j := j + 1 *)
      proves_assign_simple_arithemtical INTEGER.
      intros [γ' m] [[[t j] A] q].
      simpl.
      reduce_var_access.
      reduce_update.
      reduce_tedious.
      intros [[l [p1 [p2 p3]]]  [[h1 _] h2]].
      exists l.
      rewrite <- h2.
      simpl; repeat split; auto.
      rewrite <- p2.
      pose proof (h1 eq_refl) as h1.
      rewrite p2 in h1.
      replace (2 * 1) with 2 by ring.
      rewrite <- p2 in h1.
      simpl in h1.
      exact h1.      
    }
    
      
    apply (pp_rw_sequence_tot
               (θ :=
                [(γ', m) : ((INTEGER :: Γ) ++ REAL :: REAL :: INTEGER ::  nil) ;;;
                        (((_, j), A), q) : (REAL :: REAL :: INTEGER ::  nil)]
                  ||- {{_ : UNIT | let j' := snd (fst (fst (fst_app γ'))) in
                                   let x := var_access Γ k REAL w (snd_app γ') in
                     exists n : nat, Z.of_nat n = j' /\ j = (j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)}})).
    {
      (* A := A + q *)
      proves_assign_simple_arithemtical REAL.
      intros [γ' m] [[[t j] A] q].
      reduce_var_access.
      reduce_update.
      intros [l [p1 [p2 p3]]].
      exists l.
      rewrite <- p2.
      rewrite <- p1.
      simpl; repeat split; auto.
    }
    {
      (* q := - q * x * x / (2 j + 2) (2 j  + 3)  *)
      pose proof (has_type_ro_add_auxiliary _ _ _ w (REAL :: REAL :: INTEGER :: nil)).
      proves_assign_simple_arithemtical REAL.

      {
        intros [[[[γ' m] j] A] q].
        reduce_var_access.
        intros [l [p1 [p2 p3]]].
        repeat split; auto.
        enough (IZR (2 * j + 2) <> 0) by auto.
        apply not_0_IZR.
        pose proof (Zle_0_nat l).
        assert (0 < j)%Z by lia.
        lia.
        
        (* prove 2 j + 3 ≠ 0 *)
        enough (IZR (2 * j + 3) <> 0) by auto.
        apply not_0_IZR.
        pose proof (Zle_0_nat l).
        assert (0 < j)%Z by lia.
        lia.
      }
      
      intros [γ' m] [[[t j] A] q].
      reduce_update.
      intros [l [p1 [p2 p3]]].
      exists l.
      repeat split; auto.
    }
  }
  

  {
    (* ψ is well-founded *)
    intros.
    intro.
    destruct H0.
    destruct H0.
    destruct δ as [[[t j0] A0] q0].     
    assert (forall n,
               snd (fst (fst (x n))) = Z.of_nat n + j0)%Z.
    {
      intro.
      induction n.
      rewrite H0.
      simpl.
      auto.
      pose proof (H1 n).
      unfold ψ in H2.
      destruct γ.
      simpl in H2.
      destruct (x (S n)) as [[[tt j'] A'] q'].
      destruct H2.
      destruct H2.
      rewrite <- H2 in H3.
      reduce_tedious H2.
      rewrite H2 in H3.
      simpl in IHn.
      rewrite IHn in H3.
      rewrite Nat2Z.inj_succ.
      simpl.
      destruct H3.
      rewrite H3.      
      ring. 
    }

    
      
    destruct γ as [γ m].
    pose proof (Rconverge (var_access _ _ _ w γ) (m + 1)) as [l h].
    destruct H as [j0n [hj _]].
    simpl in hj.
    pose proof (H1 (l)%nat).
    simpl in H.
    destruct (x (S l)) as [[[tt j'] A'] q'].
    reduce_tedious H.
    destruct H.
    destruct H.
    destruct H3.
    simpl in h.
    rewrite H2 in H.
    rewrite <- hj in H.
    rewrite <- Nat2Z.inj_add in H.
    apply Nat2Z.inj in H.
    assert (l <= x0)%nat by lia.
    pose proof (h _ H5).
    replace (-(m+1))%Z with (-m-1)%Z in H6 by ring.
    exact (Rlt_asym _ _ H4 H6).
  }

  {
    (* enterring the loop; initial conditoin *)
    intros x.
    intros.
    destruct x.
    destruct s0 as [[[tt j'] A'] q'].
    simpl.
    destruct s.
    exists O.
    simpl.
    simpl in H.
    reduce_var_access H.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse
                                            (has_type_ro_Var_S_inverse ( (has_type_ro_Var_S_inverse w''')))) w) in H.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse ( (has_type_ro_Var_S_inverse w''))) w) in H.
    
    destruct H as [h1 [h2 [h3 h4]]].
    repeat split; auto.
  }

  {
    (* after exiting the loop *)

    
    intros [[γ m] [[[[t j] A] q] _]] [h1 h2]. 
    simpl.
    destruct h2 as [_ h3].
    pose proof (h3 eq_refl); clear h3.
    simpl in h1.
    destruct h1 as [l [t1 [t2 t4]]].
    rewrite t4.
    pose proof (Rtheorem l (var_access Γ k REAL w γ)).
    simpl in H0.
    rewrite <- t2 in H0.
    rewrite <- Rabs_Ropp.
    replace (- (sin_A l (var_access Γ k REAL w γ) - sin (var_access Γ k REAL w γ))) with
      (sin (var_access Γ k REAL w γ) - sin_A l (var_access Γ k REAL w γ)) by ring.
    apply (Rlt_trans _ _ _ H0 H).
  }

  
  prove_arith.
  rewrite val.
  clear val.
  destruct y as [[[[γ m] j] A] q].
  simpl.
  simpl in pre.
  reduce_var_access.
  exact pre.

Defined.

