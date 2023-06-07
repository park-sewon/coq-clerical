From Clerical Require Import Clerical.

Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

From Examples Require Import abs bounded logic.
Print sin_n.
(*
  The specifications of our sine function rely on the theory
  of trigonometric functions in Coq Standard library:

  - sin : R -> R is the sin function
  - sin_n := fun n => (-1) ^ n / INR (fact (2 * n + 1)) : nat -> R
      is the coefficient of the taylor expansion:
      sin x = infinite_sum n => infty. (sin_n n) * x^n 
      
 *)

Search sin.
Search sin_approx.
Print sin_approx. 
Print sin.
Check exist_sin.
Print exist_sin.
Print sin_in.
Print infinite_sum.
Print sin_n.
Search sin_n.
Search exist_sin.

(* partial sum term *)
Fixpoint sin_q n x : R
  := match n with
     | O => x
     | S m => - x * x * (sin_q m x) / (INR (2 * m + 3)%nat) / (INR (2 * m + 2)%nat)
     end.

Fixpoint sin_A n x : R
  := match n with
     | O => x
     | S m => sin_q (S m) x + sin_A m x 
     end.

Lemma Rtheorem : forall n x,
    Rabs (sin x - sin_A n x) < sin_q (S n) x.
Proof.
Admitted.

Lemma Rconverge : forall x,
    forall n, exists m, Rabs (sin_q m x) < pow2 (- n).
Admitted.


(*
  x : k 

  Lim m.

  x : Var (1 + k)
  m : Var 0

  Newvar δ := 2⁻ᵐ in

  x : Var (2 + k)
  m : Var 1
  δ : Var 0

  Newvar j := 0 in

  x : Var (3 + k)
  m : Var 2
  δ : Var 1
  j : Var 0

  Newvar A := x in

  x : Var (4 + k)
  m : Var 3
  δ : Var 2
  j : Var 1
  A : Var 0

  Newvar q := x³ / 6 in

  x : Var (5 + k)
  m : Var 4
  δ : Var 3
  j : Var 2
  A : Var 1
  q : Var 0

  * A = A(j, x) /\ q = q (j + 1, x)

  While ¬ bounded q δ
  do
    j := j + 1
    A := A + q
    q := - q * x * x / (2 j + 2) (2 j  + 3) 
  End;

  A


 *)

(* compute sine(VAR k) *)
Definition exp_sine k :=
  Lim
    (
      NEWVAR EXP (:-: (VAR 0)) IN
      NEWVAR INT 0 IN
      NEWVAR VAR (3 + k) IN
      NEWVAR VAR (4 + k) ;*; VAR (4 + k) ;*; VAR (4 + k) ;/; RE (INT 6) IN
      WHILE
        clerical_neg (clerical_bounded 0 3)
      DO
        LET 2 := VAR 2 :+: INT 1 ;;
        LET 1 := VAR 1 ;+; VAR 0 ;;
        LET 0 := ;-; VAR 0 ;*; VAR (5 + k) ;*; VAR (5 + k) ;/; (RE (INT 2 :*: VAR 2 :+: INT 2)) ;/; (RE (INT 2 :*: VAR 2 :+: INT 3))
      END ;; VAR 1
    ).

Fixpoint has_type_ro_Var_S_inverse {Γ} {τ} {σ} {k} (w : (σ :: Γ) |- Var (S k) : τ) : Γ |- Var k : τ.
Proof.
  dependent destruction w.
  dependent destruction h.
  simpl in h.
  exact (has_type_ro_Var_S_inverse _ _ _ _ h).
  exact w.
Defined.  
        
Lemma reduce_ro_access_0 : forall Γ τ (w : (τ :: Γ) |- Var 0 : τ) x,
    ro_access _ _ _ w x = fst x.
Proof.
  intros.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_0 _ _)).
  destruct x; auto.
Defined.

Lemma reduce_ro_access_S : forall Γ τ σ n (w : (σ :: Γ) |- Var (S n) : τ) x,
    ro_access _ _ _ w x = ro_access _ _ _ (has_type_ro_Var_S_inverse w) (snd x).
Proof.
  intros.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_S _ _ _ _ (has_type_ro_Var_S_inverse w))).
  destruct x; auto.
Defined.

Ltac reduce_ro_access_tactic h :=
  match type of h with
  | ltac_No_arg =>
      repeat (simpl; try rewrite reduce_ro_access_S; try rewrite reduce_ro_access_0)
  | _ =>
      repeat (simpl in h; try rewrite reduce_ro_access_S in h; try rewrite reduce_ro_access_0 in h)
  end.

Tactic Notation "reduce_ro_access" constr(x1) :=
  reduce_ro_access_tactic x1 .
                    
Tactic Notation "reduce_ro_access" :=
  reduce_ro_access_tactic ltac_no_arg.


Lemma assignable_S_inverse {Γ} {τ} {σ} {k} (a : assignable (σ :: Γ) τ (S k)) :
  assignable Γ τ k.
Proof.
  dependent destruction a.
  exact a.
Defined.
  
Lemma reduce_update_0 : forall Δ τ (a : assignable (τ :: Δ) τ 0)
                                   (x y : sem_datatype τ) (δ : sem_ro_ctx Δ),
    @update τ (τ::Δ) 0 x (y, δ) a = (x, δ).
Proof.
  intros.
  rewrite (update_assignable_irrl 0 _ _ _ _ a (assignable_0 _ _)).
  auto.
Defined.

Lemma update_assignable_S : forall Δ σ k (a : assignable Δ σ k) τ x δ y,
    @update σ (τ :: Δ) (S k) x (y, δ) (assignable_S _ σ τ _ a)
    = (y, @update σ Δ k x δ a).
Proof.
  intros.
  simpl.
  unfold update.
  apply lp.
  auto.
  simpl.
  destruct a.
  simpl.
  auto.
  simpl.
  apply lp.
  auto.
Defined.

  
Lemma reduce_update_S : forall Δ k τ σ (a : assignable (τ :: Δ) σ (S k)) x y
                               (δ : sem_ro_ctx Δ),
    @update σ (τ :: Δ) (S k) x (y, δ) a
    = (y, @update σ Δ k x δ (assignable_S_inverse a)). 
Proof.
  intros.
  rewrite (update_assignable_irrl _ _ _ _ _ a
             (assignable_S _ _ _ _ ((assignable_S_inverse a)))).
  rewrite update_assignable_S.
  auto.
Defined.




Ltac reduce_update_tactic h :=
  match type of h with
  | ltac_No_arg =>
      repeat (simpl; try rewrite reduce_update_S; try rewrite reduce_update_0)
  | _ =>
      repeat (simpl in h; try rewrite reduce_update_S in h; try rewrite reduce_update_0 in h)
  end.

Tactic Notation "reduce_update" constr(x1) :=
  reduce_update_tactic x1 .
                    
Tactic Notation "reduce_update" :=
  reduce_update_tactic ltac_no_arg.




Lemma pp_rw_assign_tot_util {Γ Δ} {k} {e} τ {ϕ} {θ} {ψ : post} :
  forall (a : assignable Δ τ k),
    (Δ ++ Γ) |-- [{rw_to_ro_pre  ϕ}] e [{y : τ | θ y}] ->
    (forall x γ δ, ϕ (δ, γ) -> θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    Γ;;; Δ ||-- [{ϕ}] (LET k := e) [{y : UNIT | ψ y}].
Proof.
  intros.
  apply (pp_rw_assign_tot a
           (θ := θ /\\\ (fun _ => rw_to_ro_pre ϕ))).
  apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; split; auto.
  intros.
  apply H; destruct H0; auto.
  unfold rw_to_ro_pre in H1.
  rewrite tedious_equiv_0 in H1.
  exact H1.
Defined.

Lemma exp_sine_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    Γ |-- [{fun _ => True}]
          exp_sine k
          [{y : REAL | fun x => y = sin (ro_access Γ k REAL w x) }].
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun x =>  sin (ro_access Γ k REAL w x)));
    try (intros h1 h2 [_ h3]; auto; fail).

  apply (pp_ro_rw_tot_back).
  
  assert ((nil  ++  (INTEGER :: Γ)) |- VAR (0) : INTEGER) as w' by auto_typing.
  apply (pp_rw_new_var_tot
           (Γ := (INTEGER :: Γ))
           (Δ := nil)
           (σ := REAL)
           (θ := (fun y x => y = pow2 (- ro_access _ _ _ w' x)))).
  proves_simple_arithmetical.

  reduce_ro_access val; reduce_ro_access; exact val.
    
  apply (pp_rw_new_var_tot
           (σ := INTEGER)
           (θ := (fun y x => y = 0%Z))).
  proves_simple_arithmetical.

  assert (((INTEGER :: REAL :: nil)  ++  (INTEGER :: Γ)) |- VAR (3 + k) : REAL) as w'' by auto_typing.
  apply (pp_rw_new_var_tot
           (σ := REAL)
           (θ := (fun y x => y = ro_access _ _ _ w'' x))).
  proves_simple_arithmetical.
  rewrite (ro_access_typing_irrl _ _ _ w'' tmp1).
  exact val.
    
  assert (((REAL :: INTEGER :: REAL :: nil)  ++  (INTEGER :: Γ)) |- VAR (4 + k) : REAL) as w''' by auto_typing.
  apply (pp_rw_new_var_tot
           (σ := REAL)
           (θ := (fun y x => y = sin_q 1 (ro_access _ _ _ w''' x)))).

  proves_simple_arithmetical.
  repeat destruct x.
  repeat destruct p.
  simpl in y.
  simpl in pre.
  simpl in val.
  rewrite val.
  admit.

  

  clear w' w''.
  apply (pp_rw_sequence_tot
           (Γ := (INTEGER :: Γ))
           (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
           (θ :=
              fun _ δγ  => 
                let A := fst (snd (fst δγ)) in
                Rabs (A - sin (ro_access Γ k REAL w (snd (snd δγ)))) < pow2 (- fst (snd δγ)))).
  simpl.


  pose (ϕ :=
          fun δγ :
            sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx (INTEGER :: Γ)  
              =>
                let m := fst (snd δγ) in
                let x := ro_access _ _ _ w (snd (snd δγ)) in
                let q := fst (fst δγ) in
                let A := fst (snd (fst δγ)) in
                let j := fst (snd (snd (fst δγ))) in
                let δ := fst (snd (snd (snd (fst δγ)))) in
                exists n : nat,
                  Z.of_nat n = j /\
                    δ = pow2 (- m) /\ q = sin_q (S n) x /\ A = sin_A n x).

  pose (θ :=
          fun (y : bool) (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ))) =>
            let q := fst (fst_app δγ) in
            let δ := fst (snd (snd (snd (fst_app δγ)))) in
            ϕ (fst_app δγ, snd_app δγ) /\
              (y = true -> δ / 2 < Rabs q) /\ (y = false -> Rabs q < δ)).

  pose (ψ :=
          fun δγδ :   
                sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx ((INTEGER :: Γ) ++  (REAL :: REAL :: INTEGER :: REAL :: nil))
               =>
                 let m := fst (fst_app (snd δγδ)) in
                 let x := ro_access _ _ _ w (snd (fst_app (snd δγδ))) in
                 let j := fst (snd (snd (fst δγδ))) in
                 let j' := fst (snd (snd (snd_app (snd δγδ)))) in
                 exists n : nat,
                   Z.of_nat n = j' /\ 
                     (j = j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)).
  
  apply (pp_rw_while_tot_back
           (Γ := (INTEGER :: Γ))
           (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
           (θ := θ)
           (ϕ := ϕ)
           (ψ := ψ)).
                
  {
    (* proving condition part *)
    assert (wk : ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ INTEGER :: Γ) |- VAR 0 : REAL) by auto_typing.
    assert (wδ : ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ INTEGER :: Γ) |- VAR 3 : REAL) by auto_typing.
    pose proof (clerical_neg_correct_tot _ _ _ _  (clerical_bounded_correct  ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ INTEGER :: Γ) 0 3 wk wδ)).
    apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
    apply (pp_ro_imply_tot X).
    intros h1 h2; split; auto.
    destruct h2.
    destruct H.
    destruct H0.
    destruct h1 as [q [A [j [δ [m γ]]]]].
    simpl in H, H0, H1.
    reduce_ro_access.
    rewrite H0.
    apply pow2_positive.

    intros h1 [q [A [j [δ [m γ]]]]] [h3 h4].
    simpl in h3.
    reduce_ro_access h3.
    unfold θ.
    simpl.
    unfold fst_app, snd_app; simpl.
    split; auto.
    destruct h3.
    split.
    intro.
    rewrite H1 in H0.
    apply H0; auto.
    intro.
    rewrite H1 in H.
    apply H; auto.
  }
  {
    (* proving invariant *)
      apply (pp_rw_sequence_tot
           (Γ := (INTEGER :: Γ))
           (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
           (θ :=
              fun _ (δγ :
                sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx (INTEGER :: Γ))  
              =>
                let m := fst (snd δγ) in
                let x := ro_access _ _ _ w (snd (snd δγ)) in
                let q := fst (fst δγ) in
                let A := fst (snd (fst δγ)) in
                let j := fst (snd (snd (fst δγ))) in
                let δ := fst (snd (snd (snd (fst δγ)))) in
                exists n : nat,
                  Z.of_nat n = (j - 1)%Z /\
                    δ = pow2 (- m) /\ q = sin_q (S n) x /\ A = sin_A n x)).

      {
        (* j := j + 1 *)
        assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) INTEGER 2) as a
            by repeat constructor.
        apply (pp_rw_assign_tot_util INTEGER
                 (θ := (fun y
                            (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ)))
                        => 
                          let j := fst (snd (snd (fst_app δγ))) in
                          y = j + 1)%Z)
                 a
              ).    
        
        proves_simple_arithmetical.
        rewrite val.
        reduce_ro_access.
        unfold fst_app; simpl; auto.
        destruct x as [q [A [j [δ [m γ]]]]].      
        simpl; auto.
        intros j' [m γ] [q [A [n [δ t]]]] h1 h2.
        simpl in h2.
        unfold ro_to_rw_pre in h1.
        simpl in h1.
        destruct h1.
        simpl in H.
        simpl in H0.
        unfold fst_app, snd_app in H; simpl in H.
        destruct H as [l [p1 [p2 [p3 p4]]]].
        simpl in p1, p2, p3, p4.
        exists l.
        reduce_update.
        repeat split; auto.
        rewrite h2.
        ring_simplify.
        auto.
      }

      apply (pp_rw_sequence_tot
               (Γ := (INTEGER :: Γ))
               (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
               (θ :=
                  fun _ (δγ :
                        sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx (INTEGER :: Γ))  
                  =>
                    let m := fst (snd δγ) in
                    let x := ro_access _ _ _ w (snd (snd δγ)) in
                    let q := fst (fst δγ) in
                    let A := fst (snd (fst δγ)) in
                    let j := fst (snd (snd (fst δγ))) in
                    let δ := fst (snd (snd (snd (fst δγ)))) in
                    exists n : nat,
                      Z.of_nat n = (j - 1)%Z /\
                        δ = pow2 (- m) /\ q = sin_q (S n) x /\ A = sin_A (S n) x)).
      {
        (* A := A + q *)
        assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) REAL 1) as a
            by repeat constructor.
        apply (pp_rw_assign_tot_util REAL
                 (θ := (fun y
                            (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ)))
                        => 
                          let q := fst (fst_app δγ) in
                          let A := fst (snd (fst_app δγ)) in
                          y = A + q)%R)
                 a
              ).    
        proves_simple_arithmetical.

        rewrite val.
        reduce_ro_access.
        unfold fst_app; simpl; auto.
        destruct x as [q [A [j [δ [m γ]]]]].      
        simpl; auto.


        intros j' [m γ] [q [A [n [δ t]]]] [l [p1 [p2 [p3 p4]]]] h2.
        simpl in p1, p2, p3, p4, h2.
        exists l.
        reduce_update.
        repeat split; auto.
        rewrite h2.
        rewrite <- p3.
        rewrite <- p4.
        ring.
      }

      (* q := - q * x * x / (2 j + 2) (2 j  + 3)  *)
      assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) REAL 0) as a
          by repeat constructor.
      apply (pp_rw_assign_tot_util REAL
               (θ := (fun y
                          (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ)))
                      => 
                        let q := fst (fst_app δγ) in
                        let x := ro_access Γ k REAL w (snd (snd_app δγ)) in
                        let j := fst (snd (snd (fst_app δγ))) in
                        y = - q * x * x / (IZR (2 * j + 2))%Z / (IZR (2 * j + 3))%Z))
               a
            ).

      proves_simple_arithmetical.
      reduce_ro_access.
      destruct x as [q [A [j [δ [m γ]]]]].      
      simpl.
      repeat split; auto.
      apply not_0_IZR.
      destruct pre.
      simpl in H.
      destruct H.
      admit.
      admit.

      rewrite val.
      reduce_ro_access.
      destruct x as [q [A [j [δ [m γ]]]]].      
      simpl.
      rewrite (ro_access_typing_irrl _ _ _   (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse h4)))))  w).
      rewrite (ro_access_typing_irrl _ _ _   (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse h6)))))  w).
      unfold Rdiv.
      ring.

      
      intros q' [m γ] [q [A [j δ]]] [l [p1 [p2 [p3 p4]]]] h2.
      simpl in p1, p2, p3, p4, h2.
      reduce_update.
      exists (S l).
      simpl.
      repeat split; auto.
      Require Import Lia.
      lia.
      rewrite h2.
      destruct δ; auto.

      simpl.
      rewrite <- p3.
      unfold Rdiv.
      replace ( IZR (match j with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'~0
                     | Z.neg y' => Z.neg y'~0
                     end + 2)%Z)
        with (match (l + S (l + 0) + 2)%nat with
              | 0%nat => 1
              | S _ => INR (l + S (l + 0) + 2) + 1
              end).
      
      replace (IZR (match j with
                    | 0 => 0
                    | Z.pos y' => Z.pos y'~0
                    | Z.neg y' => Z.neg y'~0
                    end + 3)%Z)
        with
        
        (match (l + S (l + 0) + 3)%nat with
         | 0%nat => 1
         | S _ => INR (l + S (l + 0) + 3) + 1
         end).
      ring.
      replace ((match j with
             | 0 => 0
             | Z.pos y' => Z.pos y'~0
             | Z.neg y' => Z.neg y'~0
             end + 3)%Z) with (2 * j + 3)%Z by auto. 
      replace (l + S (l + 0) + 3)%nat with (S (2 + l + S (l + 0)))%nat by ring.
      rewrite INR_IZR_INZ.
      replace (Z.of_nat (S (2 + l + S (l + 0)))) with (2 * (Z.of_nat l) + 4)%Z.
      rewrite p1.
      rewrite plus_IZR. 
      rewrite plus_IZR. 
      rewrite mult_IZR.
      rewrite mult_IZR.
      rewrite minus_IZR. 
      ring.
      replace (S (2 + l + S (l + 0))) with (l + l + 4)%nat by ring.      
      repeat rewrite Nat2Z.inj_add.
      ring.
      replace ((match j with
             | 0 => 0
             | Z.pos y' => Z.pos y'~0
             | Z.neg y' => Z.neg y'~0
             end + 2)%Z) with (2 * j + 2)%Z by auto. 
      replace (l + S (l + 0) + 2)%nat with (S (1 + l + S (l + 0)))%nat by ring.
      rewrite INR_IZR_INZ.
      replace (Z.of_nat (S (1 + l + S (l + 0)))) with (2 * (Z.of_nat l) + 3)%Z.
      rewrite p1.
      rewrite plus_IZR. 
      rewrite plus_IZR. 
      rewrite mult_IZR.
      rewrite mult_IZR.
      rewrite minus_IZR. 
      ring.
      replace (S (1 + l + S (l + 0))) with (l + l + 3)%nat by ring.      
      repeat rewrite Nat2Z.inj_add.
      ring.
  }
  {
    (* proving variant *)
    apply (pp_rw_sequence_tot
             (Γ := (INTEGER :: Γ) ++ REAL :: REAL :: INTEGER :: REAL :: nil)
             (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
             (θ :=
                (fun _ (δγδ : sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx ((INTEGER :: Γ) ++ REAL :: REAL :: INTEGER :: REAL :: nil)) =>
       let m := fst (fst_app (snd δγδ)) in
       let x := ro_access Γ k REAL w (snd (fst_app (snd δγδ))) in
       let j := fst (snd (snd (fst δγδ))) in
       let j' := fst (snd (snd (snd_app (snd δγδ)))) in
       exists n : nat, Z.of_nat n = j' /\ j = (j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)))).
      {
        (* j := j + 1 *)
        assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) INTEGER 2) as a
            by repeat constructor.
        apply (pp_rw_assign_tot_util INTEGER
                 (θ := (fun y
                            (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (_)))
                        => 
                          let j := fst (snd (snd (fst_app δγ))) in
                          y = j + 1)%Z)
                 a
              ).    
        
        proves_simple_arithmetical.
        rewrite val.
        reduce_ro_access.
        unfold fst_app; simpl; auto.
        destruct x as [q [A [j [δ [m γ]]]]].      
        simpl; auto.
        intros j' [m γ] [q [A [n [δ t]]]] h1 h2.
        simpl in h2.
        unfold ro_to_rw_pre in h1.
        destruct h1.
        simpl in H0.
        simpl in H.
        destruct H.
        destruct H.
        simpl in H.
        exists ( x).
        simpl.
        rewrite <- H0.
        reduce_update.
        repeat split; auto.
        destruct H; auto.
        destruct H1.
        simpl in H1.
        rewrite tedious_equiv_2_fst.
        simpl.
        destruct H.
        destruct H3.
        destruct H4.
        rewrite tedious_equiv_2_fst in H4.
        simpl in H4.
        rewrite <- H4.
        rewrite tedious_equiv_2_fst in H3.
        simpl in H3.
        rewrite H3 in H1.
        pose proof (H1 eq_refl).
        replace (-m - 1)%Z with (-m + -1)%Z by auto.
        rewrite pow2_add.
        simpl.
        replace (2 * 1) with 2 by ring.
        exact H6.
      }

      
      apply (pp_rw_sequence_tot
               (Γ := (INTEGER :: Γ) ++ REAL :: REAL :: INTEGER :: REAL :: nil)
               (Δ :=  REAL :: REAL :: INTEGER :: REAL :: nil)
               (θ :=
                  (fun _ (δγδ : sem_ro_ctx (REAL :: REAL :: INTEGER :: REAL :: nil) * sem_ro_ctx ((INTEGER :: Γ) ++ REAL :: REAL :: INTEGER :: REAL :: nil)) =>
                     let m := fst (fst_app (snd δγδ)) in
                     let x := ro_access Γ k REAL w (snd (fst_app (snd δγδ))) in
                     let j := fst (snd (snd (fst δγδ))) in
                     let j' := fst (snd (snd (snd_app (snd δγδ)))) in
                     exists n : nat, Z.of_nat n = j' /\ j = (j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q (S n) x)))).
      {
        (* A := A + q *)
        assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) REAL 1) as a
            by repeat constructor.
        apply (pp_rw_assign_tot_util REAL
                 (θ := (fun y
                            (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ ++ _)))
                        => 
                          let q := fst (fst_app δγ) in
                          let A := fst (snd (fst_app δγ)) in
                          y = A + q)%R)
                 a
              ).
        
        proves_simple_arithmetical.

        rewrite val.
        reduce_ro_access.
        unfold fst_app; simpl; auto.
        destruct x as [q [A [j [δ [m γ]]]]].      
        simpl; auto.
        intros j' [m γ] [q [A [n [δ t]]]] h1 h2.
        simpl in h2.
        unfold ro_to_rw_pre in h1.
        destruct h1.
        simpl in H.
        destruct H.
        destruct H0.
        exists ( x).
        simpl.
        rewrite <- H0.
        reduce_update.
        repeat split; auto.
      }

      (* q := - q * x * x / (2 j + 2) (2 j  + 3)  *)
      assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) REAL 0) as a
          by repeat constructor.
      apply (pp_rw_assign_tot_util REAL
               (θ := (fun y
                          (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ ((INTEGER :: Γ) ++ _)))
                      => 
                        let q := fst (fst_app δγ) in
                        let x := ro_access Γ k REAL w (snd (fst_app (snd_app δγ))) in
                        let j := fst (snd (snd (fst_app δγ))) in
                        y = - q * x * x / (IZR (2 * j + 2))%Z / (IZR (2 * j + 3))%Z))
               a
            ).
      simpl.

      pose proof (has_type_ro_add_auxiliary _ _ _ w''' (REAL :: REAL :: INTEGER :: REAL :: nil)).
      pose proof (has_type_ro_add_auxiliary _ _ _ w (REAL :: REAL :: INTEGER :: REAL :: nil)).
      proves_simple_arithmetical.

      reduce_ro_access.      
      destruct x as [q [A [j [δ [m γ]]]]].      
      simpl.
      repeat split; auto.
      apply not_0_IZR.
      destruct pre.
      simpl in H.
      admit.
      admit.

      rewrite val.
      reduce_ro_access.
      destruct x as [q [A [j [δ [m γ]]]]].      
      simpl.
      Search ro_access.
      rewrite (tedious_equiv_2 γ).
      rewrite <- (ro_access_app _ _ _ _ w _ _ (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse h6)))))).
      rewrite <- (ro_access_app _ _ _ _ w _ _ (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse (has_type_ro_Var_S_inverse h4)))))).
      unfold Rdiv.
      simpl.
      repeat rewrite tedious_equiv_2_snd.
      simpl.      
      rewrite tedious_equiv_2_fst.
      simpl.
      rewrite tedious_equiv_fst.
      ring.

      intros j' [m γ] [q [A [n [δ t]]]] h1 h2.
      simpl in h2.
      unfold ro_to_rw_pre in h1.
      destruct h1.
      simpl in H.
      destruct H.
      destruct H0.
      exists ( x).
      simpl.
      rewrite <- H0.
      reduce_update.
      repeat split; auto.
  }

  {
    (* ψ is well-founded *)
    intros.
    intro.
    destruct H0.
    destruct H0.

    admit.
  }

  {
    (* enterring the loop; initial conditoin *)
    intros x.
    intros.
    exists O.
    repeat split.
    rewrite H.
    repeat split.
    
