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
     | S m => sin_q (S m) x * sin_A m x 
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
        LET 0 := VAR 0 ;*; VAR (6 + k) ;*; VAR (6 + k) ;/; (RE (INT 2 :*: VAR 3 :+: INT 1)) ;/; (RE (INT 2 :*: VAR 3))
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
                     (j = j' + 1)%Z /\ pow2 (- m - 1) < Rabs (sin_q n x)).
  
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

      Check pp_rw_assign_tot.
      assert (assignable (REAL :: REAL :: INTEGER :: REAL :: nil) INTEGER 2) as a.
      repeat constructor.
      apply ( pp_rw_assign_tot
               (τ := INTEGER)
               (θ := (fun y
                          (δγ : sem_ro_ctx ((REAL :: REAL :: INTEGER :: REAL :: nil) ++ (INTEGER :: Γ)))
                           => 
                        let j := fst (snd (snd (fst_app δγ))) in
                        y = j + 1)%Z)
               (k := 2)
               a
            ).
      
      proves_simple_arithmetical.
      rewrite val.
      reduce_ro_access.
      unfold fst_app; simpl; auto.
      repeat destruct x.
      repeat destruct p.
      simpl; auto.
      intros.
      
      
      unfold ro_to_rw_pre in pre.
      
      simpl in pre.
      


    X : Var (5 + k)
  m : Var 4
  δ : Var 3
  j : Var 2
  A : Var 1
  q : Var 0

                let j := fst (snd (snd 
             

        ).
  
  exp_abs_

Lemma sine_wty : forall Γ k, Γ |- VAR k : REAL -> Γ |- sine k : REAL.
Proof.
  intros.
  auto_typing.
  apply r_has_type_rw_has_type_rw.
  apply r_has_type_rw_Newvar.
                                     
