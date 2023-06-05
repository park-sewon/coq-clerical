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
Print sin_in.
Print infinite_sum.
Print sin_n.
Search sin_n.
Search exist_sin.

(* compute sine(VAR k) *)
Definition exp_sine k :=
  Lim
    (
      NEWVAR (EXP (:-: (VAR 0))) IN
      NEWVAR (INT 0) IN
      NEWVAR (RE (INT 1)) IN
      NEWVAR (RE (INT 0)) IN
      NEWVAR (VAR (5 + k)) IN
        
      WHILE
        clerical_neg (clerical_bounded 0 4)
      DO
        LET 3 := VAR 3 :+: INT 1 ;;
        LET 1 := VAR 1 ;+; VAR 0 ;*; VAR 2  ;;
        LET 2 := VAR 2 ;*; (RE (INT -1)) ;;
        LET 0 := VAR 0 ;*; VAR (6 + k) ;*; VAR (6 + k) ;*; (;/; (RE (INT 2 :*: VAR 3 :+: INT 1))) ;*; (;/; (RE (INT 2 :*: VAR 3)))
      END ;; VAR 1
    ).

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
           (σ := REAL)
           (θ := (fun y x => y = pow2 (- ro_access _ _ _ w' x)))).
  proves_simple_arithmetical.
  rewrite val.
  rewrite (ro_access_typing_irrl _ _ _ w' h0).
  reflexivity.
  
  apply (pp_rw_new_var_tot
           (σ := INTEGER)
           (θ := (fun y x => y = 0%Z))).

  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot
           (σ := REAL)
           (θ := (fun y x => y = 1%R))).

  proves_simple_arithmetical.

  apply (pp_rw_new_var_tot
           (σ := REAL)
           (θ := (fun y x => y = 0%R))).

  proves_simple_arithmetical.

  
  assert ( ((REAL :: REAL :: INTEGER :: REAL :: nil)  ++  (INTEGER :: Γ)) |- VAR (5 + k) : REAL) as w'' by auto_typing.
  apply (pp_rw_new_var_tot  
           (σ := REAL)
           (θ := (fun y x => y = ro_access _ _ _ w'' x))).
  proves_simple_arithmetical.
  rewrite (ro_access_typing_irrl _ _ _ w'' tmp1).
  exact val.

  simpl.

  apply (pp_rw_while_tot_back
           (

        ).
  
  exp_abs_

Lemma sine_wty : forall Γ k, Γ |- VAR k : REAL -> Γ |- sine k : REAL.
Proof.
  intros.
  auto_typing.
  apply r_has_type_rw_has_type_rw.
  apply r_has_type_rw_Newvar.
                                     
