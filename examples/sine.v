From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

Require Import Examples.abs.

Definition relation X := X -> X -> Type.
Definition PartialOrder X (R : relation X) :=
  True.
Class PPO {X: Type} (R : relation X) := {
    partial :> PartialOrder X R;
    Bot : X;
    Bot_least_elem : forall x:X, R Bot x;
}.

(* compute sine(VAR k) *)
Definition exp_sine k :=
  Lim
    (
      NEWVAR (INT 0) IN
      NEWVAR (RE (INT 1)) IN
      NEWVAR (RE (INT 0)) IN
      NEWVAR (VAR (k + 4)) IN
             
      WHILE
        exp_abs 0 ;<; EXP (:-: VAR 0)
      DO
        LET 3 := VAR 3 :+: INT 1 ;;
        LET 1 := VAR 1 ;+; VAR 0 ;*; VAR 2  ;;
        LET 2 := VAR 2 ;*; (RE (INT -1)) ;;
        LET 0 := VAR 0 ;*; VAR (k + 5) ;*; VAR (k + 5) ;*; (;/; (RE (INT 2 :*: VAR 3 :+: INT 1))) ;*; (;/; (RE (INT 2 :*: VAR 3)))
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

  
  assert ( ((REAL :: REAL :: INTEGER :: nil)  ++  (INTEGER :: Γ)) |- VAR (k + 4) : REAL) as w'.
  simpl.
  replace (k + 4)%nat with (S (S (S (S k)))) by ring.
  auto_typing.

  
  apply (pp_rw_new_var_tot  
           (σ := REAL)
           (θ := (fun y x => y = ro_access _ _ _ w' x))).

  proves_simple_arithmetical.

  rewrite (ro_access_typing_irrl _ _ _ w' tmp1).
  exact val.

  simpl.
  
  
  exp_abs_

Lemma sine_wty : forall Γ k, Γ |- VAR k : REAL -> Γ |- sine k : REAL.
Proof.
  intros.
  auto_typing.
  apply r_has_type_rw_has_type_rw.
  apply r_has_type_rw_Newvar.
                                     
