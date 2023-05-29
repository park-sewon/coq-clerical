From Clerical Require Import Clerical.
Require Import ZArith.
Notation "':-:' e" := (BinOp OpZminus ( (INT 0)) e) (at level 45, right associativity) : clerical_scope.
Notation "';-;' e" := (BinOp OpRminus (RE (INT 0)) e) (at level 45, right associativity) : clerical_scope.

(* computing the absolute value of variable k *)
Definition exp_abs k :=  
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1))
       ==> ;-; VAR (S k)
       OR
       ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) 
       ==> VAR (S k)
       END)
.

Lemma exp_abs_wty :
  forall Γ k, Γ |- VAR k : REAL ->
                         Γ |- exp_abs k : REAL. 

  intros.
  apply has_type_ro_Lim.
  apply has_type_ro_rw.
  apply has_type_rw_Case.
  simpl.
  apply has_type_ro_OpRlt.
  apply has_type_ro_Var_S.
  exact H.
  apply has_type_ro_OpZRexp.
  apply has_type_ro_OpZminus.
  apply has_type_ro_OpZminus.
  apply has_type_ro_Int.
  apply has_type_ro_Var_0.
  apply has_type_ro_Int.
  apply has_type_rw_ro.
  apply has_type_ro_OpRminus.
  apply has_type_ro_OpZRcoerce.
  apply has_type_ro_Int.
  apply has_type_ro_Var_S.
  exact H.

  apply has_type_ro_OpRlt.
  apply has_type_ro_OpRminus.
  apply has_type_ro_OpZRcoerce.
  apply has_type_ro_Int.
  apply has_type_ro_OpZRexp.
  apply has_type_ro_OpZminus.
  apply has_type_ro_OpZminus.
  apply has_type_ro_Int.
  apply has_type_ro_Var_0.
  apply has_type_ro_Int.
  apply has_type_ro_Var_S.
  exact H.

  apply has_type_rw_ro.
  apply has_type_ro_Var_S.
  exact H.
Defined.

Check ro_access.
Require Import Reals.
Open Scope R.

(* when we know where the limit converges to *)
Lemma ro_lim_prt_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ro_ctx Γ -> R) :
  (has_type_ro_Lim_inverse Γ e w) |-
        [{fun x => ϕ (snd x)}]
          e
          [{y | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
        ((fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
        w |- {{ϕ}} Lim e {{ψ}}.
Proof.
  intros.
  pose proof
    (ro_lim_prt _ _ _ _ _ w
       (fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x)
       X
    ).
  assert ((forall γ, ϕ γ ->
                exists y : R,
                  (fun y0 x => ϕ x /\ y0 = f x) y γ /\
                    (forall x z,
                        (fun y0 x0 => Rabs (y0 - f (snd x0)) < pow2 (- fst x0)) z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x)))).
  intros.
  exists (f γ).
  split.
  split; auto.
  intros.
  exact H1.
  apply X0 in H0.
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a H0 H);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_lim_tot_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ro_ctx Γ -> R) :
  (has_type_ro_Lim_inverse Γ e w) |-
        [{fun x => ϕ (snd x)}]
          e
          [{y | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
        ((fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
        w |- [{ϕ}] Lim e [{ψ}].
Proof.
  intros.
  pose proof
    (ro_lim_tot _ _ _ _ _ w (fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x) X).
  assert ((forall γ, ϕ γ ->
                exists y : R,
                  (fun y0 x => ϕ x /\ y0 = f x) y γ /\
                    (forall x z,
                        (fun y0 x0 => Rabs (y0 - f (snd x0)) < pow2 (- fst x0)) z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x)))).
  intros.
  exists (f γ).
  split.
  split; auto.
  intros.
  exact H1.
  apply X0 in H0.
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a H0 H);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Require Import List.
Lemma ro_rw_prt_util {Γ } {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} :
  has_type_rw_ro Γ nil e τ w ||-
    {{fun x => ϕ (snd x)}}
    e
    {{y | fun x => ψ y (snd x)}} ->
  w |- {{ϕ}} e {{ψ}}.
Proof.
  intro.
  pose proof (ro_rw_prt _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_rw_tot_util {Γ} {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} :
  has_type_rw_ro Γ nil e τ w ||-
    [{fun x => ϕ (snd x)}]
    e
    [{y | fun x => ψ y (snd x)}] ->
  w |- [{ϕ}] e [{ψ}].
Proof.
  intro.
  pose proof (ro_rw_tot _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X0);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Notation " Γ ||- {{ ϕ }} e {{ ψ }} " :=
  (proves_ro_prt Γ e _ _ (mk_ro_prt _ ϕ ψ)) (at level 40,  ϕ, e, ψ at next level) : simple_scope.

Notation " Γ ||- [{ P }] e [{ Q }] " :=
  (proves_ro_tot Γ e _ _ (mk_ro_tot _ P Q)) (at level 40,  P, e, Q at next level).

Notation " Γ ;;; Δ ||- {{ ϕ }} e {{ ψ }} " :=
  (proves_rw_prt Γ Δ e _ _ (mk_rw_prt _ ϕ ψ)) (at level 50).

Notation " Γ ;;; Δ ||- [{ P }] e [{ Q }] " :=
  (proves_rw_tot Γ Δ e _ _ (mk_rw_tot _ P Q)) (at level 40, Δ, P, e, Q at next level).

Lemma exp_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    (exp_abs_wty Γ k w) |-
      [{fun _ => True}]
        exp_abs k 
        [{y | fun x => y = Rabs (ro_access Γ k REAL w x) }].
Proof.
  intros.
  Close Scope detail_scope.
  apply (ro_lim_tot_util (fun x =>  Rabs (ro_access Γ k REAL w x)));
    try (intros h1 h2 [_ h3]; auto; fail).
  apply (ro_rw_tot_util).
  
  
  Check rw_ro_tot.
