Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.
Require Import Clerical.ReasoningAdmissible.

Require Import List.


Definition proves_ro_prt_util Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & w |- {{ϕ}} e {{ψ}} }.

Definition proves_ro_tot_util Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & w |- [{ϕ}] e [{ψ}] }.

Definition proves_rw_prt_util Γ Δ e τ ϕ ψ :=
  {w : Γ ;;; Δ ||- e : τ & w ||- {{ϕ}} e {{ψ}} }.

Definition proves_rw_tot_util Γ Δ e τ ϕ ψ :=
  {w : Γ ;;; Δ ||- e : τ & w ||- [{ϕ}] e [{ψ}] }.

Notation " Γ |-- {{ ϕ }} e {{ y : τ | ψ }} " :=
  (proves_ro_prt_util Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ '|--' '[{' ϕ '}]' e '[{' y ':' τ '|' ψ '}]' " :=
  (proves_ro_tot_util Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ ;;; Δ ||-- {{ ϕ }} e {{ y : τ | ψ }} " :=
  (proves_rw_prt_util Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ ;;; Δ ||-- [{ ϕ }] e [{ y : τ | ψ }] " :=
  (proves_rw_tot_util Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope.



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




Section LogicalRules.
  Lemma util_ro_imply_prt {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    Γ |-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ |-- {{ϕ'}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_imply_tot {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    Γ |-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ |-- [{ϕ'}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_imply_prt {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ ;;; Δ ||-- {{ϕ'}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_imply_tot {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ ;;; Δ ||-- [{ϕ'}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_pre_prt {Γ} {e} {τ} {ϕ ϕ'} {ψ} :
    Γ |-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ  -> Γ |-- {{ϕ'}} e {{y : τ | ψ y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_pre_tot {Γ} {e} {τ} {ϕ ϕ'} {ψ} :
    Γ |-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ -> Γ |-- [{ϕ'}] e [{y : τ | ψ y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_pre_prt {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ -> Γ ;;; Δ ||-- {{ϕ'}} e {{y : τ | ψ y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_pre_tot {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ ->  Γ ;;; Δ ||-- [{ϕ'}] e [{y : τ | ψ y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.


  Lemma util_ro_post_prt {Γ} {e} {τ} {ϕ} {ψ ψ'} :
    Γ |-- {{ϕ}} e {{y : τ | ψ y}} -> ψ ->>> ψ' -> Γ |-- {{ϕ}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_post_tot {Γ} {e} {τ} {ϕ} {ψ ψ'} :
    Γ |-- [{ϕ}] e [{y : τ | ψ y}] ->  ψ ->>> ψ' -> Γ |-- [{ϕ}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_post_prt {Γ Δ} {e} {τ} {ϕ} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- {{ϕ}} e {{y : τ | ψ y}} ->  ψ ->>> ψ' -> Γ ;;; Δ ||-- {{ϕ}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_rw_post_tot {Γ Δ} {e} {τ} {ϕ} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- [{ϕ}] e [{y : τ | ψ y}] -> ψ ->>> ψ' -> Γ ;;; Δ ||-- [{ϕ}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_rw_prt {Γ} {e} {τ} {ϕ} {ψ} :
    Γ ;;; nil ||-- {{fun x => ϕ (snd x)}} e {{y : τ| fun x => ψ y (snd x)}} ->
    Γ |-- {{ϕ}} e {{y : τ | ψ y}}.
  Proof.
    intros.
    destruct X.
    exists (has_type_ro_rw _ _ _ x).
    apply (ro_rw_prt_util ).  
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_rw_tot {Γ} {e} {τ} {ϕ} {ψ} :
    Γ ;;; nil ||-- [{fun x => ϕ (snd x)}] e [{y : τ| fun x => ψ y (snd x)}] ->
    Γ |-- [{ϕ}] e [{y : τ | ψ y}].
  Proof.
    intros.
    destruct X.
    exists (has_type_ro_rw _ _ _ x).
    apply (ro_rw_tot_util ).  
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

End LogicalRules.

Section VarAndConstants.

  Lemma util_ro_var_prt {Γ} {k} {τ} {ϕ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      ϕ ->> (fun x => ψ (ro_access Γ k τ w x) x) ->
                      Γ |-- {{ϕ}} VAR k {{y : τ | ψ y}}.
  Proof.
    intros.
    exists w.
    pose proof (ro_var_prt _ _ _ w ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma util_ro_var_tot {Γ} {k} {τ} {ϕ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      ϕ ->> (fun x => ψ (ro_access Γ k τ w x) x) ->
                      Γ |-- [{ϕ}] VAR k [{y : τ | ψ y}].
  Proof.
    intros.
    exists w.
    pose proof (ro_var_tot _ _ _ w ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_skip_prt {Γ} {ϕ} {ψ} :
    ϕ ->> ψ tt -> Γ |-- {{ϕ}} SKIP {{y : UNIT | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_skip_tot {Γ} {ϕ} {ψ} :
    ϕ ->> ψ tt -> Γ |-- [{ϕ}] SKIP [{y : UNIT | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma util_ro_true_prt {Γ} {ϕ} {ψ} :
    ϕ ->> ψ true -> Γ |-- {{ϕ}} TRUE {{y : BOOL | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_true_tot {Γ} {ϕ} {ψ} :
    ϕ ->> ψ true -> Γ |-- [{ϕ}] TRUE [{y : BOOL | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma util_ro_false_prt {Γ} {ϕ} {ψ} :
    ϕ ->> ψ false -> Γ |-- {{ϕ}} FALSE {{y : BOOL | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_false_tot {Γ} {ϕ} {ψ} :
    ϕ ->> ψ false -> Γ |-- [{ϕ}] FALSE [{y : BOOL | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
    
  Lemma util_ro_int_prt {Γ} {k} {ϕ} {ψ} :
    ϕ ->> ψ k -> Γ |-- {{ϕ}} INT k {{y : INTEGER | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma util_ro_int_tot {Γ} {k} {ϕ} {ψ} :
    ϕ ->> ψ k -> Γ |-- [{ϕ}] INT k [{y : INTEGER | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    pose proof (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
End VarAndConstants.

Section Unary.
  Lemma util_ro_coerce_prt {Γ} {e} {ϕ} {ψ} :
    Γ |-- {{ϕ}} e {{y : INTEGER | ψ (IZR y) }} ->
    Γ |-- {{ϕ}} RE e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_prt _ _ w _ _ _ p). 
  Defined.

  Lemma util_ro_coerce_tot {Γ} {e} {ϕ} {ψ} :
    Γ |-- [{ϕ}] e [{y : INTEGER | ψ (IZR y) }] ->
    Γ |-- [{ϕ}] RE e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_tot _ _ w _ _ _ p). 
  Defined.
  
  Lemma util_ro_exp_prt {Γ} {e} {ϕ} {ψ} :
    Γ |-- {{ϕ}} e {{y : INTEGER | ψ (pow2 y) }} ->
    Γ |-- {{ϕ}} EXP e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_prt _ _ w _ _ _ p). 
  Defined.

  Lemma util_ro_exp_tot {Γ} {e} {ϕ} {ψ} :
    Γ |-- [{ϕ}] e [{y : INTEGER | ψ (pow2 y) }] ->
    Γ |-- [{ϕ}] EXP e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_tot _ _ w _ _ _ p). 
  Defined.

  Lemma util_ro_recip_prt {Γ} {e} {ϕ} {ψ} :
    Γ |-- {{ϕ}} e {{y : REAL | ψ (/ y) }} ->
    Γ |-- {{ϕ}} ;/; e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_prt _ _ w _ _ _ _ p).
    intros x h [j _]; auto.
  Defined.

  Lemma util_ro_recip_tot {Γ} {e} {ϕ} {ψ} :
    Γ |-- [{ϕ}] e [{y : REAL | ψ (/ y) /\\ (fun _ => y <> 0 %R)}] ->
    Γ |-- [{ϕ}] ;/; e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_tot _ _ w _ _ _ _ p).
    intros x h [j jj]; auto.
    split.
    exact jj.
    exact j.
  Defined.

End Unary.

Section Binary.
  Lemma util_ro_int_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :+: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :-: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :*: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :<: e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_comp_eq_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :=: e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;+; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;-; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;*; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 -> ψ (Rltb'' y1 y2)%R x)) ->
    Γ |-- {{ϕ}} e1 ;<; e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :+: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :-: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :*: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :<: e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_int_comp_eq_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :=: e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;+; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;-; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;*; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma util_ro_real_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 /\ ψ (Rltb'' y1 y2)%R x)) ->
    Γ |-- [{ϕ}] e1 ;<; e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

End Binary.

Section Limits.
  Lemma util_ro_lim_prt {Γ} {e} {ϕ : sem_ro_ctx Γ -> Prop} {ψ} (f : sem_ro_ctx Γ -> R) :
    (INTEGER :: Γ) |-- [{fun x => ϕ (snd x)}] e  [{y : REAL | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
    ((fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
    Γ |-- {{ϕ}} Lim e {{y : REAL | ψ y}}.
  Proof.
    intros.
    destruct X.
    exists (has_type_ro_Lim _ _ x).
    apply (ro_lim_prt_util f).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    exact H.
  Defined.

  Lemma util_ro_lim_tot {Γ} {e} {ϕ : sem_ro_ctx Γ -> Prop} {ψ} (f : sem_ro_ctx Γ -> R) :
    (INTEGER :: Γ) |-- [{fun x => ϕ (snd x)}] e  [{y : REAL | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
    ((fun y (x : sem_ro_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
    Γ |-- [{ϕ}] Lim e [{y : REAL | ψ y}].
  Proof.
    intros.
    destruct X.
    exists (has_type_ro_Lim _ _ x).
    apply (ro_lim_tot_util f).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    exact H.
  Defined.
End Limits.

Section CommandsTmp.

  Lemma rw_new_var_prt_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
    {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
    w1 |- {{ϕ'}} e {{θ}} ->
          w2 ||- {{θ'}} c {{ψ'}} ->
          ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
          ((fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
          (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
          w ||- {{ϕ}} Newvar e c {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w1 w1 _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_new_var_prt).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
  Defined.

  Lemma rw_new_var_tot_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
    {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
    w1 |- [{ϕ'}] e [{θ}] ->
          w2 ||- [{θ'}] c [{ψ'}] ->
          ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
          ((fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
          (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
          w ||- [{ϕ}] Newvar e c [{ψ}].
  Proof.
    intros.
    pose proof (ro_imply_tot _ _ _ w1 w1 _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_new_var_tot).
    apply (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
  Defined.

  Lemma rw_assign_prt_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
    {ϕ} {ϕ'} {ψ : post} {θ} :
    w |- {{ϕ'}} e {{θ}} ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
         w' ||- {{ϕ}} Assign k e {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ X0 H0).
  Defined.

  Lemma rw_assign_tot_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
    {ϕ} {ϕ'} {ψ : post} {θ} :
    w |- [{ϕ'}] e [{θ}] ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
         w' ||- [{ϕ}] Assign k e [{ψ}].
  Proof.
    intros.
    pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    apply (rw_assign_tot _ _ _ _ _ _ _ _ _ _ X0 H0).
  Defined.

  Lemma rw_cond_prt_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
    {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
    w |- {{ϕ'}} e {{θ}} ->
         w1 ||- {{θ1'}} c1 {{ψ1'}} ->
         w2 ||- {{θ2'}} c2 {{ψ2'}} ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ1') -> 
         (ψ1' ->>> ψ) ->
         (ro_to_rw_pre (θ false) ->> θ2') -> 
         (ψ2' ->>> ψ) ->
         w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                  H2 X1 H3
      ).

    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
  Defined.

  Lemma rw_cond_tot_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
    {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
    w |- [{ϕ'}] e [{θ}] ->
         w1 ||- [{θ1'}] c1 [{ψ1'}] ->
         w2 ||- [{θ2'}] c2 [{ψ2'}] ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ1') -> 
         (ψ1' ->>> ψ) ->
         (ro_to_rw_pre (θ false) ->> θ2') -> 
         (ψ2' ->>> ψ) ->
         w' ||- [{ϕ}] Cond e c1 c2 [{ψ}].
  Proof.
    intros.
    pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_tot _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                  H2 X1 H3
      ).

    apply (rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
  Defined.

  Lemma rw_while_prt_util {Γ Δ} {e c}  {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c : UNIT} 
    {w' : Γ ;;; Δ ||- While e c : UNIT} {ϕ} {ϕ'} {θ} {θ'} {ψ'}  {ψ : post} :
    w |- {{ϕ'}} e {{θ}} ->
         w1 ||- {{θ'}} c {{ψ'}} ->
         ((rw_to_ro_pre ϕ) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ') -> 
         (ψ' ->>> (fun _ => ϕ)) -> 
         ((fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ) ->
         w' ||- {{ϕ}} While e c {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_while_prt _ _ _ _ _ _ w' _ _ X1 X2).
    exact (rw_imply_prt _ _ _ _ w' w' _ _ _ _
             (fun _ p => p) X3 H2
          ).
  Defined.

End CommandsTmp.

Section Commands.
  
  Lemma util_rw_new_var_prt {Γ Δ} {e c} {τ σ}
    {ϕ} {ϕ'} {ψ : post} {θ} {θ'} {ψ' : post}:
    (Δ ++ Γ) |-- {{ϕ'}} e {{y : σ | θ y}} ->
    Γ ;;; (σ :: Δ) ||-- {{θ'}} c {{y : τ | ψ' y}} ->
    ((fun x  => ϕ (tedious_sem_app Δ Γ x)) ->> ϕ') ->
    ((fun x  => θ (fst (fst x)) (snd (fst x); snd x)) ->> θ') ->
    (ψ' ->>> (fun y x => ψ y (snd (fst x), snd x))) ->
    Γ ;;; Δ ||-- {{ϕ}} Newvar e c {{y : τ | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h1 h2 h3.
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_prt_util p1 p2 h1 h2 h3).
  Defined.
  
  Lemma util_rw_new_var_tot {Γ Δ} {e c} {τ σ}
    {ϕ} {ϕ'} {ψ : post} {θ} {θ'} {ψ' : post}:
    (Δ ++ Γ) |-- [{ϕ'}] e [{y : σ | θ y}] ->
    Γ ;;; (σ :: Δ) ||-- [{θ'}] c [{y : τ | ψ' y}] ->
    ((fun x  => ϕ (tedious_sem_app Δ Γ x)) ->> ϕ') ->
    ((fun x  => θ (fst (fst x)) (snd (fst x); snd x)) ->> θ') ->
    (ψ' ->>> (fun y x => ψ y (snd (fst x), snd x))) ->
    Γ ;;; Δ ||-- [{ϕ}] Newvar e c [{y : τ | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h1 h2 h3.
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_tot_util p1 p2 h1 h2 h3).
  Defined.

  Check update.

  Lemma util_rw_assign_prt {Γ Δ} {k} {e} {τ} {ϕ} {ϕ'} {ψ : post} {θ} 
    (a : assignable Δ τ k) :
    (Δ ++ Γ) |-- {{ϕ'}} e {{y : τ | θ y}} ->
    ((fun x  => ϕ (tedious_sem_app Δ Γ x)) ->> ϕ') ->
    (forall x γ δ, θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
         Γ ;;; Δ ||-- {{ϕ}} Assign k e {{y : UNIT | ψ y}}.
  Proof.
    intros [w p] h1 h2.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ X0 H0).
  Defined.

  Lemma rw_assign_tot_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
    {ϕ} {ϕ'} {ψ : post} {θ} :
    w |- [{ϕ'}] e [{θ}] ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
         w' ||- [{ϕ}] Assign k e [{ψ}].
  Proof.
    intros.
    pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    apply (rw_assign_tot _ _ _ _ _ _ _ _ _ _ X0 H0).
  Defined.

  Lemma rw_cond_prt_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
    {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
    w |- {{ϕ'}} e {{θ}} ->
         w1 ||- {{θ1'}} c1 {{ψ1'}} ->
         w2 ||- {{θ2'}} c2 {{ψ2'}} ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ1') -> 
         (ψ1' ->>> ψ) ->
         (ro_to_rw_pre (θ false) ->> θ2') -> 
         (ψ2' ->>> ψ) ->
         w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                  H2 X1 H3
      ).

    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
  Defined.

  Lemma rw_cond_tot_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
    {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
    w |- [{ϕ'}] e [{θ}] ->
         w1 ||- [{θ1'}] c1 [{ψ1'}] ->
         w2 ||- [{θ2'}] c2 [{ψ2'}] ->
         ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ1') -> 
         (ψ1' ->>> ψ) ->
         (ro_to_rw_pre (θ false) ->> θ2') -> 
         (ψ2' ->>> ψ) ->
         w' ||- [{ϕ}] Cond e c1 c2 [{ψ}].
  Proof.
    intros.
    pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_tot _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                  H2 X1 H3
      ).

    apply (rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
  Defined.

  Lemma rw_while_prt_util {Γ Δ} {e c}  {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c : UNIT} 
    {w' : Γ ;;; Δ ||- While e c : UNIT} {ϕ} {ϕ'} {θ} {θ'} {ψ'}  {ψ : post} :
    w |- {{ϕ'}} e {{θ}} ->
         w1 ||- {{θ'}} c {{ψ'}} ->
         ((rw_to_ro_pre ϕ) ->> ϕ') ->
         (ro_to_rw_pre (θ true) ->> θ') -> 
         (ψ' ->>> (fun _ => ϕ)) -> 
         ((fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ) ->
         w' ||- {{ϕ}} While e c {{ψ}}.
  Proof.
    intros.
    pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                  H X (fun x h p => p)
      ).
    pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                  H0 X0 H1
      ).
    pose proof (rw_while_prt _ _ _ _ _ _ w' _ _ X1 X2).
    exact (rw_imply_prt _ _ _ _ w' w' _ _ _ _
             (fun _ p => p) X3 H2
          ).
  Defined.

