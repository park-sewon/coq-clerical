Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Preliminaries.Preliminaries.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.

Require Import List.

Lemma ro_prt_change_wty {Γ} {e} {τ} {w : Γ |- e : τ} (w' : Γ |- e : τ) {ϕ} {ψ} (p : w |- {{ϕ}} e {{ψ}}) : w' |- {{ϕ}} e {{ψ}}.
Proof.
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_tot_change_wty {Γ} {e} {τ} {w : Γ |- e : τ} (w' : Γ |- e : τ) {ϕ} {ψ} (p : w |- [{ϕ}] e [{ψ}]) : w' |- [{ϕ}] e [{ψ}].
Proof.
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma rw_prt_change_wty {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} (w' : Γ ;;; Δ ||- e : τ) {ϕ} {ψ} (p : w ||- {{ϕ}} e {{ψ}}) : w' ||- {{ϕ}} e {{ψ}}.
Proof.
  apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma rw_tot_change_wty {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} (w' : Γ ;;; Δ ||- e : τ) {ϕ} {ψ} (p : w ||- [{ϕ}] e [{ψ}]) : w' ||- [{ϕ}] e [{ψ}].
Proof.
  apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Definition proves_ro_prt_pp Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & w |- {{ϕ}} e {{ψ}} }.

Definition proves_ro_tot_pp Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & w |- [{ϕ}] e [{ψ}] }.

Definition proves_rw_prt_pp Γ Δ e τ ϕ ψ :=
  {w : Γ ;;; Δ ||- e : τ & w ||- {{ϕ}} e {{ψ}} }.

Definition proves_rw_tot_pp Γ Δ e τ ϕ ψ :=
  {w : Γ ;;; Δ ||- e : τ & w ||- [{ϕ}] e [{ψ}] }.

Notation " Γ '|--' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}' " :=
  (proves_ro_prt_pp Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ '|--' '[{' ϕ '}]' e '[{' y ':' τ '|' ψ '}]' " :=
  (proves_ro_tot_pp Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ ';;;' Δ '||--' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}' " :=
  (proves_rw_prt_pp Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Notation " Γ ';;;' Δ '||--' '[{' ϕ '}]' e '[{' y ':' τ '|' ψ '}]' " :=
  (proves_rw_tot_pp Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope.

Section LogicalRules.
  
  Lemma pp_ro_imply_prt {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    Γ |-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ |-- {{ϕ'}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_imply_tot {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    Γ |-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ |-- [{ϕ'}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_rw_imply_prt {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- {{ϕ}} e {{y : τ | ψ y}} -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ ;;; Δ ||-- {{ϕ'}} e {{y : τ | ψ' y}}.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_rw_imply_tot {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop} :
    Γ ;;; Δ ||-- [{ϕ}] e [{y : τ | ψ y}] -> ϕ' ->> ϕ -> ψ ->>> ψ' -> Γ ;;; Δ ||-- [{ϕ'}] e [{y : τ | ψ' y}].
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

End LogicalRules.


Section ROAndRW.
  Lemma pp_ro_rw_prt {Γ} {c} {τ} {ϕ} {ψ} :
    Γ ;;; nil ||-- {{ϕ}} c {{y : τ | ψ y}} -> 
    Γ |-- {{fun x => ϕ (tt, x)}} c {{y : τ | fun x => ψ y (tt, x)}}.
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_prt _ _ _ _ _ _ _ p).
  Defined.
  
  Lemma pp_ro_rw_tot {Γ} {c} {τ} {ϕ} {ψ} :
    Γ ;;; nil ||-- [{ϕ}] c [{y : τ | ψ y}] -> 
    Γ |-- [{fun x => ϕ (tt, x)}] c [{y : τ | fun x => ψ y (tt, x)}].
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_tot _ _ _ _ _ _ _ p).
  Defined.

  Lemma pp_rw_ro_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    (Δ ++ Γ) |-- {{ϕ}} e {{y : τ | ψ y}} -> 
    Γ ;;; Δ ||-- {{fun x => ϕ (tedious_prod_sem _ _ x)}} e {{y : τ | fun x => ψ y (tedious_prod_sem _ _ x)}}.
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    apply (rw_ro_prt _ _ _ _ _ _ _ _ p).
  Defined.

  Lemma pp_rw_ro_tot {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    (Δ ++ Γ) |-- [{ϕ}] e [{y : τ | ψ y}] -> 
    Γ ;;; Δ ||-- [{fun x => ϕ (tedious_prod_sem _ _ x)}] e [{y : τ | fun x => ψ y (tedious_prod_sem _ _ x)}].
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    apply (rw_ro_tot _ _ _ _ _ _ _ _ p).
  Defined.
End ROAndRW.


Section VariablesAndConstants.

  Lemma pp_ro_var_prt {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      Γ |-- {{(fun x => ψ (ro_access Γ k τ w x) x)}} VAR k {{y : τ | ψ y}}.
  Proof.
    intros.
    exists w.
    pose proof (ro_var_prt _ _ _ w ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_var_tot {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      Γ |-- [{(fun x => ψ (ro_access Γ k τ w x) x)}] VAR k [{y : τ | ψ y}].
  Proof.
    intros.
    exists w.
    pose proof (ro_var_tot _ _ _ w ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_skip_prt {Γ} {ψ} :
    Γ |-- {{ψ tt}} SKIP {{y : UNIT | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_skip_tot {Γ} {ψ} :
    Γ |-- [{ψ tt}] SKIP [{y : UNIT | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_true_prt {Γ} {ψ} :
    Γ |-- {{ψ true}} TRUE {{y : BOOL | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_true_tot {Γ} {ψ} :
    Γ |-- [{ψ true}] TRUE [{y : BOOL | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_false_prt {Γ} {ψ} :
    Γ |-- {{ψ false}} FALSE {{y : BOOL | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_false_tot {Γ} {ψ} :
    Γ |-- [{ψ false}] FALSE [{y : BOOL | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_int_prt {Γ} {k} {ψ} :
    Γ |-- {{ψ k}} INT k {{y : INTEGER | ψ y}}.
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_int_tot {Γ} {k} {ψ} :
    Γ |-- [{ψ k}] INT k [{y : INTEGER | ψ y}].
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    pose proof (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

End VariablesAndConstants.

Section UnaryOp.
  Lemma pp_ro_coerce_prt {Γ} {e} {ϕ} {ψ} :
    Γ |-- {{ϕ}} e {{y : INTEGER | ψ (IZR y) }} ->
    Γ |-- {{ϕ}} RE e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_coerce_tot {Γ} {e} {ϕ} {ψ} :
    Γ |-- [{ϕ}] e [{y : INTEGER | ψ (IZR y) }] ->
    Γ |-- [{ϕ}] RE e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_tot _ _ w _ _ _ p). 
  Defined.
  
  Lemma pp_ro_exp_prt {Γ} {e} {ϕ} {ψ} :
    Γ |-- {{ϕ}} e {{y : INTEGER | ψ (pow2 y) }} ->
    Γ |-- {{ϕ}} EXP e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_exp_tot {Γ} {e} {ϕ} {ψ} :
    Γ |-- [{ϕ}] e [{y : INTEGER | ψ (pow2 y) }] ->
    Γ |-- [{ϕ}] EXP e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_tot _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_recip_prt {Γ} {e} {ϕ} {θ} {ψ} :
    Γ |-- {{ϕ}} e {{y : REAL | θ y }} ->
    (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) -> 
    Γ |-- {{ϕ}} ;/; e {{y : REAL | ψ y}}.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_prt _ _ w _ _ _ _ p).
    exact H.
  Defined.

  Lemma pp_ro_recip_tot {Γ} {e} {ϕ} {θ} {ψ} :
    Γ |-- [{ϕ}] e [{y : REAL | θ y}] ->
    (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) -> 
    Γ |-- [{ϕ}] ;/; e [{y : REAL | ψ y}].
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_tot _ _ w _ _ _ _ p).
    exact H.
  Defined.
  
End UnaryOp.

Section BinaryOp.

  Lemma pp_ro_int_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :+: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :-: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :*: e2 {{y : INTEGER | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :<: e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : INTEGER | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : INTEGER | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    Γ |-- {{ϕ}} e1 :=: e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;+; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;-; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    Γ |-- {{ϕ}} e1 ;*; e2 {{y : REAL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- {{ϕ}} e1 {{y : REAL | ψ1 y}} ->
    Γ |-- {{ϕ}} e2 {{y : REAL | ψ2 y}} ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 -> ψ (Rltb'' y1 y2)%R x)) ->
    Γ |-- {{ϕ}} e1 ;<; e2 {{y : BOOL | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :+: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :-: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :*: e2 [{y : INTEGER | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :<: e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : INTEGER | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : INTEGER | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    Γ |-- [{ϕ}] e1 :=: e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;+; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;-; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    Γ |-- [{ϕ}] e1 ;*; e2 [{y : REAL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    Γ |-- [{ϕ}] e1 [{y : REAL | ψ1 y}] ->
    Γ |-- [{ϕ}] e2 [{y : REAL | ψ2 y}] ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 /\ ψ (Rltb'' y1 y2)%R x)) ->
    Γ |-- [{ϕ}] e1 ;<; e2 [{y : BOOL | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

End BinaryOp.

Section Limits.
  Lemma pp_ro_lim_prt {Γ} {e} {ϕ : sem_ro_ctx Γ -> Prop} {θ} {ψ} :
    (INTEGER :: Γ) |-- [{fun x => ϕ (snd x)}] e [{y : REAL | θ y}] ->
    (forall γ : sem_ro_ctx Γ, ϕ γ ->
                              exists y, ψ y γ /\
                                          forall x z, θ z (x, γ) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    Γ |-- {{ϕ}} Lim e {{y : REAL | ψ y}}.
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    apply (ro_lim_prt _ _ _ _ _ _ _ p X).
  Defined.

  Lemma pp_ro_lim_tot {Γ} {e} {ϕ : sem_ro_ctx Γ -> Prop} {θ} {ψ} :
    (INTEGER :: Γ) |-- [{fun x => ϕ (snd x)}] e [{y : REAL | θ y}] ->
    (forall γ : sem_ro_ctx Γ, ϕ γ ->
                              exists y, ψ y γ /\
                                          forall x z, θ z (x, γ) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    Γ |-- [{ϕ}] Lim e [{y : REAL | ψ y}].
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    apply (ro_lim_tot _ _ _ _ _ _ _ p X).
  Defined.
End Limits.

Section Commands.

  Lemma pp_rw_sequence_prt {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    Γ ;;; Δ ||-- {{ϕ}} c1 {{y : UNIT | θ y}} -> 
    Γ ;;; Δ ||-- {{θ tt}} c2 {{y : τ | ψ y}} -> 
    Γ ;;; Δ ||-- {{ϕ}} c1 ;; c2 {{y : τ | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.
  
  Lemma pp_rw_sequence_tot {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    Γ ;;; Δ ||-- [{ϕ}] c1 [{y : UNIT | θ y}] -> 
    Γ ;;; Δ ||-- [{θ tt}] c2 [{y : τ | ψ y}] -> 
    Γ ;;; Δ ||-- [{ϕ}] c1 ;; c2 [{y : τ | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.  
  
  Lemma pp_rw_new_var_prt {Γ Δ} {e} {c} {τ σ} {ϕ} {θ} {ψ}:
    (Δ ++ Γ) |-- {{fun x => ϕ (tedious_sem_app _ _ x)}} e {{y : σ | θ y}} -> 
    Γ ;;; (σ :: Δ) ||-- {{fun x => θ (fst (fst x)) (tedious_prod_sem _ _ (snd (fst x), snd x))}}
      c
      {{y : τ | fun x => ψ y (snd (fst x), snd x)}} -> 
    Γ ;;; Δ ||-- {{ϕ}} NEWVAR e IN c {{y : τ | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.

  Lemma pp_rw_new_var_tot {Γ Δ} {e} {c} {τ σ} {ϕ} {θ} {ψ}:
    (Δ ++ Γ) |-- [{fun x => ϕ (tedious_sem_app _ _ x)}] e [{y : σ | θ y}] -> 
    Γ ;;; (σ :: Δ) ||-- [{fun x => θ (fst (fst x)) (tedious_prod_sem _ _ (snd (fst x), snd x))}]
      c
      [{y : τ | fun x => ψ y (snd (fst x), snd x)}] -> 
    Γ ;;; Δ ||-- [{ϕ}] NEWVAR e IN c [{y : τ | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.

  
  Lemma pp_rw_assign_prt {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : post}
        (a : assignable Δ τ k) :
    (Δ ++ Γ) |-- {{fun x => ϕ (tedious_sem_app _ _ x)}} e {{y : τ | θ y}} -> 
    (forall x γ δ, θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    Γ ;;; Δ ||-- {{ϕ}} LET k := e {{y : UNIT | ψ y}}.
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ p1).
    unfold update'.
    intros.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.

  Lemma pp_rw_assign_tot {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : post}
        (a : assignable Δ τ k) :
    (Δ ++ Γ) |-- [{fun x => ϕ (tedious_sem_app _ _ x)}] e [{y : τ | θ y}] -> 
    (forall x γ δ, θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    Γ ;;; Δ ||-- [{ϕ}] LET k := e [{y : UNIT | ψ y}].
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    apply (rw_assign_tot _ _ _ _ _ _ _ _ _ _ p1).
    unfold update'.
    intros.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.
  
  Lemma pp_rw_cond_prt {Γ Δ} {e} {c1 c2} {τ}
        (* (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) *)
        {ϕ} {θ} {ψ} :
    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e {{y : BOOL | θ y}} ->
    Γ ;;; Δ ||-- {{ro_to_rw_pre (θ true)}} c1 {{y : τ | ψ y}} ->
    Γ ;;; Δ ||-- {{ro_to_rw_pre (θ false)}} c2 {{y : τ | ψ y}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- {{ϕ}} Cond e c1 c2 {{y : τ | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 p3).
  Defined.
  
  Lemma pp_rw_cond_tot {Γ Δ} {e} {c1 c2} {τ}
        (* (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) *)
        {ϕ} {θ} {ψ} :
    (Δ ++ Γ) |-- [{rw_to_ro_pre ϕ}] e [{y : BOOL | θ y}] ->
    Γ ;;; Δ ||-- [{ro_to_rw_pre (θ true)}] c1 [{y : τ | ψ y}] ->
    Γ ;;; Δ ||-- [{ro_to_rw_pre (θ false)}] c2 [{y : τ | ψ y}] ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- [{ϕ}] Cond e c1 c2 [{y : τ | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    apply (rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 p3).
  Defined.
  
  Lemma pp_rw_case_prt {Γ Δ} {e1 e2 c1 c2} {τ}
        (* (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) *)
        {ϕ} {θ1} {θ2} {ψ} :
    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e1 {{y : BOOL | θ1 y}} -> 
    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e2 {{y : BOOL | θ2 y}} -> 
    Γ ;;; Δ ||-- {{ro_to_rw_pre (θ1 true)}} c1 {{y : τ | ψ y}} -> 
    Γ ;;; Δ ||-- {{ro_to_rw_pre (θ2 true)}} c2 {{y : τ | ψ y}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- {{ϕ}} Case e1 c1 e2 c2 {{y : τ | ψ y}}.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3] [w4 p4].
    exists (has_type_rw_Case _ _ _ _ _ _ _ w1 w3 w2 w4).
    apply (rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 p3 p4).
  Defined.

  Lemma pp_rw_case_tot {Γ Δ} {e1 e2 c1 c2} {τ}
        (* (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) *)
        {ϕ} {θ1} {θ2} {ψ} {ϕ1 ϕ2}:
    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e1 {{y : BOOL | θ1 y}} -> 
    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e2 {{y : BOOL | θ2 y}} -> 
    Γ ;;; Δ ||-- [{ro_to_rw_pre (θ1 true)}] c1 [{y : τ | ψ y}] -> 
    Γ ;;; Δ ||-- [{ro_to_rw_pre (θ2 true)}] c2 [{y : τ | ψ y}] ->
    (Δ ++ Γ) |-- [{ϕ1}] e1 [{y : BOOL | fun _ => y = true}] -> 
    (Δ ++ Γ) |-- [{ϕ2}] e2 [{y : BOOL | fun _ => y = true}] ->
    (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x)) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- [{ϕ}] Case e1 c1 e2 c2 [{y : τ | ψ y}].
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3] [w4 p4] [w5 p5] [w6 p6] h.
    exists (has_type_rw_Case _ _ _ _ _ _ _ w1 w3 w2 w4).
    apply (ro_tot_change_wty w1) in p5.
    apply (ro_tot_change_wty w2) in p6.
    apply (rw_case_tot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p1 p2 p3 p4 p5 p6 h).
  Defined.

  Lemma pp_rw_case_list_prt {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
        (* (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l) *)
        (* (wty : Γ ;;; Δ ||- CaseList l : τ) *)
        (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
        {ϕ} {ψ} :
    ForallT1 _ (fun ec (θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
                =>
                  ((Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} fst ec {{y : BOOL | θ y}}) *
                    (Γ ;;; Δ ||-- {{ro_to_rw_pre (θ true)}} snd ec {{y : τ | ψ y}}))%type l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- {{ϕ}} CaseList l {{y : τ | ψ y}}.
  Proof.
    intros.
    assert (ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l).
    clear h.
    dependent induction X.
    apply ForallT_nil.
    apply ForallT_cons.
    destruct r.
    destruct p0.
    destruct p1.
    auto.
    apply (IHX).
    exists (has_type_rw_CaseList _ _ _ _ h H).
    apply (rw_case_list_prt _ _ _ _ H _ θ).
    clear h.
    induction l.
    dependent destruction X.
    dependent destruction H.
    apply ForallT2_nil.
    dependent destruction X.
    
    dependent destruction H.
    apply ForallT2_cons.
    apply IHl.
    exact X.
    clear IHl.
    destruct p0.
    destruct p0.
    split.
    apply (ro_prt_change_wty (fst p1)) in p0.
    exact p0.
    destruct p2.
    apply (rw_prt_change_wty (snd p1)) in p2.
    exact p2.
  Defined.

  Lemma pp_rw_case_list_tot {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
        (* (wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l) *)
        (* (wty : Γ ;;; Δ ||- CaseList l : τ) *)
        (θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l)
        (ϕi : ForallT (fun _ => sem_ro_ctx (Δ ++ Γ) -> Prop) l)
        {ϕ} {ψ} :
    ForallT2 _ _ (fun ec θ ϕi =>
                    ((Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} fst ec {{y : BOOL | θ y}}) *
                      (Γ ;;; Δ ||-- [{ro_to_rw_pre (θ true)}] snd ec [{y : τ | ψ y}]) *
                      ((Δ ++ Γ) |-- [{ϕi}] fst ec [{y : BOOL | fun _ => y = true}])
                 )%type l θ ϕi  ->
    (forall x : sem_ro_ctx (Δ ++ Γ),
        rw_to_ro_pre ϕ x ->
        ForallT_disj (fun _ : exp * exp => sem_ro_ctx (Δ ++ Γ) -> Prop)
                     (fun (_ : exp * exp) (ϕi0 : sem_ro_ctx (Δ ++ Γ) -> Prop) => ϕi0 x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||-- [{ϕ}] CaseList l [{y : τ | ψ y}].
  Proof.
    intros X HH.
    assert (ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l).
    {
      clear h HH.
      dependent induction X.
      apply ForallT_nil.
      apply ForallT_cons.
      destruct r.
      destruct p0.
      destruct p1.
      destruct p0.
      destruct p2.
      auto.
      apply (IHX).
    }
    exists (has_type_rw_CaseList _ _ _ _ h H).
    apply (rw_case_list_tot _ _ _ _ H _ θ ϕi).
    clear h HH.
    induction l.
    dependent destruction X.
    dependent destruction H.
    apply ForallT3_nil.
    dependent destruction X.
    
    dependent destruction H.
    apply ForallT3_cons.
    apply IHl.
    exact X.
    clear IHl.
    destruct p0.
    destruct p0.
    destruct p0.
    destruct p3.
    destruct p2.
    repeat split.
    apply (ro_prt_change_wty (fst p1)) in p0.
    exact p0.
    apply (rw_tot_change_wty (snd p1)) in p3.
    exact p3.
    apply (ro_tot_change_wty (fst p1)) in p2.
    exact p2.
    exact HH.
  Defined.
  
  Lemma pp_rw_while_prt {Γ Δ} {e c}
        (* (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) *)
        {ϕ} {θ} :

    (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}} e {{y : BOOL | θ y}} -> 
    Γ ;;; Δ ||-- {{ro_to_rw_pre (θ true)}} c {{y : UNIT | ϕ }} -> 
    Γ ;;; Δ ||-- {{ϕ}} While e c {{y : UNIT | (ϕ /\\ ro_to_rw_pre (θ false))}}.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_While _ _ _ _ w1 w2).
    apply (rw_while_prt _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.

  Lemma pp_rw_while_tot {Γ Δ} {e c}
        (* (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) *)
        {ϕ} {θ} {ψ}:

    (Δ ++ Γ) |-- [{rw_to_ro_pre ϕ}] e [{y : BOOL | θ y}] ->
    Γ ;;; Δ ||-- [{ro_to_rw_pre (θ true)}] c [{y : UNIT | ϕ }] -> 
    (Γ ++ Δ) ;;; Δ ||-- [{(fun x =>  ro_to_rw_pre (θ true) (fst x, fst_app (snd x)) /\ fst x = snd_app (snd x))}] c [{y : UNIT | ψ }] ->
    (forall δ γ,
        ϕ (δ, γ) -> ~ (exists f : nat -> sem_ro_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ (f (S n), (γ; f n))))) -> 
    Γ ;;; Δ ||-- [{ϕ}] While e c [{y : UNIT | (ϕ /\\ ro_to_rw_pre (θ false))}].
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3] h.
    exists (has_type_rw_While _ _ _ _ w1 w2).
    apply (rw_while_tot _ _ _ _ _ _ _  _ _ _ _ p1 p2 p3 h).
Defined.  
  

End Commands.



