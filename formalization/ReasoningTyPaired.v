Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals ZArith.
From Clerical Require Import Preliminaries.Preliminaries Powerdomain.Powerdomain Syntax Typing TypingProperties Semantics SemanticsProperties Specification ReasoningRules.

Definition proves_ro_prt_pp Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ }.

Definition proves_ro_tot_pp Γ e τ ϕ ψ :=
  {w : Γ |- e : τ & [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ }.

Definition proves_rw_prt_pp Γ Δ e τ ϕ ψ :=
  {w : Γ  ;;; Δ ||- e : τ & [x : Γ ;;; y : Δ] ||- w {{ϕ (x, y)}} e {{z : τ | ψ (x, (y, z))}}ᵖ }.

Definition proves_rw_tot_pp Γ Δ e τ ϕ ψ :=
  {w : Γ  ;;; Δ ||- e : τ & [x : Γ ;;; y : Δ] ||- w {{ϕ (x, y)}} e {{z : τ | ψ (x, (y, z))}}ᵗ }.


Notation "[ x ':' Γ ]  '|-' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵖ' " :=
  (proves_ro_prt_pp Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)) (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.

Notation "[ x ':' Γ ] '|-' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵗ' " :=
  (proves_ro_tot_pp Γ e τ (fun x => ϕ) (fun '(x, y) => ψ)) (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.

Notation "[ x :  Γ  ;;;   z : Δ ]  ||- {{ ϕ }} e {{ y : τ | ψ }}ᵖ " :=
  (proves_rw_prt_pp Γ Δ e τ (fun '(x, z) => ϕ) (fun '(x, (z, y)) => ψ)) (at level 50, Γ, Δ, y,  ϕ, e, y, τ, ψ at next level, x pattern , z pattern) : clerical_scope.

Notation "[ x :  Γ  ;;;  z : Δ ] ||- {{ ϕ }} e {{ y : τ | ψ }}ᵗ " :=
  (proves_rw_tot_pp Γ Δ e τ (fun '(x, z) => ϕ) (fun '(x, (z, y)) => ψ)) (at level 50, Γ, Δ, y,  ϕ, e, y, τ, ψ at next level, x pattern , z pattern) : clerical_scope.





(* Lemma ro_prt_change_wty {Γ} {e} {τ} {w : Γ |- e : τ} (w' : Γ |- e : τ) {ϕ} {ψ} (p : w |- {{ϕ}} e {{ψ}}) : w' |- {{ϕ}} e {{ψ}}. *)
(* Proof. *)
(*   apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)

(* Lemma ro_tot_change_wty {Γ} {e} {τ} {w : Γ |- e : τ} (w' : Γ |- e : τ) {ϕ} {ψ} (p : w |- [{ϕ}] e [{ψ}]) : w' |- [{ϕ}] e [{ψ}]. *)
(* Proof. *)
(*   apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)

(* Lemma rw_prt_change_wty {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} (w' : Γ ;;; Δ ||- e : τ) {ϕ} {ψ} (p : w ||- {{ϕ}} e {{ψ}}) : w' ||- {{ϕ}} e {{ψ}}. *)
(* Proof. *)
(*   apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)


(* Lemma rw_tot_change_wty {Γ Δ} {e} {τ} {w : Γ ;;; Δ ||- e : τ} (w' : Γ ;;; Δ ||- e : τ) {ϕ} {ψ} (p : w ||- [{ϕ}] e [{ψ}]) : w' ||- [{ϕ}] e [{ψ}]. *)
(* Proof. *)
(*   apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)

Section LogicalRules.
  
  Lemma pp_ro_imply_prt {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ ->
               ϕ' ->> ϕ -> ψ ->> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' (γ, y)}}ᵖ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_imply_tot {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ ->
               ϕ' ->> ϕ -> ψ ->> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' (γ, y)}}ᵗ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (ro_imply_tot _ _ _ _ _ _ _ _ _ p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

    
  Lemma pp_rw_imply_prt {Γ Δ} {e} {τ} {ϕ ϕ' :pred} {ψ ψ' : pred} :
    [ γ : Γ ;;; δ : Δ ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ ->
    (ϕ' ->> ϕ) -> (ψ ->> ψ') ->
    [ γ : Γ ;;; δ : Δ ]  ||- {{ϕ' (γ, δ)}} e {{y : τ | ψ' (γ, (δ, y))}}ᵖ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (rw_imply_prt _ _ _ _ _ _ _ _ _ _ p); auto.
  Defined.

  Lemma pp_rw_imply_tot {Γ Δ} {e} {τ} {ϕ ϕ' : pred} {ψ ψ' : pred} :
    [ γ : Γ ;;; δ : Δ ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ ->
    (ϕ' ->> ϕ) -> (ψ ->> ψ') ->
    [ γ : Γ ;;; δ : Δ ]  ||- {{ϕ' (γ, δ)}} e {{y : τ | ψ' (γ, (δ, y))}}ᵗ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (rw_imply_tot _ _ _ _ _ _ _ _ _ _ p); auto.
  Defined.

End LogicalRules.


Section ROAndRW.

  Lemma pp_ro_rw_prt {Γ} {c} {τ} {ϕ} {ψ} :
    [γ : Γ ;;; _ : nil] ||- {{ϕ (γ, tt)}} c {{y : τ | ψ (γ, (tt, y))}}ᵖ -> 
    [γ : Γ] |- {{ϕ (γ, tt)}} c {{y : τ | ψ (γ, (tt, y))}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_prt _ _ _ _ _ _ _ p).
  Defined.
  
  Lemma pp_ro_rw_tot {Γ} {c} {τ} {ϕ} {ψ} :
    [γ : Γ ;;; _ : nil] ||- {{ϕ (γ, tt)}} c {{y : τ | ψ (γ, (tt, y))}}ᵗ -> 
    [γ : Γ] |- {{ϕ (γ, tt)}} c {{y : τ | ψ (γ, (tt, y))}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_tot _ _ _ _ _ _ _ p).
  Defined.

  Lemma pp_rw_ro_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    [x : Γ +++ Δ] |- {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ -> 
                    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ ; δ) }} e {{y : τ | ψ ((γ ; δ), y)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    exact (rw_ro_prt _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ e τ w) p).
  Defined.

  Lemma pp_rw_ro_tot {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    [x : Γ +++ Δ] |- {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ -> 
                    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ ; δ) }} e {{y : τ | ψ ((γ ; δ), y)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    exact (rw_ro_tot _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ e τ w) p).
  Defined.
  
End ROAndRW.


Section VariablesAndConstants.

  Lemma pp_ro_var_prt {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      [γ : Γ] |- {{(ψ (γ, var_access Γ k τ w γ))}} VAR k {{y : τ | ψ (γ, y) }}ᵖ.
  Proof.
    intros.
    exists w.
    exact (ro_var_prt _ _ _ w ψ).
  Defined.

  Lemma pp_ro_var_tot {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      [γ : Γ] |- {{(ψ (γ, var_access Γ k τ w γ))}} VAR k {{y : τ | ψ (γ, y) }}ᵗ.
  Proof.
    intros.
    exists w.
    exact (ro_var_tot _ _ _ w ψ).
  Defined.
  
  Lemma pp_ro_skip_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, tt)}} SKIP {{y : UNIT | ψ (γ, y)}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    exact (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
  Defined.

  Lemma pp_ro_skip_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, tt)}} SKIP {{y : UNIT | ψ (γ, y)}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    exact (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
  Defined.
  
  Lemma pp_ro_true_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, true)}} TRUE {{y : BOOL | ψ (γ, y)}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    exact (ro_true_prt _  (has_type_ro_True Γ) ψ).
  Defined.

  Lemma pp_ro_true_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, true)}} TRUE {{y : BOOL | ψ (γ, y)}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    exact (ro_true_tot _  (has_type_ro_True Γ) ψ).
  Defined.
  
  Lemma pp_ro_false_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, false)}} FALSE {{y : BOOL | ψ (γ, y)}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    exact (ro_false_prt _  (has_type_ro_False Γ) ψ).
  Defined.

  Lemma pp_ro_false_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ (γ, false)}} FALSE {{y : BOOL | ψ (γ, y)}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    exact (ro_false_tot _  (has_type_ro_False Γ) ψ).
  Defined.
  
  Lemma pp_ro_int_prt {Γ} {k} {ψ} :
    [γ : Γ] |- {{ψ (γ, k)}} INT k {{y : INTEGER | ψ (γ, y)}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    exact (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
  Defined.

  Lemma pp_ro_int_tot {Γ} {k} {ψ} :
    [γ : Γ] |- {{ψ (γ, k)}} INT k {{y : INTEGER | ψ (γ, y)}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    exact (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
  Defined.

End VariablesAndConstants.

Section UnaryOp.
  Lemma pp_ro_coerce_prt {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (γ, IZR y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} RE e {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_coerce_tot {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (γ, IZR y) }}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} RE e {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_tot _ _ w _ _ _ p). 
  Defined.
  
  Lemma pp_ro_exp_prt {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (γ, pow2 y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} EXP e {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_exp_tot {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (γ, pow2 y) }}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} EXP e {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_tot _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_recip_prt {Γ} {e} {ϕ} {θ} {ψ : pred} :
    [γ : Γ] |- {{ϕ γ}} e {{y : REAL | θ (γ, y)}}ᵖ ->
    (forall (γ : sem_ctx Γ) (x : sem_datatype REAL), θ (γ, x) /\ x <> 0 -> ψ (γ, / x)) ->
    [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_prt _ _ w _ _ _ _ p).
    exact H.
  Defined.

  Lemma pp_ro_recip_tot {Γ} {e} {ϕ} {θ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : REAL | θ (γ, y)}}ᵗ ->
               (forall (γ : sem_ctx Γ) (x : sem_datatype REAL), θ (γ, x) -> x <> 0 /\ ψ (γ, / x)) ->
               [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_tot _ _ w _ _ _ _ p).
    exact H.
  Defined.
  
End UnaryOp.

Section BinaryOp.

  Lemma pp_ro_int_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zplus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :+: e2 {{y : INTEGER | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zminus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :-: e2 {{y : INTEGER | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zmult y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :*: e2 {{y : INTEGER | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Z.ltb y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :<: e2 {{y : BOOL | ψ (γ, y)}}ᵖ. 
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Z.eqb y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :=: e2 {{y : BOOL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rplus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;+; e2 {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rminus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;-; e2 {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rmult y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;*; e2 {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵖ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> y1 <> y2 -> ψ (x, Rltb'' y1 y2)%R) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zplus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :+: e2 {{y : INTEGER | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zminus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :-: e2 {{y : INTEGER | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Zmult y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :*: e2 {{y : INTEGER | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Z.ltb y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :<: e2 {{y : BOOL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Z.eqb y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 :=: e2 {{y : BOOL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rplus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;+; e2 {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rminus y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;-; e2 {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> ψ (x, Rmult y1 y2)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;*; e2 {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : pred} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
    (forall x y1 y2, ψ1 (x, y1) -> ψ2 (x, y2) -> (y1 <> y2 /\ ψ (x, Rltb'' y1 y2)%R)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

End BinaryOp.

Section Limits.
  Lemma pp_ro_lim_prt {Γ} {e} {ϕ : pred} {θ : pred} {ψ} :
    [ (γ, z) : (Γ ::: INTEGER) ] |- {{ ϕ γ }} e {{y : REAL | θ ((γ, z), y) }}ᵗ ->
    (forall γ : sem_ctx Γ, ϕ γ ->
                           exists y, ψ (γ, y) /\
                                       forall x z, θ ((γ, x), z) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵖ.
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    pose proof (ro_lim_prt _ _ w ϕ θ (  has_type_ro_Lim Γ e w)  ψ).
    apply X0; auto.
  Defined.

  Lemma pp_ro_lim_tot {Γ} {e} {ϕ : pred} {θ : pred} {ψ} :
    [ (γ, z) : (Γ ::: INTEGER) ] |- {{ ϕ γ }} e {{y : REAL | θ ((γ, z), y) }}ᵗ ->
    (forall γ : sem_ctx Γ, ϕ γ ->
                           exists y, ψ (γ, y) /\
                                       forall x z, θ ((γ, x), z) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵗ.
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    pose proof (ro_lim_tot _ _ w ϕ θ (  has_type_ro_Lim Γ e w)  ψ).
    apply X0; auto.
  Defined.
End Limits.

Section Commands.

  Lemma pp_rw_sequence_prt {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} c1 {{y : UNIT | θ (γ, (δ, y))}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ (γ, (δ, tt))}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} c1 ;; c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.
  
  Lemma pp_rw_sequence_tot {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} c1 {{y : UNIT | θ (γ, (δ, y))}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ (γ, (δ, tt))}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} c1 ;; c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.  

  Lemma pp_rw_new_var_var {Γ Δ} {e} {c} {τ σ} {ϕ} {θ} {ψ}:
    [ x : (Γ +++ Δ) ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵖ -> 
    [ γ : Γ  ;;; (δ, z) : Δ ::: σ] ||- {{θ ((γ; δ), z)}} c {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (NEWVAR e IN c) {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    simpl in p2.
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Newvar Γ Δ e c σ τ w1 w2 ) p1 p2).
  Defined.

  
  Lemma pp_rw_new_var_tot {Γ Δ} {e} {c} {τ σ} {ϕ} {θ} {ψ}:
    [ x : (Γ +++ Δ) ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵗ -> 
    [ γ : Γ  ;;; (δ, z) : Δ ::: σ] ||- {{θ ((γ; δ), z)}} c {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (NEWVAR e IN c) {{y : τ | ψ (γ, (δ, y))}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2].
    simpl in p2.
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    apply (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Newvar Γ Δ e c σ τ w1 w2 ) p1 p2).
  Defined.

  Lemma tedious_equiv_4 Γ Δ x : tedious_sem_app Δ Γ x = (fst_app x, snd_app x).
  Proof.
    unfold  fst_app, snd_app.
    destruct (tedious_sem_app Δ Γ x); auto.
  Defined.
  
  Lemma pp_rw_assign_prt {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : pred}
        (a : assignable Δ τ k) :
       [x : (Γ +++ Δ)]|- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y) }}ᵖ ->
       (forall (γ : sem_ctx Γ) (δ : sem_ctx Δ) (x : sem_datatype τ), θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
       [γ : Γ ;;; δ : Δ]||- {{ϕ (γ, δ)}} (LET k := e) {{y : UNIT | ψ (γ, (δ, y)) }}ᵖ.
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    apply  (rw_assign_prt _ _ _ _ _ w1 ϕ θ ψ (  has_type_rw_Assign Γ Δ e τ k a w1) ); auto.
    intros.
    unfold update'.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.

  Lemma pp_rw_assign_tot {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : pred}
        (a : assignable Δ τ k) :
       [x : (Γ +++ Δ)]|- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y) }}ᵗ ->
       (forall (γ : sem_ctx Γ) (δ : sem_ctx Δ) (x : sem_datatype τ), θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
       [γ : Γ ;;; δ : Δ]||- {{ϕ (γ, δ)}} (LET k := e) {{y : UNIT | ψ (γ, (δ, y)) }}ᵗ.
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    apply  (rw_assign_tot _ _ _ _ _ w1 ϕ θ ψ (  has_type_rw_Assign Γ Δ e τ k a w1) ); auto.
    intros.
    unfold update'.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.  
  
  Lemma pp_rw_cond_prt {Γ Δ} {e} {c1 c2} {τ}
    {ϕ} {θ} {ψ} :
    [x : (Γ +++ Δ)] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y) }}ᵖ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y)) }}ᵖ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y)) }}ᵖ ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (IF e THEN c1 ELSE c2 END) {{y : τ | ψ (γ, (δ, y)) }}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _
                  (  has_type_rw_Cond Γ Δ e c1 c2 τ w1 w2 w3)
                  _ _ _ p1 p2 p3 ).
  Defined.

  Lemma pp_rw_cond_tot {Γ Δ} {e} {c1 c2} {τ}
    {ϕ} {θ} {ψ} :
    [x : (Γ +++ Δ)] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y) }}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y)) }}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y)) }}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (IF e THEN c1 ELSE c2 END) {{y : τ | ψ (γ, (δ, y)) }}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    apply (rw_cond_tot _ _ _ _ _ _ _ _ _
                       (  has_type_rw_Cond Γ Δ e c1 c2 τ w1 w2 w3)
                       _ _ _ p1 p2 p3 ).
  Defined.

  Lemma pp_rw_case_list_prt {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
    (θ : ForallT (fun _ => sem_ctx (Γ +++ Δ) * bool  -> Prop) l)
    {ϕ} {ψ} :   
    ForallT1 _ (fun ec (θ : sem_ctx (Γ +++ Δ) * bool -> Prop)
                =>
                  ([x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ) *
                    ([γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ))%type l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  Proof.
    intros.
    assert (ForallT (fun ec => ((Γ +++ Δ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l).
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
    
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ p0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct p2.

    apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf p2);
      try (intros [h1 h2] h3; auto); try (intros h1 [h2 h3] h4; auto); auto.
    auto.
    auto.
  Defined.

  Lemma pp_rw_case_list_tot {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
    (θ : ForallT (fun _ => sem_ctx (Γ +++ Δ) * bool -> Prop) l)
    (ϕi : ForallT (fun _ => sem_ctx (Γ +++ Δ) -> Prop) l)
    {ϕ} {ψ} :
    ForallT2 _ _ (fun ec θ ϕi =>
                    ([x  : (Γ +++ Δ)] |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ)
                    *
                      ([γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵗ) *
                      ([x : Γ +++ Δ] |- {{ϕi x}} fst ec {{y : BOOL | y = true}}ᵗ)
                 )%type l θ ϕi  ->
    (forall x : sem_ctx (Γ +++ Δ),
        ϕ (fst_app x, snd_app x) ->
        ForallT_disj (fun _ : exp * exp => sem_ctx (Γ +++ Δ) -> Prop)
          (fun (_ : exp * exp) (ϕi0 : sem_ctx (Γ +++ Δ) -> Prop) => ϕi0 x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵗ.
  Proof.
    intros X HH.
    assert (ForallT (fun ec => ((Γ +++ Δ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ))%type l).
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
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ p0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) => ψ (γ, (δ, y))) p3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    auto.
    destruct h1.
    destruct p4.
    auto.
    apply (ro_imply_tot _ _ _ _ _ _ patf _ patf p2).
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros [h1 h2] h3; auto.
    intros.
    apply HH.
    exact H0.
  Defined.

    Lemma pp_rw_case_prt {Γ Δ} {e1 e2 c1 c2} {τ}
      {ϕ} {θ1} {θ2} {ψ} :
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 (x, y)}}ᵖ -> 
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 (x, y)}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ1 ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ2 ((γ; δ), true)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  Proof.
    intros.
    assert (1 <= length ((e1, c1) :: (e2, c2) :: nil))%nat.
    simpl; auto.
    apply (pp_rw_case_list_prt H
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) θ1
                           (ForallT_cons _ (e2, c2) nil θ2
                                         (ForallT_nil _)))).
    apply ForallT1_cons.
    apply ForallT1_cons.
    apply ForallT1_nil.
    split; auto.
    split; auto.
  Defined.

  Lemma pp_rw_case_tot {Γ Δ} {e1 e2 c1 c2} {τ}
    {ϕ} {θ1} {θ2} {ψ} {ϕ1 ϕ2}:
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 (x, y)}}ᵖ -> 
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 (x, y)}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ1 ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ2 ((γ; δ), true)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
    [x : Γ +++ Δ] |- {{ϕ1 x}} e1 {{y : BOOL | y = true}}ᵗ -> 
    [x : Γ +++ Δ] |- {{ϕ2 x}} e2 {{y : BOOL | y = true}}ᵗ -> 
    (forall x, (ϕ (fst_app x, snd_app x) -> (ϕ1 x \/ ϕ2 x))) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ (γ, (δ, y))}}ᵗ.
  Proof.
    intros.
    assert (1 <= length ((e1, c1) :: (e2, c2) :: nil))%nat.
    simpl; auto.
    apply (pp_rw_case_list_tot H0
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) θ1
                           (ForallT_cons _ (e2, c2) nil θ2
                                         (ForallT_nil _)))
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) ϕ1
                           (ForallT_cons _ (e2, c2) nil ϕ2
                                         (ForallT_nil _)))).
    apply ForallT2_cons.
    apply ForallT2_cons.
    apply ForallT2_nil.
    repeat split; auto.
    repeat split; auto.
    simpl.
    intros.
    destruct (H x H1); auto.
  Defined.

  
  Lemma pp_rw_while_prt {Γ Δ} {e c}
    {ϕ} {θ} :
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} c {{y : UNIT | ϕ (γ, δ) }}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} While e c {{y : UNIT | ϕ (γ, δ) /\ θ ((γ; δ), false)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_While _ _ _ _ w1 w2).    
    apply (rw_while_prt _ _ _ _ _ _ (  has_type_rw_While Γ Δ e c w1 w2)  _ _  p1 p2).
  Defined.
  
  Lemma pp_rw_while_tot {Γ Δ} {e c}
    {ϕ} {θ} {ψ}:
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} c {{y : UNIT | ϕ (γ, δ) }}ᵗ -> 
    [x : (Δ +++ Γ) ;;;  δ : Δ] ||- {{(θ ((snd_app x; δ), true) /\ δ = fst_app x)}} c {{_ : UNIT | ψ (x, δ) }}ᵗ ->
    (forall (γ : sem_ctx Γ) (δ : sem_ctx Δ),
        ϕ (γ, δ) -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ ((f n; γ), f (S n))))) ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} While e c {{y : UNIT | ϕ (γ, δ) /\ θ ((γ; δ), false)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3] h.
    exists (has_type_rw_While _ _ _ _ w1 w2).
    apply (rw_while_tot _ _ _ _ _ _ _ (has_type_rw_While Γ Δ e c w1 w2) _ _ _ p1 p2 p3 h).
  Defined.
  
End Commands.
