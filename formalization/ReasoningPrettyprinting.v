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

(* Notation " Γ '|--' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}' " := *)
(*   (proves_ro_prt_pp Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope. *)

(* Notation " Γ '|--' '[{' ϕ '}]' e '[{' y ':' τ '|' ψ '}]' " := *)
(*   (proves_ro_tot_pp Γ e τ ϕ (fun y => ψ)) (at level 50, ϕ, e, y, τ, ψ at next level) : clerical_scope. *)

(* Notation " Γ ';;;' Δ '||--' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}' " := *)
(*   (proves_rw_prt_pp Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope. *)

(* Notation " Γ ';;;' Δ '||--' '[{' ϕ '}]' e '[{' y ':' τ '|' ψ '}]' " := *)
(*   (proves_rw_tot_pp Γ Δ e τ ϕ (fun y => ψ)) (at level 50, Δ, ϕ, e, y, τ, ψ at next level) : clerical_scope. *)




Notation "[ x ':' Γ ]  '|-' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵖ' " :=
  (proves_ro_prt_pp Γ e τ (fun x => ϕ) (fun y x => ψ)) (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.

Notation "[ x ':' Γ ] '|-' '{{' ϕ '}}' e '{{' y ':' τ '|' ψ '}}ᵗ' " :=
  (proves_ro_tot_pp Γ e τ (fun x => ϕ) (fun y x => ψ)) (at level 50, Γ, ϕ, e, y, τ, ψ at next level, x pattern) : clerical_scope.

Notation "[ x :  Γ ]  ;  [ z : Δ ] ||- {{ ϕ }} e {{ y : τ | ψ }}ᵖ " :=
  (proves_rw_prt_pp Γ Δ e τ (fun '(z, x) => ϕ) (fun y '(z, x) => ψ)) (at level 50, Γ, Δ, y,  ϕ, e, y, τ, ψ at next level, x pattern , z pattern) : clerical_scope.

Notation "[ x :  Γ ] ; [ z : Δ ] ||- {{ ϕ }} e {{ y : τ | ψ }}ᵗ " :=
  (proves_rw_tot_pp Γ Δ e τ (fun '(z, x) => ϕ) (fun y '(z, x) => ψ)) (at level 50, Γ, Δ, y,  ϕ, e, y, τ, ψ at next level, x pattern , z pattern) : clerical_scope.


Section LogicalRules.
  
  Lemma pp_ro_imply_prt {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵖ ->
               ϕ' ->> ϕ -> ψ ->>> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' y γ}}ᵖ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_imply_tot {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵗ ->
               ϕ' ->> ϕ -> ψ ->>> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' y γ}}ᵗ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_rw_imply_prt {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : post} :
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ) }}ᵖ ->
    ϕ' ->> ϕ -> ψ ->>> ψ' -> [γ : Γ] ; [δ : Δ]  ||- {{ϕ' (δ, γ)}} e {{y : τ | ψ' y (δ, γ)}}ᵖ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p); intros h1 h2.
    destruct h1; apply H; auto.
    intro.
    destruct h2; apply H0; auto.
  Defined.

  Lemma pp_rw_imply_tot {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ctx Δ * sem_ctx Γ -> Prop} :
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵗ -> ϕ' ->> ϕ -> ψ ->>> ψ' ->
              [γ : Γ] ; [δ : Δ] ||- {{ϕ' (δ, γ)}} e {{y : τ | ψ' y (δ, γ)}}ᵗ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; apply H; auto.
    intro.
    destruct h2; apply H0; auto.
  Defined.

End LogicalRules.


Section ROAndRW.

  Lemma pp_ro_rw_prt {Γ} {c} {τ} {ϕ} {ψ} :
    [γ : Γ] ; [_ : nil] ||- {{ϕ (tt, γ)}} c {{y : τ | ψ y (tt, γ)}}ᵖ -> 
    [γ : Γ] |- {{ϕ (tt, γ)}} c {{y : τ | ψ y (tt, γ)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_prt _ _ _ _ _ _ _ p).
  Defined.
  
  Lemma pp_ro_rw_tot {Γ} {c} {τ} {ϕ} {ψ} :
    [γ : Γ] ; [_ : nil] ||- {{ϕ (tt, γ)}} c {{y : τ | ψ y (tt, γ)}}ᵗ -> 
    [γ : Γ] |- {{ϕ (tt, γ)}} c {{y : τ | ψ y (tt, γ)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_rw _ _ _ w).
    apply (ro_rw_tot _ _ _ _ _ _ _ p).
  Defined.

  Lemma pp_rw_ro_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    [δγ : Δ ++ Γ] |- {{ϕ δγ}} e {{y : τ | ψ y δγ}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ ; γ)}} e {{y : τ | ψ y (δ; γ)}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    pose proof (rw_ro_prt _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ e τ w) p).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
  Defined.

  Lemma pp_rw_ro_tot {Γ Δ} {e} {τ} {ϕ} {ψ} : 
    [δγ : Δ ++ Γ] |- {{ϕ δγ}} e {{y : τ | ψ y δγ}}ᵗ -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ ; γ)}} e {{y : τ | ψ y (δ; γ)}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_rw_ro _ _ _ _ w).
    pose proof (rw_ro_tot _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ e τ w) p).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
  Defined.

End ROAndRW.


Section VariablesAndConstants.

  Lemma pp_ro_var_prt {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      [γ : Γ] |- {{(ψ (ro_access Γ k τ w γ) γ)}} VAR k {{y : τ | ψ y γ}}ᵖ.
  Proof.
    intros.
    exists w.
    pose proof (ro_var_prt _ _ _ w ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_var_tot {Γ} {k} {τ} {ψ} :
    forall w : Γ |- VAR k : τ, 
      [γ : Γ] |- {{(ψ (ro_access Γ k τ w γ) γ)}} VAR k {{y : τ | ψ y γ}}ᵗ.
  Proof.
    intros.
    exists w.
    pose proof (ro_var_tot _ _ _ w ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_skip_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ tt γ}} SKIP {{y : UNIT | ψ y γ}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_skip_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ tt γ}} SKIP {{y : UNIT | ψ y γ}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_Skip Γ).
    pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_true_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ true γ}} TRUE {{y : BOOL | ψ y γ}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_true_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ true γ}} TRUE {{y : BOOL | ψ y γ}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_True Γ).
    pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_false_prt {Γ} {ψ} :
    [γ : Γ] |- {{ψ false γ}} FALSE {{y : BOOL | ψ y γ}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_false_tot {Γ} {ψ} :
    [γ : Γ] |- {{ψ false γ}} FALSE {{y : BOOL | ψ y γ}}ᵗ.
  Proof.
    intros.
    exists (has_type_ro_False Γ).
    pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.
  
  Lemma pp_ro_int_prt {Γ} {k} {ψ} :
    [γ : Γ] |- {{ψ k γ}} INT k {{y : INTEGER | ψ y γ}}ᵖ.
  Proof.
    intros.
    exists (has_type_ro_Int Γ k).
    pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  Defined.

  Lemma pp_ro_int_tot {Γ} {k} {ψ} :
    [γ : Γ] |- {{ψ k γ}} INT k {{y : INTEGER | ψ y γ}}ᵗ.
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
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (IZR y)  γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} RE e {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_coerce_tot {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (IZR y) }}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} RE e {{y : REAL | ψ y}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRcoerce _ _ w).
    apply (ro_coerce_tot _ _ w _ _ _ p). 
  Defined.
  
  Lemma pp_ro_exp_prt {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (pow2 y)  γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} EXP e {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_prt _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_exp_tot {Γ} {e} {ϕ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : INTEGER | ψ (pow2 y) }}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} EXP e {{y : REAL | ψ y}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpZRexp _ _ w).
    apply (ro_exp_tot _ _ w _ _ _ p). 
  Defined.

  Lemma pp_ro_recip_prt {Γ} {e} {ϕ} {θ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : REAL | θ y  γ}}ᵖ ->
    (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) -> 
    [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_prt _ _ w _ _ _ _ p).
    exact H.
  Defined.

  Lemma pp_ro_recip_tot {Γ} {e} {ϕ} {θ} {ψ} :
    [γ : Γ] |- {{ϕ γ}} e {{y : REAL | θ y γ}}ᵗ ->
    (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) -> 
    [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ y γ}}ᵗ.
  Proof.
    intros [w p].
    exists (has_type_ro_OpRrecip _ _ w).
    apply (ro_recip_tot _ _ w _ _ _ _ p).
    exact H.
  Defined.
  
End UnaryOp.

Section BinaryOp.

  Lemma pp_ro_int_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :+: e2 {{y : INTEGER | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :-: e2 {{y : INTEGER | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :*: e2 {{y : INTEGER | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :<: e2 {{y : BOOL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :=: e2 {{y : BOOL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;+; e2 {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;-; e2 {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;*; e2 {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_prt {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵖ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵖ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 -> ψ (Rltb'' y1 y2)%R x)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ y γ}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zplus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :+: e2 {{y : INTEGER | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZplus _ _ _ w1 w2).
    apply (ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zminus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :-: e2 {{y : INTEGER | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZminus _ _ _ w1 w2).
    apply (ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Zmult y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :*: e2 {{y : INTEGER | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZmult _ _ _ w1 w2).
    apply (ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.ltb y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :<: e2 {{y : BOOL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZlt _ _ _ w1 w2).
    apply (ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_int_comp_eq_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : INTEGER | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : INTEGER | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Z.eqb y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 :=: e2 {{y : BOOL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpZeq _ _ _ w1 w2).
    apply (ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_plus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rplus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;+; e2 {{y : REAL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRplus _ _ _ w1 w2).
    apply (ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_minus_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rminus y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;-; e2 {{y : REAL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRminus _ _ _ w1 w2).
    apply (ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_op_mult_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> ψ (Rmult y1 y2) x) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;*; e2 {{y : REAL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRmult _ _ _ w1 w2).
    apply (ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

  Lemma pp_ro_real_comp_lt_tot {Γ} {e1 e2} {ϕ} {ψ : post} ψ1 ψ2 :
    [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 y γ}}ᵗ ->
    [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 y γ}}ᵗ ->
    (forall y1 y2 x, ψ1 y1 x -> ψ2 y2 x -> (y1 <> y2 /\ ψ (Rltb'' y1 y2)%R x)) ->
    [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ y γ}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] h.
    exists (has_type_ro_OpRlt _ _ _ w1 w2).
    apply (ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ p1 p2 h).
  Defined.

End BinaryOp.

Section Limits.
  Lemma pp_ro_lim_prt {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {θ : R -> (sem_ctx (INTEGER ::  Γ)) -> Prop} {ψ} :
    [ (z, γ) : (INTEGER :: Γ) ] |- {{ ϕ γ }} e {{y : REAL | θ y (z, γ) }}ᵗ ->
    (forall γ : sem_ctx Γ, ϕ γ ->
                              exists y, ψ y γ /\
                                          forall x z, θ z (x, γ) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ y γ}}ᵖ.
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    unfold pow2 in X.
    pose proof (ro_lim_prt _ _ w ϕ θ (  has_type_ro_Lim Γ e w)  ψ).
    assert (w |- [{(fun γ' : sem_ctx (INTEGER :: Γ) => ϕ (snd γ'))}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
    apply X0 in X1.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply X.
    exact H.
  Defined.

  Lemma pp_ro_lim_tot {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {θ : R -> (sem_ctx (INTEGER ::  Γ)) -> Prop} {ψ} :
    [ (z, γ) : (INTEGER :: Γ) ] |- {{ ϕ γ }} e {{y : REAL | θ y (z, γ) }}ᵗ ->
    (forall γ : sem_ctx Γ, ϕ γ ->
                              exists y, ψ y γ /\
                                          forall x z, θ z (x, γ) -> (Rabs (z - y)%R < pow2 (- x))%R) ->
    [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ y γ}}ᵗ.
  Proof.
    intros [w p] X.
    exists (has_type_ro_Lim _ _ w).
    unfold pow2 in X.
    pose proof (ro_lim_tot _ _ w ϕ θ (  has_type_ro_Lim Γ e w)  ψ).
    assert (w |- [{(fun γ' : sem_ctx (INTEGER :: Γ) => ϕ (snd γ'))}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
    apply X0 in X1.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply X.
    exact H.
  Defined.

End Limits.

Section Commands.

  Lemma pp_rw_sequence_prt {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} c1 {{y : UNIT | θ y (δ, γ)}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ tt (δ, γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} c1 ;; c2 {{y : τ | ψ y (δ, γ)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.
  
  Lemma pp_rw_sequence_tot {Γ Δ} {c1 c2} {τ} {ϕ} {θ} {ψ} :    
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} c1 {{y : UNIT | θ y (δ, γ)}}ᵗ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ tt (δ, γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵗ -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} c1 ;; c2 {{y : τ | ψ y (δ, γ)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
    apply (rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  Defined.  
  
  Lemma pp_rw_new_var_prt {Γ Δ} {e} {c} {τ σ} {ϕ} {θ}
    {ψ : sem_datatype τ -> sem_ctx Δ * sem_ctx Γ -> Prop }:
    [ δγ : Δ ++ Γ ] |- {{ϕ (fst_app δγ, snd_app δγ)}} e {{y : σ | θ y δγ}}ᵖ -> 
    [ γ : Γ ] ; [ (z, δ) : σ :: Δ] ||- {{θ z (δ ; γ)}}
                  c
                  {{y : τ | ψ y (δ, γ)}}ᵖ -> 
                [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} NEWVAR e IN c {{y : τ | ψ y (δ, γ)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    assert (w1 |- {{(fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ))}} e {{y | θ y}}).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1) in h2.
    unfold fst_app, snd_app in h2.
    unfold fst_app, snd_app.
    destruct (tedious_sem_app Δ Γ h1); auto.
    rewrite tedious_equiv_1 in h2.
    auto.
    assert (w2 ||- {{(fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ))}} c {{x | (fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => ψ x (snd (fst xδγ), snd xδγ))}}).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    destruct s; auto.
    destruct h2; auto.
    destruct s; auto.
    pose proof (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Newvar Γ Δ e c σ τ w1 w2 ) X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
  Defined.
  

  Lemma pp_rw_new_var_tot {Γ Δ} {e} {c} {τ σ} {ϕ} {θ}
    {ψ : sem_datatype τ -> sem_ctx Δ * sem_ctx Γ -> Prop }:
    [ δγ : Δ ++ Γ ] |- {{ϕ (fst_app δγ, snd_app δγ)}} e {{y : σ | θ y δγ}}ᵗ -> 
    [ γ : Γ ] ; [ (z, δ) : σ :: Δ] ||- {{θ z (δ ; γ)}}
                  c
                  {{y : τ | ψ y (δ, γ)}}ᵗ -> 
                [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} NEWVAR e IN c {{y : τ | ψ y (δ, γ)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).
    assert (w1 |- [{(fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ))}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1) in h2.
    unfold fst_app, snd_app in h2.
    unfold fst_app, snd_app.
    destruct (tedious_sem_app Δ Γ h1); auto.
    rewrite tedious_equiv_1 in h2.
    auto.
    assert (w2 ||- [{(fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ))}] c [{x | (fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => ψ x (snd (fst xδγ), snd xδγ))}]).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    destruct s; auto.
    destruct h2; auto.
    destruct s; auto.
    pose proof (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Newvar Γ Δ e c σ τ w1 w2 ) X X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; auto.
    destruct h2; auto.
  Defined.

  Lemma tedious_equiv_4 Γ Δ x : tedious_sem_app Δ Γ x = (fst_app x, snd_app x).
  Proof.
    unfold  fst_app, snd_app.
    destruct (tedious_sem_app Δ Γ x); auto.
  Defined.
  
    
  Lemma pp_rw_assign_prt {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : post}
    (a : assignable Δ τ k) :
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ y x}}ᵖ -> 
    (forall x γ δ, θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} LET k := e {{y : UNIT | ψ y (δ, γ)}}ᵖ.
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    pose proof (rw_assign_prt _ _ _ _ _ w1 ϕ θ ψ (  has_type_rw_Assign Γ Δ e τ k a w1) ).
    assert (w1 |- {{(fun δγ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ δγ))}} e {{y | θ y}}).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_4 in h2; auto.
    apply X in X0.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).

    intros.    
    unfold update'.
    intros.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.

  Lemma pp_rw_assign_tot {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ : post}
    (a : assignable Δ τ k) :
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ y x}}ᵗ -> 
    (forall x γ δ, θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} LET k := e {{y : UNIT | ψ y (δ, γ)}}ᵗ.
  Proof.
    intros [w1 p1] h.
    exists (has_type_rw_Assign _ _ _ _ _ a w1).
    pose proof (rw_assign_tot _ _ _ _ _ w1 ϕ θ ψ (  has_type_rw_Assign Γ Δ e τ k a w1) ).
    assert (w1 |- [{(fun δγ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ δγ))}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_4 in h2; auto.
    apply X in X0.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).

    intros.    
    unfold update'.
    intros.
    rewrite (assignable_unique _ _ _  (assign_wty_assignable Γ Δ k e τ w1 (has_type_rw_Assign Γ Δ e τ k a w1)) a).
    apply h; auto.
  Defined.
  
  
  Lemma pp_rw_cond_prt {Γ Δ} {e} {c1 c2} {τ}
    {ϕ} {θ} {ψ} :
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ y x}}ᵖ ->
    [γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} c1 {{y : τ | ψ y (δ, γ)}}ᵖ ->
    [γ : Γ] ; [δ : Δ] ||- {{θ false (δ; γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} Cond e c1 c2 {{y : τ | ψ y (δ, γ)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    assert (w1 |- {{rw_to_ro_pre ϕ}} e {{y | θ y}}).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_4 in h2; auto.
    assert (w2 ||- {{ro_to_rw_pre (θ true)}} c1 {{y | ψ y}}).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
    assert (w3 ||- {{ro_to_rw_pre (θ false)}} c2 {{y | ψ y}}).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
    pose proof (rw_cond_prt _ _ _ _ _ _ _ _ _
                  (  has_type_rw_Cond Γ Δ e c1 c2 τ w1 w2 w3)
                  _ _ _ X X0 X1 ).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
  Defined.
    
  Lemma pp_rw_cond_tot {Γ Δ} {e} {c1 c2} {τ}
    {ϕ} {θ} {ψ} :
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ y x}}ᵗ ->
    [γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} c1 {{y : τ | ψ y (δ, γ)}}ᵗ ->
    [γ : Γ] ; [δ : Δ] ||- {{θ false (δ; γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵗ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} Cond e c1 c2 {{y : τ | ψ y (δ, γ)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3].
    exists (has_type_rw_Cond _ _ _ _ _ _ w1 w2 w3).
    assert (w1 |- [{rw_to_ro_pre ϕ}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_4 in h2; auto.
    assert (w2 ||- [{ro_to_rw_pre (θ true)}] c1 [{y | ψ y}]).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
    assert (w3 ||- [{ro_to_rw_pre (θ false)}] c2 [{y | ψ y}]).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
    pose proof (rw_cond_tot _ _ _ _ _ _ _ _ _
                  (  has_type_rw_Cond Γ Δ e c1 c2 τ w1 w2 w3)
                  _ _ _ X X0 X1 ).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 [h2 h2']; auto); try (intros [h1 h2] h3; auto).
  Defined.
  
  Lemma pp_rw_case_list_prt {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
    (θ : ForallT (fun _ => bool -> sem_ctx (Δ ++ Γ) -> Prop) l)
    {ϕ} {ψ} :
    ForallT1 _ (fun ec (θ : bool -> sem_ctx (Δ ++ Γ) -> Prop)
                =>
                  ([x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ y x}}ᵖ) *
                    ([γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} snd ec {{y : τ | ψ y (δ, γ)}}ᵖ))%type l θ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} CaseList l {{y : τ | ψ y (δ, γ)}}ᵖ.
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
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2; rewrite tedious_equiv_4 in h2; auto.
    destruct p2.
    apply (rw_prt_change_wty (snd p1)) in p2.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros [h1 h1'] h2; auto); try (intros h1 h2 h3; auto).    
  Defined.

  Lemma pp_rw_case_list_tot {Γ Δ} {l} {τ} (h : (1 <= length l)%nat)
    (θ : ForallT (fun _ => bool -> sem_ctx (Δ ++ Γ) -> Prop) l)
    (ϕi : ForallT (fun _ => sem_ctx (Δ ++ Γ) -> Prop) l)
    {ϕ} {ψ} :
    ForallT2 _ _ (fun ec θ ϕi =>
                    ([x  : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ y x}}ᵖ) *
                      ([γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} snd ec {{y : τ | ψ y (δ, γ)}}ᵗ) *
                      ([x : Δ ++ Γ] |- {{ϕi x}} fst ec {{y : BOOL | y = true}}ᵗ)
                 )%type l θ ϕi  ->
    (forall x : sem_ctx (Δ ++ Γ),
        ϕ (fst_app x, snd_app x) ->
        ForallT_disj (fun _ : exp * exp => sem_ctx (Δ ++ Γ) -> Prop)
          (fun (_ : exp * exp) (ϕi0 : sem_ctx (Δ ++ Γ) -> Prop) => ϕi0 x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} CaseList l {{y : τ | ψ y (δ, γ)}}ᵗ.
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
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2; rewrite tedious_equiv_4 in h2; auto.
    apply (rw_tot_change_wty (snd p1)) in p3.

    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros [h1 h1'] h2; auto); try (intros h1 h2 h3; auto).
    
    apply (ro_tot_change_wty (fst p1)) in p2.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply HH.
    unfold rw_to_ro_pre in H0; rewrite tedious_equiv_4 in H0; auto.
  Defined.

    Lemma pp_rw_case_prt {Γ Δ} {e1 e2 c1 c2} {τ}
      {ϕ} {θ1} {θ2} {ψ} :
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 y x}}ᵖ -> 
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 y x}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ1 true (δ ; γ)}} c1 {{y : τ | ψ y (δ, γ)}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ2 true (δ ; γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ y (δ, γ)}}ᵖ.
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
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 y x}}ᵖ -> 
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 y x}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ1 true (δ ; γ)}} c1 {{y : τ | ψ y (δ, γ)}}ᵗ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ2 true (δ ; γ)}} c2 {{y : τ | ψ y (δ, γ)}}ᵗ ->
    [x : Δ ++ Γ] |- {{ϕ1 x}} e1 {{y : BOOL | y = true}}ᵗ -> 
    [x : Δ ++ Γ] |- {{ϕ2 x}} e2 {{y : BOOL | y = true}}ᵗ -> 
    (forall x, (ϕ (fst_app x, snd_app x)) -> (ϕ1 x \/ ϕ2 x)) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ y (δ, γ)}}ᵗ.
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
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ y x}}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} c {{y : UNIT | ϕ (δ, γ) }}ᵖ -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} While e c {{y : UNIT | ϕ (δ, γ) /\ θ false (δ ; γ)}}ᵖ.
  Proof.
    intros [w1 p1] [w2 p2].
    exists (has_type_rw_While _ _ _ _ w1 w2).    
    assert (w1 |- {{rw_to_ro_pre ϕ}} e {{y | θ y}}).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2; rewrite tedious_equiv_4 in h2; auto.
    assert (w2 ||- {{ro_to_rw_pre (θ true)}} c {{_ | ϕ}}).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
    pose proof (rw_while_prt _ _ _ _ _ _ (  has_type_rw_While Γ Δ e c w1 w2)  _ _  X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  Defined.
  
  Lemma pp_rw_while_tot {Γ Δ} {e c}
    {ϕ} {θ} {ψ}:
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ y x}}ᵗ -> 
    [γ : Γ] ; [δ : Δ] ||- {{θ true (δ; γ)}} c {{y : UNIT | ϕ (δ, γ) }}ᵗ -> 
    [γ' : Γ ++ Δ] ; [δ : Δ] ||- {{θ true (δ; fst_app γ') /\ δ = snd_app γ'}} c {{_ : UNIT | ψ (δ, γ')}}ᵗ ->
    (forall δ γ, 
        ϕ (δ, γ) -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ (f (S n), (γ; f n))))) -> 
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} While e c {{y : UNIT | ϕ (δ, γ) /\ θ false (δ ; γ)}}ᵗ.
  Proof.
    intros [w1 p1] [w2 p2] [w3 p3] h.
    exists (has_type_rw_While _ _ _ _ w1 w2).
    assert (w1 |- [{rw_to_ro_pre ϕ}] e [{y | θ y}]).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre in h2; rewrite tedious_equiv_4 in h2; auto.
    assert (w2 ||- [{ro_to_rw_pre (θ true)}] c [{_ | ϕ}]).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
    assert (w3 ||- [{(fun x : sem_ctx Δ * sem_ctx (Γ ++ Δ) => ro_to_rw_pre (θ true) (fst x, fst_app (snd x)) /\ fst x = snd_app (snd x))}] c [{_ | (fun x : sem_ctx Δ * sem_ctx (Γ ++ Δ) => ψ x)}]).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
    pose proof (rw_while_tot _ _ _ _ _ _ _ (has_type_rw_While Γ Δ e c w1 w2) _ _ _ X X0 X1 h).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  Defined.
  
End Commands.



