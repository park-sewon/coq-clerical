From Clerical Require Import Preliminaries.Preliminaries.
From Clerical Require Import Powerdomain.Powerdomain.
From Clerical Require Import Syntax Typing TypingProperties Semantics Specification ReasoningRules ReasoningUtils.
From Clerical.Utils Require Import TypingTactic Arith ReducingTactic.
Require Import Coq.Program.Equality.
Require Import ZArith Reals List.

Ltac decide_arithmetic e X Xdefi :=
  let v := fresh "tmp" in 
  case_eq (arith_dec
             e
          );
  intros X v; [simpl in v; injection v; intro Xdefi; clear v |simpl in v; discriminate v].

Ltac unfold_stuffs :=
  reduce_tedious.
  
Ltac auto_imp :=
  match goal with
  |  |- asrt_imp _ _ =>
       let v1 := fresh "tmp" in
       let v2 := fresh "tmp" in
       let v3 := fresh "tmp" in
       let w1 := fresh "tmp" in
       let w2 := fresh "tmp" in
       let w3 := fresh "tmp" in
       unfold_stuffs;
       intros v1 v2;
       repeat destruct v1;
       repeat destruct v2;
       repeat split;
       auto
  end.

Ltac prove_arith :=
  lazymatch goal with
  | |- proves_ro_prt ?Γ ?e ?τ (@mk_ro_prt _ _ _ ?ϕ ?ψ) =>
      
      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (arith_prt Γ e τ v3 v1) as v4;

      apply (ro_prt_pose_readonly (Γ := Γ) (τ := τ) (ψ := patf) ϕ) in v4;

      simpl in v4;
      
      apply (ro_imply_prt' (ψ := patf) (ψ' := patf) v4); clear v4;

      try (auto_imp; fail);
      rewrite <- v2; clear v2;
      easy_rewrite_uip;
      reduce_tedious;
      intros [y x];
      
      reduce_tedious;

      intros [v p];

      repeat (
          try (destruct has_type_ro_OpZplus_inverse);
          try (destruct has_type_ro_OpZminus_inverse);
          try (destruct has_type_ro_OpZmult_inverse);
          try (destruct has_type_ro_OpZlt_inverse);
          try (destruct has_type_ro_OpZeq_inverse);
          try (destruct has_type_ro_OpRplus_inverse);
          try (destruct has_type_ro_OpRminus_inverse);
          try (destruct has_type_ro_OpRmult_inverse);
          try (destruct has_type_ro_OpRlt_inverse);
          try (destruct has_type_ro_OpRrecip_inverse);
          try (destruct has_type_ro_OpZRexp_inverse);
          try (destruct has_type_ro_OpZRcoerce_inverse);
          try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)) in v);
          try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)) in v);
          try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)) in v);
          simpl in v)

             
             
          

  | |- proves_ro_tot ?Γ ?e ?τ (@mk_ro_tot _ _ _ ?ϕ ?ψ) =>

      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (arith_tot _ v1 _ _  v3) as v4;
      
      apply (ro_tot_pose_readonly (Γ := Γ) (τ := τ) (ψ := patf) ϕ) in v4;

      simpl in v4;
      
      apply (ro_imply_tot' (ψ := patf) (ψ' := patf) v4); clear v4;
      rewrite <- v2; clear v2; easy_rewrite_uip;
      [
        intro x;
        reduce_tedious;
        intro p;
        split;
        [
          repeat (
              try (destruct has_type_ro_OpZplus_inverse);
              try (destruct has_type_ro_OpZminus_inverse);
              try (destruct has_type_ro_OpZmult_inverse);
              try (destruct has_type_ro_OpZlt_inverse);
              try (destruct has_type_ro_OpZeq_inverse);
              try (destruct has_type_ro_OpRplus_inverse);
              try (destruct has_type_ro_OpRminus_inverse);
              try (destruct has_type_ro_OpRmult_inverse);
              try (destruct has_type_ro_OpRlt_inverse);
              try (destruct has_type_ro_OpRrecip_inverse);
              try (destruct has_type_ro_OpZRexp_inverse);
              try (destruct has_type_ro_OpZRcoerce_inverse);
              try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)));
              simpl); auto

        |
          auto          
        ]
      |               
        intros [y x];
        reduce_tedious;
        intros [v p];

        repeat (
            try (destruct has_type_ro_OpZplus_inverse);
            try (destruct has_type_ro_OpZminus_inverse);
            try (destruct has_type_ro_OpZmult_inverse);
            try (destruct has_type_ro_OpZlt_inverse);
            try (destruct has_type_ro_OpZeq_inverse);
            try (destruct has_type_ro_OpRplus_inverse);
            try (destruct has_type_ro_OpRminus_inverse);
            try (destruct has_type_ro_OpRmult_inverse);
            try (destruct has_type_ro_OpRlt_inverse);
            try (destruct has_type_ro_OpRrecip_inverse);
            try (destruct has_type_ro_OpZRexp_inverse);
            try (destruct has_type_ro_OpZRcoerce_inverse);
            try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)) in v);
            try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)) in v);
            try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)) in v);
            simpl in v); auto
      ]

  | |- proves_rw_tot ?Γ ?Δ ?e ?τ (@mk_rw_tot _ _ _ _ ?ϕ ?ψ) =>
      apply (rw_ro_tot_back (Γ := Γ) (Δ := Δ) (τ := τ) (ϕ := ϕ) (ψ := ψ));
      prove_arith

  | |- proves_rw_prt ?Γ ?Δ ?e ?τ (@mk_rw_prt _ _ _ ?ϕ ?ψ)=>
      apply (rw_ro_prt_back (τ := τ) (ϕ := patf) (ψ := pattf));
      prove_arith

  | _ => idtac "bbb"
  end.


Lemma rw_assign_arith_tot
  e (p : arith e) Γ Δ k τ
  (we : (Γ +++ Δ) |- e : τ)
  (a : assignable Δ τ k)
  (ϕ : pred) (ψ : pred) :
  (forall x, ϕ (fst_app x, snd_app x) -> arith_cond _ p _ _ we x) ->
  (forall γ δ, ϕ (γ, δ) ->
      ψ (γ, (update k (arith_val _ p _ _ we (γ; δ)) δ a, tt))) ->
  [γ : Γ ;;; δ : Δ]||- {{ϕ (γ, δ)}} (LET k := e) {{y : UNIT | ψ (γ, (δ, y)) }}ᵗ.
Proof.
  intros.
  pose proof (arith_tot e p (Δ ++ Γ) τ we).
  apply (ro_tot_pose_readonly (ψ := patf) (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (rw_assign_tot_util τ
           (θ := fun '(x, y) => y = (arith_val _ p _ _ we x)) a).
  apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X).
  intros x y.
  split; auto.
  intros [h1 h2] [h3 _]; auto.
  intros.
  rewrite H2; apply H0.
  auto.
Defined.


Ltac prove_assign_arith t :=
  match goal with
  | |- proves_rw_tot ?Γ ?Δ (Assign ?k ?e) ?τ (@mk_rw_tot _ _ _ _ ?ϕ ?ψ) =>
      let a := fresh "a" in
      let we := fresh "w" in

      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_arithmetic e v1 v2;

      assert (assignable Δ t k) as a by (repeat constructor; auto);
      
      assert ((Δ ++ Γ) |- e : t) as we by auto_typing;

      apply (rw_assign_arith_tot e v1 Γ Δ k t we a ϕ ψ);
      [
        rewrite <- v2;
        clear v1 v2;
        simpl;
        repeat (
            try (destruct has_type_ro_OpZplus_inverse);
            try (destruct has_type_ro_OpZminus_inverse);
            try (destruct has_type_ro_OpZmult_inverse);
            try (destruct has_type_ro_OpZlt_inverse);
            try (destruct has_type_ro_OpZeq_inverse);
            try (destruct has_type_ro_OpRplus_inverse);
            try (destruct has_type_ro_OpRminus_inverse);
            try (destruct has_type_ro_OpRmult_inverse);
            try (destruct has_type_ro_OpRlt_inverse);
            try (destruct has_type_ro_OpRrecip_inverse);
            try (destruct has_type_ro_OpZRexp_inverse);
            try (destruct has_type_ro_OpZRcoerce_inverse);
            try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)));
            try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)));
            try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)));
            simpl); auto
        |

          rewrite <- v2;
          clear v1 v2;
          simpl;
          repeat (
              try (destruct has_type_ro_OpZplus_inverse);
              try (destruct has_type_ro_OpZminus_inverse);
              try (destruct has_type_ro_OpZmult_inverse);
              try (destruct has_type_ro_OpZlt_inverse);
              try (destruct has_type_ro_OpZeq_inverse);
              try (destruct has_type_ro_OpRplus_inverse);
              try (destruct has_type_ro_OpRminus_inverse);
              try (destruct has_type_ro_OpRmult_inverse);
              try (destruct has_type_ro_OpRlt_inverse);
              try (destruct has_type_ro_OpRrecip_inverse);
              try (destruct has_type_ro_OpZRexp_inverse);
              try (destruct has_type_ro_OpZRcoerce_inverse);
              try (rewrite <- (prop_irrl _ (eq_refl REAL) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl INTEGER) (eq_sym _)));
              try (rewrite <- (prop_irrl _ (eq_refl BOOL) (eq_sym _)));
              simpl); auto;
          reduce_var_access;
          reduce_update;
          simpl
      ]
      
  end.

