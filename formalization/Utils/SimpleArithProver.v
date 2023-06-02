From Clerical Require Import Preliminaries.Preliminaries.
From Clerical Require Import Powerdomain.Powerdomain.
From Clerical Require Import Syntax Typing TypingProperties Semantics ReasoningPrettyprinting ReasoningRules ReasoningUtils.
From Clerical.Utils Require Import TypingTactic SimpleArith.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.


Ltac decide_simple_arithmetic e X Xdefi :=
  let v := fresh "tmp" in 
  case_eq (simple_arithmetical_dec
             e
          );
  intros X v; [simpl in v; injection v; intro Xdefi; clear v |simpl in v; discriminate v].

Ltac unfold_stuffs :=
  unfold rw_to_ro_pre;
  unfold ro_to_rw_pre.
  
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
  |  |- asrt_imp2 _ _ =>
       let v1 := fresh "tmp" in
       let v2 := fresh "tmp" in
       let v3 := fresh "tmp" in
       let w1 := fresh "tmp" in
       let w2 := fresh "tmp" in
       let w3 := fresh "tmp" in
       unfold_stuffs;
       intros v1 v2 v3;
       repeat destruct v1;
       repeat destruct v2;
       repeat destruct v3;
       repeat split;
       auto
  end.

       
Ltac proves_simple_arithmetical :=
  match goal with
  | |- proves_ro_prt_pp ?Γ ?e ?τ ?ϕ ?ψ =>
      
      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_simple_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (simple_arithmetical_prt Γ e τ v3 v1) as v4;
      
      apply (pp_ro_prt_pose_readonly ϕ) in v4;

      simpl in v4;
      
      apply (pp_ro_imply_prt v4); clear v4;

      try (auto_imp; fail);
      rewrite <- v2; clear v2;
      easy_rewrite_uip;

      intros y x [val pre];

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

             
             
          

  | |- proves_ro_tot_pp ?Γ ?e ?τ ?ϕ ?ψ =>

      let v1 := fresh "tmp" in
      let v2 := fresh "tmp" in
      let v3 := fresh "tmp" in
      let v4 := fresh "tmp" in
      
      let y := fresh "y" in
      let x := fresh "x" in
      let v := fresh "val" in
      let p := fresh "pre" in

      decide_simple_arithmetic e v1 v2;

      assert (Γ |- e : τ) as v3 by auto_typing;

      pose proof (simple_arithmetical_tot _ v1 _ _  v3) as v4;
      
      apply (pp_ro_tot_pose_readonly (Γ := Γ) ϕ) in v4;

      simpl in v4;
      
      apply (pp_ro_imply_tot v4); clear v4;
      rewrite <- v2; clear v2; easy_rewrite_uip;
      [
        intros x p;
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
        intros y x [v p];

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

  | |- proves_rw_tot_pp ?Γ ?Δ ?e ?τ ?ϕ ?ψ =>
      apply (pp_rw_ro_tot_back (τ := τ));
      proves_simple_arithmetical

  | |- proves_rw_prt_pp ?Γ ?Δ ?e ?τ ?ϕ ?ψ =>
      apply (pp_rw_ro_prt_back (τ := τ));
      proves_simple_arithmetical

  | _ => idtac "bbb"
  end.

