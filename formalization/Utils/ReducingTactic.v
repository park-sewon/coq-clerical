From Clerical.Preliminaries Require Import Preliminaries.
From Clerical Require Import Syntax Typing TypingProperties Semantics SemanticsProperties.


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
  


Ltac reduce_update_tactic h :=
  match type of h with
  | ltac_No_arg =>
      repeat (simpl; try rewrite reduce_update_S; try rewrite reduce_update_0)
  | _ =>
      repeat (simpl in h; try rewrite reduce_update_S in h; try rewrite reduce_update_0 in h)
  end.

Tactic Notation "reduce_update" constr(x1) :=
  reduce_update_tactic x1 .
                    
Tactic Notation "reduce_update" :=
  reduce_update_tactic ltac_no_arg.

