From Clerical Require Import Typing TypingProperties. 

Ltac r_auto_typing_step :=
  try apply r_has_type_ro_Var_S;
  try apply r_has_type_ro_Var_0
  ;  try apply  r_has_type_ro_True
  ;  try apply  r_has_type_ro_False
  ;  try apply r_has_type_ro_Int
  ;  try apply r_has_type_ro_OpZplus
  ;  try apply r_has_type_ro_OpZminus
  ;  try apply r_has_type_ro_OpZmult
  ;  try apply r_has_type_ro_OpZlt
  ;  try apply r_has_type_ro_OpZeq
  ;  try apply r_has_type_ro_OpRplus
  ;  try apply r_has_type_ro_OpRminus
  ;  try apply r_has_type_ro_OpRlt
  ;  try apply r_has_type_ro_OpRmult
  ;  try apply r_has_type_ro_OpRrecip
  ;  try apply r_has_type_ro_OpZRcoerce
  ;  try apply r_has_type_ro_OpZRexp
  ;  try apply r_has_type_ro_Skip
  ;  try apply r_has_type_ro_rw_Seq
  ;  try apply r_has_type_ro_rw_Cond
  ;  try apply  r_has_type_ro_rw_Case 
  ;  try apply r_has_type_ro_rw_CaseList
  ;  try apply r_has_type_ro_rw_While
  ;  try apply r_has_type_ro_rw_Newvar
  ;  try apply r_has_type_ro_rw_Assign
  ;  try apply r_has_type_ro_Lim
  ;  try apply r_has_type_rw_ro_Var
  ;  try apply r_has_type_rw_ro_Boolean
  ;  try apply r_has_type_rw_ro_Integer
  ;  try apply r_has_type_rw_ro_BinOp
  ;  try apply r_has_type_rw_ro_UniOp
  ;  try apply r_has_type_rw_ro_Skip
  ;  try apply r_has_type_rw_Seq
  ;  try apply r_has_type_rw_Cond
  ;  try apply  r_has_type_rw_Case 
  ;  try apply r_has_type_rw_CaseList
  ;  try apply r_has_type_rw_While
  ;  try apply r_has_type_rw_Newvar
  ;  try apply r_has_type_rw_Assign
  ;  try apply r_has_type_rw_ro_Lim

  ; try  apply r_has_type_ro_Var_S
  ; try  apply r_has_type_ro_Var_0
  ; try  apply r_has_type_ro_True
  ; try  apply r_has_type_ro_False
  ; try  apply r_has_type_ro_Int
  ; try  apply r_has_type_ro_OpZplus
  ; try  apply r_has_type_ro_OpZminus
  ; try  apply r_has_type_ro_OpZmult
  ; try  apply r_has_type_ro_OpZlt
  ; try  apply r_has_type_ro_OpZeq
  ; try  apply r_has_type_ro_OpRplus
  ; try  apply r_has_type_ro_OpRminus
  ; try  apply r_has_type_ro_OpRlt
  ; try  apply r_has_type_ro_OpRmult
         
  ; try  apply r_has_type_ro_OpRrecip
  ; try  apply r_has_type_ro_OpZRcoerce
  ; try  apply r_has_type_ro_OpZRexp
         
  ; try  apply r_has_type_ro_Skip
  ; try  apply r_has_type_ro_rw_Seq
  ; try  apply r_has_type_ro_rw_Cond
  ; try  apply r_has_type_ro_rw_Case 
  ; try  apply r_has_type_ro_rw_CaseList
  ; try  apply r_has_type_ro_rw_While
  ; try  apply r_has_type_ro_rw_Newvar
  ; try  apply r_has_type_ro_rw_Assign
  ; try  apply r_has_type_ro_Lim
  ; try  apply r_has_type_rw_ro_Var
  ; try  apply r_has_type_rw_ro_Boolean
  ; try  apply r_has_type_rw_ro_Integer
  ; try  apply r_has_type_rw_ro_BinOp
  ; try  apply r_has_type_rw_ro_UniOp
  ; try  apply r_has_type_rw_ro_Skip
  ; try  apply r_has_type_rw_Seq
  ; try  apply r_has_type_rw_Cond
  ; try  apply r_has_type_rw_Case 
  ; try  apply r_has_type_rw_CaseList
  ; try  apply r_has_type_rw_While
  ; try  apply r_has_type_rw_Newvar
  ; try  apply r_has_type_rw_Assign
  ; try  apply r_has_type_rw_ro_Lim.


Ltac auto_typing  :=
  try (apply r_has_type_ro_has_type_ro);
  try (apply r_has_type_rw_has_type_rw);
  repeat r_auto_typing_step;
  try (apply has_type_ro_r_has_type_ro);
  try (apply has_type_rw_r_has_type_rw);
  auto.

