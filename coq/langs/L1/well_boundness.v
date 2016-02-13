Require Import L1.syntax scopes List.
Import ListNotations.

Inductive wb_exp {G: @WCGAT T}: exp -> Prop :=
| wb_cnum :
    forall s t z,
      wb_exp (E s t (CNum z))
| wb_plus: forall
    s t s1 t1 e1 s2 t2 e2
    (WB1: wb_exp (E s1 t1 e1))
    (WB2:wb_exp (E s2 t2 e2)),
    s = s2 ->
    s = s1 ->
    wb_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wb_var :
    forall
      s t r p s' d'
      (SR: rlookup wc s r p s' d')
      (DYN: dynamicDecl s' d'),
      wb_exp (E s t (Var r))
| wb_fn :
    forall
      s t d s1 t1 e1
      (WB1: wb_exp (E s1 t1 e1))
      (PS: linksofScopeP wc s1 [(P, [s])])
      (DS: declsofScopeP wc s1 [d])
      (DYN: dynamicDecl s d),
      wb_exp (E s t (Fn d (E s1 t1 e1)))
| wb_app :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WB1: wb_exp (E s1 t1 e1))
      (WB2: wb_exp (E s2 t2 e2)),
      s = s1 ->
      s = s2 ->
      wb_exp (E s t (App (E s1 t1 e1) (E s2 t2 e2)))
.

Inductive wb_prog {G: @WCGAT T} : prog -> Prop :=
| wb_prog_ :
    forall
      s0 s t e
      (WBE: wb_exp (E s t e))
      (DS: declsofScopeP wc s0 [])
      (PS : parentofScope wc s0 None),
      s = s0 ->
      wb_prog (Prog (E s t e))
.
