Require Import L1.syntax scopes List.
Import ListNotations.

(** Well-bound L1 terms as in paper Figure 10. *)

Section WellBoundness.

Context `{G: Graph (@AT T)}.

Inductive wb_exp : exp -> Prop :=
| wb_cnum :
    forall s t z,
      wb_exp (E s t (CNum z))
| wb_plus: forall
    s t s1 t1 e1 s2 t2 e2
    (WB1: wb_exp (E s1 t1 e1))
    (WB2: wb_exp (E s2 t2 e2)),
    s = s2 ->
    s = s1 ->
    wb_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wb_var :
    forall
      s t r p s' d'
      (SR: rlookup r p s' d'),
      wb_exp (E s t (Var r))
| wb_fn :
    forall
      s t d s1 t1 e1
      (WB1: wb_exp (E s1 t1 e1))
      (PS: linksofScopeP s1 [(P, [s])])
      (DS: declsofScopeP s1 [d]),
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

Inductive wb_prog : prog -> Prop :=
| wb_prog_ :
    forall
      s0 s t e
      (WBE: wb_exp (E s t e))
      (DS: declsofScopeP s0 [])
      (LS : linksofScopeP s0 []),
      s = s0 ->
      wb_prog (Prog (E s t e))
.

End WellBoundness.