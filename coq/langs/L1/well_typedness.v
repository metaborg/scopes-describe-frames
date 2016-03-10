Require Import scopes L1.syntax.

(** Well-typed L1 terms as in paper Figure. 11. *)

Section WellTypedness.

Context `{G: Graph (@AT T)}.

Inductive wt_exp : exp -> Prop :=
| wt_cnum :
    forall s t z,
      t = Tint ->
      wt_exp (E s t (CNum z))
| wt_plus:
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t = Tint ->
      t1 = Tint ->
      t2 = Tint ->
      wt_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wt_var :
    forall
      s t r p s' d'
      (SR: scopeofRefP r s)
      (DR: rlookup r p s' d')
      (TD: typofDecl d' t),
      wt_exp (E s t (Var r))
| wt_fn :
    forall
      s t d s1 t1 e1 td
      (TD: typofDecl d td)
      (WTE: wt_exp (E s1 t1 e1)),
      t = Tarrow td t1 ->
      wt_exp (E s t (Fn d (E s1 t1 e1)))
| wt_app:
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t1 = Tarrow t2 t ->
      wt_exp (E s t (App (E s1 t1 e1) (E s2 t2 e2)))
.

Inductive wt_prog : prog -> Prop :=
| wt_prog_ :
    forall
      s t e
      (WTE: wt_exp (E s t e)),
      wt_prog (Prog (E s t e))
.

End WellTypedness.