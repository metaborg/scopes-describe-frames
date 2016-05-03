Require Import ZArith scopes.

Inductive T :=
| Tint : T
| Tarrow : T -> T -> T
.

(** [pre_exp] corresponds to unannotated terms (Fig. 8 of paper);
    [exp] corresponds to annotated terms (Fig. 9 of paper). *)
Inductive pre_exp :=
| CNum: Z -> pre_exp
| Plus : exp -> exp -> pre_exp
| Fn : D -> T -> exp -> pre_exp
| App : exp -> exp -> pre_exp
| Var : R -> pre_exp
with exp :=
| E : ScopeId -> T -> pre_exp -> exp
.

Inductive prog :=
| Prog : exp -> prog.

Definition expScope (e : exp) : ScopeId :=
  match e with
  | E s _ _ => s
  end.

Definition expType (e : exp) : T :=
  match e with
  | E _ t _ => t
  end.
