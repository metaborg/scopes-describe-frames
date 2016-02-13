Require Import ZArith scopes.

Inductive T :=
| Tint : T
| Tbool: T
| Tarrow : T -> T -> T
.

Inductive pre_exp :=
| CNum: Z -> pre_exp
| CTrue : pre_exp
| CFalse : pre_exp
| Plus : exp -> exp -> pre_exp
| Gt : exp -> exp -> pre_exp
| Fn : D -> exp -> pre_exp
| App : exp -> exp -> pre_exp
| Var : R -> pre_exp
| Call : R -> exp -> pre_exp   (* call function of one variable *)
| Let : D -> exp -> exp -> pre_exp
| Asgn : R -> exp -> pre_exp
| If : exp -> exp -> exp -> pre_exp
| Seq : exp -> exp -> pre_exp
with exp :=
| E : ScopeId -> T -> pre_exp -> exp
.

Inductive prog :=
| Prog : exp -> prog. (* top-level body *)

Definition expScope (e : exp) : ScopeId :=
  match e with
    | E s _ _ => s
  end.

Definition expType (e : exp) : T :=
  match e with
    | E _ t _ => t
  end.
