Require Export ZArith scopes.

(* AST *)

(* For now, syntactic and semantic types are represented using the same definition. *)
Inductive T :=
| Tint : T
| Tbool: T
| Tarrow : list T -> T -> T
| Tclass : ScopeId -> D -> T
| TclassDef : ScopeId -> D -> T
.

Inductive pre_exp :=
| CNum: Z -> pre_exp
| CTrue : pre_exp
| CFalse : pre_exp
| Plus : exp -> exp -> pre_exp
| Gt : exp -> exp -> pre_exp
| Lhs : lhs -> pre_exp
| Fn : list D -> exp -> pre_exp (* functions of one variable *)
| App : exp -> list exp -> pre_exp
| LetPar : list binder -> exp -> pre_exp
| LetSeq : list binder -> exp -> pre_exp
| LetRec : list binder -> exp -> pre_exp
| Asgn : lhs -> exp -> pre_exp
| If : exp -> exp -> exp -> pre_exp
| Seq : exp -> exp -> pre_exp
| New : R -> pre_exp
| With : exp -> exp -> pre_exp
with lhs :=
| Var : R -> lhs (* would be nice to change R --> exp *)
| Field : exp -> R -> lhs
with binder :=
| Binder : D -> exp -> binder
with initializer :=
| Initializer : R -> exp -> initializer
with exp :=
| E : ScopeId -> T -> pre_exp -> exp.

(* Exp projections *)
Definition expScope (e : exp) : ScopeId :=
  match e with
    | E s _ _ => s
  end.
Definition expType (e : exp) : T :=
  match e with
    | E _ t _ => t
  end.

(* Initializer projections *)
Definition initRef (i : initializer) :=
  match i with
  | Initializer r _ => r
  end.
Definition initExp (i : initializer) :=
  match i with
  | Initializer _ e => e
  end.

(* Fields *)
Inductive fld_decl :=
| FldDecl : option (D * T) -> initializer -> fld_decl.
Definition fldDT (f: fld_decl) :=
  match f with
  | FldDecl optdt _ => optdt
  end.
Definition fldI (f: fld_decl) :=
  match f with
  | FldDecl _ i => i
  end.

(* Classes *)
Inductive decl :=
| Cdef : ScopeId -> D -> option (ScopeId * R) -> list fld_decl -> decl.

Inductive prog :=
| Prog : list decl -> exp -> prog. (* top-level body *)

(* Distinguishing value expressions: *)
Definition is_val e :=
  match e with
  | E _ _ e' =>
    match e' with
    | CNum _ => True
    | CTrue => True
    | CFalse => True
    | Fn _ _ => True
    | _ => False
    end
  end.

(* Helpers for working with binders and initializers *)
Definition split_b (b: binder) :=
  match b with
  | Binder d e => (d, e)
  end.
Definition split_i (i: initializer) :=
  match i with
  | Initializer r e => (r, e)
  end.
Definition split_f (f: fld_decl) :=
  match f with
  | FldDecl _ i => split_i i
  end.

Fixpoint unzip {C T1 T2} {split: C -> (T1 * T2)} (l: list C) : (list T1 * list T2) :=
  match l with
  | c :: cs =>
    let (t1,t2) := split c in
    let  t1t2s := @unzip C T1 T2 split cs in
    (t1 :: (fst t1t2s), t2 :: (snd t1t2s))
  | [] => ([], [])
  end.

Definition unzipb := @unzip binder D exp split_b.
Definition unzipi := @unzip initializer R exp split_i.
Definition unzipf := @unzip fld_decl R exp split_f.

(* Splitting binders to record the expression scope of the binder: *)
Definition split_bs (b: binder) : ((ScopeId * D) * exp) :=
  match b with
  | Binder d e => ((expScope e, d), e)
  end.

(* Splitting binders to record the expression scope of the binder: *)
Definition split_is (b: initializer) : ((ScopeId * R) * exp) :=
  match b with
  | Initializer r e => ((expScope e, r), e)
  end.
Definition split_fs (f: fld_decl) :=
  match f with
  | FldDecl _ i => split_is i
  end.

Definition unzipbs := @unzip binder (ScopeId * D) exp split_bs.
Definition unzipfs := @unzip fld_decl (ScopeId * R) exp split_fs.
