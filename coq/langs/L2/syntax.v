Require Export ZArith scopes.

(** * L2 Syntax *)

(** Corresponds to paper Fig. 16 (with some extensions). *)

(** Types *)
Inductive T :=
| Tint : T
| Tbool: T
(** n-ary function type, where n is given by the length of [list T] *)
| Tarrow : list T -> T -> T
| Trecord : D -> T
.

Inductive pre_exp :=
| CNum: Z -> pre_exp
| CTrue : pre_exp
| CFalse : pre_exp
| Plus : exp -> exp -> pre_exp
| Gt : exp -> exp -> pre_exp

(** For dereferencing a variable ([lhs]) *)
| Lhs : lhs -> pre_exp

(** n-ary functions *)
| Fn : list D -> exp -> pre_exp

(** n-ary application *)
| App : exp -> list exp -> pre_exp

(** parallel let (bodies of binders can't refer to each other) *)
| LetPar : list binder -> exp -> pre_exp

(** sequential let (bodies of binders can refer to previous
bindings) *)
| LetSeq : list binder -> exp -> pre_exp

(** recursive let (bodies of binders can refer to all other bindings,
including the one being currently bound) *)
| LetRec : list binder -> exp -> pre_exp

(** Assign a value to a variable ([lhs]) *)
| Asgn : lhs -> exp -> pre_exp
| If : exp -> exp -> exp -> pre_exp
| Seq : exp -> exp -> pre_exp

(** For creating a record value whose structure is described by the
declaration that [R] refers to *)
| New : R -> pre_exp

with lhs :=
| Var : R -> lhs
| Field : exp -> R -> lhs

with binder :=
| Binder : D -> exp -> binder

with exp :=
| E : ScopeId -> T -> pre_exp -> exp.


Definition expScope (e : exp) : ScopeId :=
  match e with
  | E s _ _ => s
  end.

Definition expType (e : exp) : T :=
  match e with
  | E _ t _ => t
  end.

(** Record type field declarations consist of a [D]eclaration, [T]ype
pair *)
Inductive fld_decl :=
| Flddecl : D -> T -> fld_decl.

Definition fldDecl (f: fld_decl) :=
  match f with
  | Flddecl d _ => d
  end.

Definition fldType (f: fld_decl) :=
  match f with
  | Flddecl _ t => t
  end.

(** Record definitions: a [D]eclaration that uniquely identifies the
record, and a list of record type field declarations *)
Inductive decl :=
| Rdef : D -> list fld_decl -> decl.

(** A program consists of a list of record type declarations and an
expression to be evaluated *)
Inductive prog :=
| Prog : list decl -> exp -> prog.

(** * Auxiliary definitions *)

(** Distinguishing value expressions. Used for type-checking
[LetRec]s, to avoid black hole semantics of self-referential
let-bindings. *)
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

(** Some helpers for working with binders. *)
Definition split_b (b: binder) :=
  match b with
  | Binder d e => (d, e)
  end.

Fixpoint unzip {C T1 T2} {split: C -> (T1 * T2)} (l: list C) : (list T1 * list T2) :=
  match l with
  | c :: cs =>
    let (t1,t2) := split c in
    let  t1t2s := @unzip C T1 T2 split cs in
    (t1 :: (fst t1t2s), t2 :: (snd t1t2s))
  | [] => ([], [])
  end.

(** Unzips a sequence of binders into a list of declarations and a
list of expressions *)
Definition unzipb := @unzip binder D exp split_b.
