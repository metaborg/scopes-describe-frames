Require Export ZArith scopes.

(** * L3 Syntax *)

(** Corresponds to paper Fig. 23 (with some extensions). *)


(** Types *)
Inductive T :=
| Tint : T
| Tbool: T
| Tarrow : list T -> T -> T
| Tclass : D -> T
| TclassDef : D -> T
.

Inductive pre_exp :=
| CNum: Z -> pre_exp
| CTrue : pre_exp
| CFalse : pre_exp
| Plus : exp -> exp -> pre_exp
| Gt : exp -> exp -> pre_exp
| Lhs : lhs -> pre_exp
| Fn : list D -> exp -> pre_exp
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
| Var : R -> lhs
| Field : exp -> R -> lhs

with binder :=
| Binder : D -> exp -> binder

(** Initializer expressions are references, referring to the
declaration to be initialized with the value given by evaluating
[exp]. *)
with initializer :=
| Initializer : R -> exp -> initializer

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

(* Initializer projections *)
Definition initRef (i : initializer) :=
  match i with
  | Initializer r _ => r
  end.
Definition initExp (i : initializer) :=
  match i with
  | Initializer _ e => e
  end.

(** Class type fields are compactly represented as an optional
[D]eclaration, [T]ype pair, and an [initializer].

Fields that have some [(D * T)] pair represent field _declarations_,
whereas fields that do not have such a pair represent an initializer
for fields in a parent class. *)
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

(** Class definitions: a [D]eclaration that uniquely identifies the
class, an optional [R]eference to a parent class, and a list of class
type field declarations *)
Inductive decl :=
| Cdef : ScopeId -> D -> option R -> list fld_decl -> decl.

(** A program consists of a list of class type declarations and an
expression to be evaluated *)
Inductive prog :=
| Prog : list decl -> exp -> prog. (* top-level body *)


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

(** Some helpers for working with binders and initializers *)
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

(** Unzipping sequences of binders, initializers, and field
declarations. *)
Definition unzipb := @unzip binder D exp split_b.
Definition unzipi := @unzip initializer R exp split_i.
Definition unzipf := @unzip fld_decl R exp split_f.
