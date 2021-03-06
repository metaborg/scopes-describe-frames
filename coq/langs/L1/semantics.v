Require Import ZArith frames L1.syntax.

(** Semantics of L1 evaluation from paper Fig. 13 and Appendix A. *)

(** L1 can only abruptly terminate by getting stuck ("going
[Wrong]"). *)

Inductive Error :=
| Wrong : Error
.

(** Values *)
Inductive V :=
(** Number *)
| NumV : Z -> V
(** Closure recording its formal parameter [D]eclaration, function
body [exp]ression, and the lexical parent [FrameId] *)
| ClosV : D -> exp -> FrameId -> V
(** Aborted computation due to [Error] *)
| AbortV : Error -> V
.

(** [abort] either propagates the current reason for aborting, or it
aborts by "going wrong". *)

Definition abort (v: V) :=
  match v with
  | AbortV e => AbortV e
  | _ => AbortV Wrong
  end.

(** A value is [good] if it is not an [AbortV]. *)
Definition good (v: V) :=
  match v with
  | AbortV _ => False
  | _ => True
  end.

(** Unifies the type parameters for the definition of [FrameHeap]
types *)

Instance FH : @FrameHeap V := {}.

(** * Dynamic Semantics *)

Section DynamicSemantics.

Context `{G: Graph (@AT T)}.

(** Evaluation depends mainly on pre-terms and, occasionally, on scope
    annotations; it ignores type annotations. *)
Inductive eval_exp : H -> FrameId -> exp -> V -> H -> Prop :=
| eval_cnum_ :
    forall frm z h s t,
      eval_exp h frm (E s t (CNum z)) (NumV z) h
| eval_plus_ :
    forall
      frm e1 e2 z1 z2 h0 h1 h2 s t
      (EVALL: eval_exp h0 frm e1 (NumV z1) h1)
      (EVALR: eval_exp h1 frm e2 (NumV z2) h2),
      eval_exp h0 frm (E s t (Plus e1 e2)) (NumV (z1+z2)%Z) h2
| eval_plus_b1 :
    forall
      frm e1 e2 h0 v1 h1 s t
      (EVALL: eval_exp h0 frm e1 v1 h1)
      (ABORTL: forall z1, v1 <> NumV z1),
      eval_exp h0 frm (E s t (Plus e1 e2)) (abort v1) h1
| eval_plus_b2 :
    forall
      frm e1 e2 h0 z1 v2 h1 h2 s t
      (EVALL: eval_exp h0 frm e1 (NumV z1) h1)
      (EVALR: eval_exp h1 frm e2 v2 h2)
      (ABORTR: forall z2, v2 <> NumV z2),
      eval_exp h0 frm (E s t (Plus e1 e2)) (abort v2) h2
| eval_var_ :
    forall
      frm s t r h0 ff d v
      (ADDR: getAddr h0 frm r (Addr_ ff d))
      (GET: getSlot h0 ff d v),
      eval_exp h0 frm (E s t (Var r)) v h0
| eval_var_b1 :
    forall
      frm r h0 s t
      (ADDR: forall ff d, ~ getAddr h0 frm r (Addr_ ff d)),
      eval_exp h0 frm (E s t (Var r)) (AbortV Wrong) h0
| eval_var_b2 :
    forall
      frm r h0 s t ff d
      (ADDR: getAddr h0 frm r (Addr_ ff d))
      (NGET: forall v, ~ getSlot h0 ff d v),
      eval_exp h0 frm (E s t (Var r)) (AbortV Wrong) h0
| eval_fn_ :
    forall
      frm h s t t0 d e,
      eval_exp h frm (E s t (Fn d t0 e)) (ClosV d e frm) h
| eval_app :
    forall
      frm h0 h1 h2 h3 h4 e1 e2 v2 s t vb ff f e d sp
      (EVAL1: eval_exp h0 frm e1 (ClosV d e ff) h1)
      (EVAL2: eval_exp h1 frm e2 v2 h2)
      (SF: scopeofFrame h2 ff sp)
      (NF: initFrame h2 (expScope e) [(P, [(sp, ff)])] [(d,v2)] f h3)
      (EVALBODY: eval_exp h3 f e vb h4),
      eval_exp h0 frm (E s t (App e1 e2)) vb h4
| eval_app_b1 :
    forall
      h0 frm v1 h1 s t e1 e2s
      (EVAL1: eval_exp h0 frm e1 v1 h1)
      (ABORT1: match v1 with
               | ClosV _ _ _ => False
               | _ => True
               end),
      eval_exp h0 frm (E s t (App e1 e2s)) (abort v1) h1
| eval_app_b2 :
    forall
      h0 frm e1 h1 e2 h2 s t d e ff q
      (EVAL1: eval_exp h0 frm e1 (ClosV d e ff) h1)
      (EVAL2: eval_exp h1 frm e2 (AbortV q) h2),
      eval_exp h0 frm (E s t (App e1 e2)) (AbortV q) h2
.

Inductive eval_prog : prog -> V -> Prop :=
| eval_prog_ :
    forall
      e v f h0 h1
      (TOPFRM: initFrame emptyHeap (expScope e) [] [] f h0)  (* The empty root frame *)
      (EVALB: eval_exp h0 f e v h1),
      eval_prog (Prog e) v
.

End DynamicSemantics.