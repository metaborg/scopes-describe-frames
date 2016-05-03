Require Import L3.syntax scopes prop_fold.

Section WellTypedness.

Context `{G: Graph (@AT T)}.

(** Subtyping, as defined in Fig. 23. *)

Inductive sub1 : T -> T -> Prop :=
| sub_rec : forall
    d d' s s' ims
    (ASC: assocScope d s)
    (ASC: assocScope d' s')
    (IMS: linksofScopeP s [(I, ims)])
    (IN_IMS: In s' ims),
    sub1 (Tclass d) (Tclass d')
| sub_fun : forall
    t1s t1s' t2 t2'
    (ARGS: Forall2 (fun t1 t1' =>
                      sub' t1' t1) t1s t1s')
    (RET: sub' t2 t2'),
    sub1 (Tarrow t1s t2) (Tarrow t1s' t2')
with sub' : T -> T -> Prop :=
| sub'_refl : forall t,
    sub' t t
| sub'_trans : forall
    t0 t1 t2
    (SUB1: sub1 t0 t1)
    (SUB2: sub' t1 t2),
    sub' t0 t2
.

(** Well-typed L3 expressions, declarations and programs, as in
paper Fig. 24 and 18. *)

Inductive wt_exp : exp -> Prop :=
| wt_cnum :
    forall
      s t z,
      t = Tint ->
      wt_exp (E s t (CNum z))
| wt_ctrue :
    forall
      s t,
      t = Tbool->
      wt_exp (E s t CTrue)
| wt_cfalse :
    forall
      s t,
      t = Tbool->
      wt_exp (E s t CFalse)
| wt_plus:
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t = Tint ->
      t1 = Tint ->
      t2 = Tint ->
      wt_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wt_gt:
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT2: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t = Tbool ->
      t1 = Tint ->
      t2 = Tint ->
      wt_exp (E s t (Gt (E s1 t1 e1) (E s2 t2 e2)))
| wt_lhs_ :
    forall
      s t lhs
      (WT: wt_lhs t lhs),
      wt_exp (E s t (Lhs lhs))
| wt_fn :
    forall
      s t ds s1 t1 e1 tds
      (TD: typofDecls ds tds)
      (WTE: wt_exp (E s1 t1 e1)),
      t = Tarrow tds t1 ->
      wt_exp (E s t (Fn ds (E s1 t1 e1)))
| wt_app :
    forall
      s t s1 e1 t2s e2s
      (WT1: wt_exp (E s1 (Tarrow t2s t) e1))
      (WT2: Forall2 (fun e t2 =>
                       sub' (expType e) t2 /\
                       wt_exp e) e2s t2s),
      wt_exp (E s t (App (E s1 (Tarrow t2s t) e1) e2s))
| wt_letpar :
    forall
      s t1s bs ds e1s s2 t2 e2 t2'
      (UNZIP: unzipb bs = (ds, e1s))
      (TD: typofDecls ds t1s)
      (WT1: Forall2 (fun e t1 =>
                       sub' (expType e) t1 /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2' e2))
      (SUB: sub' t2' t2),
      wt_exp (E s t2 (LetPar bs (E s2 t2' e2)))
| wt_letseq :
    forall
      s t1s bs ds e1s s2 t2 e2 t2'
      (UNZIP: unzipb bs = (ds, e1s))
      (TD: typofDecls ds t1s)
      (WT1: Forall2 (fun e t1 =>
                       sub' (expType e) t1 /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2' e2))
      (SUB: sub' t2' t2),
      wt_exp (E s t2 (LetSeq bs (E s2 t2' e2)))
| wt_letrec :
    forall
      s t1s bs ds e1s s2 t2 e2 t2'
      (UNZIP: unzipb bs = (ds, e1s))
      (TD: typofDecls ds t1s)
      (WT1: Forall2 (fun e t1 =>
                       (* We check that the RHS is a value *)
                       is_val e /\
                       match t1 with
                       | Tarrow _ _ => sub' (expType e) t1
                       | _ => False
                       end /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2' e2))
      (SUB: sub' t2' t2),
      wt_exp (E s t2 (LetRec bs (E s2 t2' e2)))
| wt_asgn :
    forall
      s t s1 t1 e1 lhs
      (LHS: wt_lhs t lhs)
      (WT1: wt_exp (E s1 t1 e1))
      (SUB: sub' t1 t),
      wt_exp (E s t (Asgn lhs (E s1 t1 e1)))
| wt_if :
    forall
      s t s1 t1 e1 s2 t2 e2 s3 t3 e3
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2))
      (WT3: wt_exp (E s3 t3 e3)),
      t1 = Tbool ->
      t2 = t3 ->
      t = t2 ->
      wt_exp (E s t (If (E s1 t1 e1) (E s2 t2 e2) (E s3 t3 e3)))
| wt_seq :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t = t2 ->
      wt_exp (E s t (Seq (E s1 t1 e1) (E s2 t2 e2)))
| wt_new :
    forall
      s t r p sd drec
      (RL: rlookup r p sd drec)
      (TD: typofDecl drec (TclassDef drec)),
      t = Tclass drec ->
      wt_exp (E s (Tclass drec) (New r))

with wt_lhs : T -> lhs -> Prop :=
| wt_lhs_var :
    forall t r s p sd d'
      (SCR: scopeofRefP r s)
      (SR: rlookup r p sd d')
      (TD: typofDecl d' t),
      wt_lhs t (Var r)
| wt_lhs_field :
    forall
      t r e sd s' p d' sc'
      (WT: wt_exp e)
      (SUB: sub' (expType e) (Tclass sd))
      (ASC: assocScope sd sc')
      (SCR: scopeofRefP r s')
      (SR: rlookup r p sc' d')
      (LS: linksofScopeP s' [(I,[sc'])])
      (TD: typofDecl d' t),
      wt_lhs t (Field e r)
.

Inductive wt_decls : list decl -> Prop :=
| wt_decls_rec : forall
    s fds rs es optr d ds s' ds' ts
    (SD: assocScope d s')
    (DS: declsofScopeP s' ds')
    (TS: typofDecls ds' ts)
    (SDS: forall fd, In fd fds ->
                     match fldDT fd with
                     | Some (d, t') =>
                       typofDecl d t'
                     | None => True
                     end)
    (EQ: (rs, es) = unzipf fds)
    (WTE: Forall2 (fun e r =>
                     exists sr p s'' d' t',
                       scopeofRefP r sr /\
                       rlookup r p s'' d' /\
                       typofDecl d' t' /\ sub' (expType e) t' /\ wt_exp e) es rs)
    (WTS: wt_decls ds)
    (TD: typofDecl d (TclassDef d))
    (PARENT: match optr with
             | Some r =>
               exists p s'' dpar,
               rlookup r p s'' dpar /\
               typofDecl dpar (TclassDef dpar)
             | None => True
             end),
    wt_decls ((Cdef s d optr fds) :: ds)
| wt_decl_nil :
    wt_decls nil.

Inductive wt_prog : prog -> Prop :=
| wt_prog_ : forall
    s t e rds ds ts
    (DS: declsofScopeP s ds)
    (TDS: typofDecls ds ts)
    (WTD: wt_decls rds)
    (WTE: wt_exp (E s t e)),
    wt_prog (Prog rds (E s t e))
.

End WellTypedness.
