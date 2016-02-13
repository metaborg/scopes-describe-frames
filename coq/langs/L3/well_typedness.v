Require Import L3.syntax scopes prop_fold.

Inductive sub1 {G: @WCGAT T} : T -> T -> Prop :=
| sub_rec : forall
    s0 d d' s s' ims
    (ASC: assocScope T G s0 d s)
    (ASC: assocScope T G s0 d' s')
    (IMS: linksofScopeP wc s [(I, ims)])
    (IN_IMS: In s' ims),
    sub1 (Tclass s0 d) (Tclass s0 d')
| sub_fun : forall
    t1s t1s' t2 t2'
    (ARGS: Forall2 (fun t1 t1' =>
                      sub' t1' t1) t1s t1s')
    (RET: sub' t2 t2'),
    sub1 (Tarrow t1s t2) (Tarrow t1s' t2')
with sub' {G: @WCGAT T} : T -> T -> Prop :=
| sub'_refl : forall t,
    sub' t t
| sub'_trans : forall
    t0 t1 t2
    (SUB1: sub1 t0 t1)
    (SUB2: sub' t1 t2),
    sub' t0 t2.

(* Capture the constraints on well-typed expressions. *)
Inductive wt_exp {G: @WCGAT T} : exp -> Prop :=
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
      (TD: typofDecls T G s1 ds tds)
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
      (TD: typofDecls T G s2 ds t1s)
      (WT1: Forall2 (fun e t1 =>
                       sub' (expType e) t1 /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2' e2))
      (SUB: sub' t2' t2),
      wt_exp (E s t2 (LetPar bs (E s2 t2' e2)))
| wt_letseq :
    forall
      s t1s bs dss e1s s2 t2 e2 t2'
      (UNZIP: unzipbs bs = (dss, e1s))
      (TD: typofSDecls T G dss t1s)
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
      (TD: typofDecls T G s2 ds t1s)
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
      s t r p sd drec srec
      (SCR: scopeofRefP wc r s)
      (RL: rlookup wc s r p sd drec)
      (ASC: assocScope T G sd drec srec)
      (* (DD: dynamicDecl scd d) *)
      (TD: typofDecl T G sd drec (TclassDef sd drec)),
      t = Tclass sd drec ->
      wt_exp (E s (Tclass sd drec) (New r))

with wt_lhs {G: @WCGAT T} : T -> lhs -> Prop :=
| wt_lhs_var :
    forall t r s p sd d'
      (SCR: scopeofRefP wc r s)
      (SR: rlookup wc s r p sd d')
      (TD: typofDecl T G sd d' t),
      wt_lhs t (Var r)
| wt_lhs_field :
    forall
      t r e sd s' p d' sc sc'
      (WT: wt_exp e)
      (SUB: sub' (expType e) (Tclass sc sd))
      (ASC: assocScope T G sc sd sc')
      (SCR: scopeofRefP wc r s')
      (LS: linksofScopeP wc s' [(I,[sc'])])
      (SR: rlookup wc s' r p sc' d')
      (TD: typofDecl T G sc' d' t),
      wt_lhs t (Field e r)
.

Inductive wt_decls {G: @WCGAT T} : list decl -> Prop :=
| wt_decls_rec : forall
    s fds rss es optr d ds s' ds' ts
    (SD: assocScope T G s d s')
    (DS: declsofScopeP wc s' ds')
    (TS: typofDecls T G s' ds' ts)
    (SDS: forall fd, In fd fds ->
                     match fldDT fd with
                     | Some (d, t') =>
                       typofDecl T G s d t'
                     | None => True
                     end)
    (EQ: (rss, es) = unzipfs fds)
    (WTE: Forall2 (fun e rs =>
                     match rs with
                     | (sr, r) =>
                       exists p s'' d' t',
                       rlookup wc sr r p s'' d' /\
                       typofDecl T G s'' d' t' /\ sub' (expType e) t' /\ wt_exp e
                     end) es rss)
    (WTS: wt_decls ds)
    (TD: typofDecl T G s d (TclassDef s d))
    (PARENT: match optr with
             | Some (sr, r) =>
               exists p s'' dpar,
               rlookup wc sr r p s'' dpar /\
               typofDecl T G s'' dpar (TclassDef s'' dpar)
             | None => True
             end),
    wt_decls ((Cdef s d optr fds) :: ds)
| wt_decl_nil :
    wt_decls nil.

Inductive wt_prog {G: @WCGAT T} : prog -> Prop :=
| wt_prog_ : forall
    s t e rds ds ts
    (DS: declsofScopeP wc s ds)
    (TDS: typofDecls T G s ds ts)
    (WTD: wt_decls rds)
    (WTE: wt_exp (E s t e)),
    wt_prog (Prog rds (E s t e))
.
