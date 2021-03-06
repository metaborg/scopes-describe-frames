Require Import L2.syntax scopes prop_fold.

(** Well-typed L2 expressions, declarations, and programs, as in paper Fig. 18 *)

Section WellTypedness.

Context `{G: Graph (@AT T)}.

Inductive wt_exp : exp -> Prop :=
| wt_cnum :
    forall s t z,
      t = Tint ->
      wt_exp (E s t (CNum z))
| wt_ctrue :
    forall s t,
      t = Tbool->
      wt_exp (E s t CTrue)
| wt_cfalse :
    forall s t,
      t = Tbool->
      wt_exp (E s t CFalse)
| wt_plus :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: wt_exp (E s2 t2 e2)),
      t = Tint ->
      t1 = Tint ->
      t2 = Tint ->
      wt_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wt_gt :
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
      s t s1 t1 e1 t2s e2s
      (WT1: wt_exp (E s1 t1 e1))
      (WT2: Forall2 (fun e t =>
                       expType e = t /\
                       wt_exp e) e2s t2s),
      t1 = Tarrow t2s t ->
      wt_exp (E s t (App (E s1 t1 e1) e2s))
| wt_letpar :
    forall
      s t t1s bs ds e1s s2 t2 e2 tds
      (UNZIP: unzipb bs = (ds,e1s))
      (TD: typofDecls ds tds)
      (WT1: Forall2 (fun e t =>
                       expType e = t /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2 e2)),
      tds = t1s ->
      t = t2 ->
      wt_exp (E s t (LetPar bs (E s2 t2 e2)))
| wt_letseq :
    forall
      s t t1s bs ds e1s s2 t2 e2
      (UNZIP: unzipb bs = (ds,e1s))
      (TD: typofDecls ds t1s)
      (WT1: Forall2 (fun e t1 => expType e = t1 /\
                                 wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2 e2)),
      t = t2 ->
      wt_exp (E s t (LetSeq bs (E s2 t2 e2)))
| wt_letrec :
    forall
      s t t1s bs ds e1s s2 t2 e2 tds
      (UNZIP: unzipb bs = (ds,e1s))
      (TD: typofDecls ds tds)
      (WT1: Forall2 (fun e t =>
                       (* We check that the RHS is a value *)
                       is_val e /\
                       match t with
                       | Tarrow _ _ => t = expType e
                       | _ => False
                       end /\
                       wt_exp e) e1s t1s)
      (WT2: wt_exp (E s2 t2 e2)),
      tds = t1s ->
      t = t2 ->
      wt_exp (E s t (LetRec bs (E s2 t2 e2)))
| wt_asgn :
    forall
      s t s1 t1 e1 lhs
      (LHS: wt_lhs t lhs)
      (WT1: wt_exp (E s1 t1 e1)),
      t = t1 ->
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
      (RL: rlookup r p sd drec),
      t = Trecord drec ->
      wt_exp (E s t (New r))

with wt_lhs : T -> lhs -> Prop :=
| wt_lhs_var :
    forall t r s p sd d'
      (SCR: scopeofRefP r s)
      (SR: rlookup r p sd d')
      (TD: typofDecl d' t),
      wt_lhs t (Var r)
| wt_lhs_field :
    forall
      t r drec e srec s' p sd' d'
      (WT: wt_exp e)
      (ET: expType e = Trecord drec)
      (ASC: assocScope drec srec)
      (LS: linksofScopeP s' [(I,[srec])])
      (SCR: scopeofRefP r s')
      (SR: rlookup r p sd' d')
      (TD: typofDecl d' t),
      wt_lhs t (Field e r)
.

Inductive wt_dec : ScopeId -> decl -> Prop :=
| wb_rec_dec :
    forall
      s d lf
      (WS: forall fd,
          In fd lf ->
          typofDecl (fldDecl fd) (fldType fd)),
      wt_dec s (Rdef d lf).

Inductive wt_prog : prog -> Prop :=
| wt_prog_ :
    forall
      s t e decs
      (WBD: forall dec,
          In dec decs ->
          wt_dec s dec)
      (WTE: wt_exp (E s t e)),
      wt_prog (Prog decs (E s t e))
.

End WellTypedness.