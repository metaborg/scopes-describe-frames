Require Import L2.syntax scopes prop_fold.

Section WellBoundness.

(** Well-bounded L2 expressions, declarations and programs, as in
paper Fig. 17. *)

Context `{G: Graph (@AT T)}.

Inductive wb_exp : exp -> Prop :=
| wb_cnum :
    forall s t z,
      wb_exp (E s t (CNum z))
| wb_ctrue :
    forall s t,
      wb_exp (E s t CTrue)
| wb_cfalse :
    forall s t,
      wb_exp (E s t CFalse)
| wb_plus :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WB1: wb_exp (E s1 t1 e1))
      (WB2:wb_exp (E s2 t2 e2)),
      s = s2 ->
      s = s1 ->
      wb_exp (E s t (Plus (E s1 t1 e1) (E s2 t2 e2)))
| wb_gt :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WB1: wb_exp (E s1 t1 e1))
      (WB2: wb_exp (E s2 t2 e2)),
      s = s1 ->
      s = s2 ->
      wb_exp (E s t (Gt (E s1 t1 e1) (E s2 t2 e2)))
| wb_lhs_ :
    forall
      s t lhs
      (WB: wb_lhs s lhs),
      wb_exp (E s t (Lhs lhs))
| wb_fn :
    forall
      s t ds s1 t1 e1
      (WB1: wb_exp (E s1 t1 e1))
      (PS: linksofScopeP s1 [(P, [s])])
      (DS: declsofScopeP s1 ds),
      wb_exp (E s t (Fn ds (E s1 t1 e1)))
| wb_app :
    forall
      s t s1 t1 e1 s2 e2s
      (WB1: wb_exp (E s1 t1 e1))
      (WB2: forall e2,
          In e2 e2s ->
          (expScope e2) = s2 /\
          wb_exp e2),
      s = s1 ->
      s = s2 ->
      wb_exp (E s t (App (E s1 t1 e1) e2s))
| wb_letpar :
    forall
      s t s1 bs ds e1s s2 t2 e2
      (UNZIP: unzipb bs = (ds,e1s))
      (WB1: forall e1,
          In e1 e1s ->
          (expScope e1) = s1 /\
          wb_exp e1)
      (PS: linksofScopeP s2 [(P, [s])])
      (DS: declsofScopeP s2 ds)
      (WB2:wb_exp (E s2 t2 e2)),
      s = s1 ->
      wb_exp (E s t (LetPar bs (E s2 t2 e2)))
| wb_letseq :
    forall
      s t bs ds e1s s2 t2 e2
      (UNZIP: unzipb bs = (ds, e1s))
      (* Propositional fold threading parent scopes through sequential let *)
      (WB1: ForallFold2 (fun d e ps newPs =>
                           (linksofScopeP newPs [(P, [ps])]) /\
                           declsofScopeP newPs [d] /\
                           (expScope e) = ps /\
                           wb_exp e)
                        ds e1s s s2)
      (WB2:wb_exp (E s2 t2 e2)),
      wb_exp (E s t (LetSeq bs (E s2 t2 e2)))
| wb_letrec :
    forall
      s t bs ds e1s s2 t2 e2
      (UNZIP: unzipb bs = (ds,e1s))
      (WB1: forall e1,
          In e1 e1s ->
          (expScope e1) = s2 /\ wb_exp e1)
      (LS: linksofScopeP s2 [(P, [s])])
      (DS: declsofScopeP s2 ds)
      (WB2: wb_exp (E s2 t2 e2)),
      wb_exp (E s t (LetRec bs (E s2 t2 e2)))
| wb_asgn :
    forall
      s t s1 t1 e1 lhs
      (WB1: wb_lhs s1 lhs)
      (WB2: wb_exp (E s1 t1 e1)),
      s = s1 ->
      wb_exp (E s t (Asgn lhs (E s1 t1 e1)))
| wb_if : forall
    s t s1 t1 e1 s2 t2 e2 s3 t3 e3
    (WB1: wb_exp (E s1 t1 e1))
    (WB2: wb_exp (E s2 t2 e2))
    (WB3: wb_exp (E s3 t3 e3)),
    s = s1 ->
    s = s2 ->
    s = s3 ->
    wb_exp (E s t (If (E s1 t1 e1) (E s2 t2 e2) (E s3 t3 e3)))
| wb_seq :
    forall
      s t s1 t1 e1 s2 t2 e2
      (WB1: wb_exp (E s1 t1 e1))
      (WB2: wb_exp (E s2 t2 e2)),
      s = s1 ->
      s = s2 ->
      wb_exp (E s t (Seq (E s1 t1 e1) (E s2 t2 e2)))
| wb_new :
    forall
      s t r srec p s' d'
      (SR: scopeofRefP r s)
      (SR: rlookup r p s' d')
      (ASC: assocScope d' srec)
      (PS: linksofScopeP srec []),
      wb_exp (E s t (New r))

with wb_lhs : ScopeId -> lhs -> Prop :=
| wb_lhs_var :
    forall
      s r
      (SR: scopeofRefP r s),
      wb_lhs s (Var r)
| wb_lhs_field :
    forall
      s e r srec s'
      (WB: wb_exp e)
      (ES: expScope e = s)
      (SR: scopeofRefP r s')
      (LS: linksofScopeP s' [(I,[srec])])
      (DSs: declsofScopeP s' []),
      wb_lhs s (Field e r)
.

Inductive wb_dec : ScopeId -> decl -> Prop :=
| wb_rec_dec :
    forall
      d lf s s'
      (DS: scopeofDeclP d s)
      (SD: assocScope d s')
      (WS: forall fd,
          In fd lf ->
          scopeofDeclP (fldDecl fd) s'),
      wb_dec s (Rdef d lf)
.

Inductive wb_prog : prog -> Prop :=
| wb_prog_ :
    forall
      decs s t e
      (WBD: forall dec,
          In dec decs ->
          wb_dec s dec)
      (WBE: wb_exp (E s t e))
      (LS : linksofScopeP s []),
      wb_prog (Prog decs (E s t e))
.

End WellBoundness.
