Require Export frames L3.syntax.

(* Dynamics *)

Inductive Error :=
| NullPointer : Error (* Attempting to apply a null value *)
| Wrong : Error (* Getting stuck *)
.

Inductive V :=
| NumV : Z -> V
| BoolV : bool -> V
| ClosV : list D -> exp -> FrameId -> V
| DefFunV : V -> V
| ObjectV : FrameId -> V
| ConstructorV : ScopeId -> D -> option (ScopeId * R) -> (list (ScopeId * R) * list exp) -> FrameId -> V
| NullV : V
| AbortV : Error -> V
.

(* Outcomes of auxiliary computations: *)
Inductive AuxV :=
| UnitAV
| FrameAV : FrameId -> AuxV
| AbortAV : Error -> AuxV
| AddrAV : Addr -> AuxV
.

Definition abort (v: V) : V :=
  match v with
  | AbortV e => AbortV e
  | _ => AbortV Wrong
  end.

Definition aborta (v: V) : AuxV :=
  match v with
  | AbortV e => AbortAV e
  | _ => AbortAV Wrong
  end.

Definition aabort (v: AuxV) : V :=
  match v with
  | AbortAV e => AbortV e
  | _ => AbortV Wrong
  end.

Definition aaborta (v: AuxV) : AuxV :=
  match v with
  | AbortAV e => AbortAV e
  | _ => AbortAV Wrong
  end.

Definition good (v: V) :=
  match v with
  | AbortV _ => False
  | _ => True
  end.

(* Runtime upcast of an object *)
Section WithG.

  Context {G: @WCGAT T} {VT: @VTyp T V}.

  Inductive upcast : H -> FrameId -> ScopeId -> FrameId -> Prop :=
  | upcast_ :
      forall
        h f s
        (SF: scopeofFrame V fh h f s),
        upcast h f s f
  | upcast_up :
      forall
        h f s imf f' imfs si
        (IMS: llinksofFrame V fh h f I imfs)
        (IN: get ScopeIdDec imfs si = Some imf)
        (RC: upcast h imf s f'),
        upcast h f s f'.

  (* Note that evaluation does not inspect the type labels at all.
   (Should perhaps make this somehow more explicit.) *)
  Inductive eval_exp {DVT: @DefaultVTyp T V VT} : H -> FrameId -> exp -> V -> H -> Prop :=
  | eval_cnum_ :
      forall
        frm z h s t,
        eval_exp h frm (E s t (CNum z)) (NumV z) h
  | eval_true_ :
      forall
        frm h s t,
        eval_exp h frm (E s t CTrue) (BoolV true) h
  | eval_false_:
      forall
        frm h s t,
        eval_exp h frm (E s t CFalse) (BoolV false) h
  | eval_plus_:
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
  | eval_gt_:
      forall
        frm e1 e2 z1 z2 h0 h1 h2 s t
        (EVALL: eval_exp h0 frm e1 (NumV z1) h1)
        (EVALR: eval_exp h1 frm e2 (NumV z2) h2),
        eval_exp h0 frm (E s t (Gt e1 e2)) (BoolV (Z.gtb z1 z2)) h2
  | eval_gt_b1 :
      forall
        frm e1 e2 h0 v1 h1 s t
        (EVALL: eval_exp h0 frm e1 v1 h1)
        (ABORTL:forall z1, v1 <> NumV z1),
        eval_exp h0 frm (E s t (Gt e1 e2)) (abort v1) h1
  | eval_gt_b2 :
      forall
        frm e1 e2 h0 z1 v2 h1 h2 s t
        (EVALL: eval_exp h0 frm e1 (NumV z1) h1)
        (EVALR: eval_exp h1 frm e2 v2 h2)
        (ABORTR: forall z2, v2 <> NumV z2),
        eval_exp h0 frm (E s t (Gt e1 e2)) (abort v2) h2
  | eval_lhs_:
      forall
        frm s t lhs h0 h1 ff d v
        (EVLHS: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
        (GET: getSlot V fh h1 ff d v),
        eval_exp h0 frm (E s t (Lhs lhs)) v h1
  | eval_lhs_b1 :
      forall
        frm lhs h0 s t h1 q
        (EVLHS: eval_lhs h0 frm lhs (AbortAV q) h1),
        eval_exp h0 frm (E s t (Lhs lhs)) (AbortV q) h1
  | eval_lhs_b2 :
      forall
        frm s t lhs h0 h1 ff d
        (EVLHS: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
        (GET: forall v, ~ getSlot V fh h1 ff d v),
        eval_exp h0 frm (E s t (Lhs lhs)) (AbortV Wrong) h1
  | eval_fn_ :
      forall
        frm h s t ds e,
        eval_exp h frm (E s t (Fn ds e)) (ClosV ds e frm) h
  | eval_app :
      forall
        frm h0 h1 h2 h3 h4 e1 e2s s t vb ff sf f e ds
        (EVAL1: eval_exp h0 frm e1 (ClosV ds e ff) h1)
        (SF: scopeofFrame V fh h1 ff sf)
        (NF: initNewDefaultFrame DVT h1 (expScope e) [(P, [(sf, ff)])] f h2)
        (EVAL2: fill_slots_par h2 frm f ds e2s UnitAV h3)
        (EVALBODY: eval_exp h3 f e vb h4),
        eval_exp h0 frm (E s t (App e1 e2s)) vb h4
  | eval_app_dfun :
      forall
        h0 frm h1 s t e1 e2s v
        (EVAL1: eval_exp h0 frm e1 (DefFunV v) h1),
        eval_exp h0 frm (E s t (App e1 e2s)) v h1
  | eval_app_b1 :
      forall
        h0 frm v1 h1 s t e1 e2s
        (EVAL1: eval_exp h0 frm e1 v1 h1)
        (ABORT1: match v1 with
                 | ClosV _ _ _ => False
                 | DefFunV _ => False
                 | _ => True
                 end),
        eval_exp h0 frm (E s t (App e1 e2s)) (abort v1) h1
  | eval_app_b2 :
      forall
        h0 frm e1 h1 e2s h2 h3 s t ds e ff sf f q
        (EVAL1: eval_exp h0 frm e1 (ClosV ds e ff) h1)
        (SF: scopeofFrame V fh h1 ff sf)
        (NF: initNewDefaultFrame DVT h1 (expScope e) [(P, [(sf, ff)])] f h2)
        (ABORT2: fill_slots_par h2 frm f ds e2s (AbortAV q) h3),
        eval_exp h0 frm (E s t (App e1 e2s)) (AbortV q) h3
  (* remaining bad case in tail position *)
  | eval_letpar_ :
      forall
        frm h0 h1 h2 h3 lb ds es e2 v2 ff sf s t
        (UNZIP: unzipb lb = (ds,es))
        (SF: scopeofFrame V fh h1 frm sf)
        (NF: initNewDefaultFrame DVT h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
        (EVAL1: fill_slots_par h1 frm ff ds es UnitAV h2)
        (EVAL2: eval_exp h2 ff e2 v2 h3),
        eval_exp h0 frm (E s t (LetPar lb e2)) v2 h3
  | eval_letpar_b1 :
      forall
        frm h0 h1 h2 lb ds es e2 s t ff sf q
        (UNZIP : unzipb lb = (ds,es))
        (SF: scopeofFrame V fh h1 frm sf)
        (NF: initNewDefaultFrame DVT h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
        (ABORT1: fill_slots_par h1 frm ff ds es (AbortAV q) h2),
        eval_exp h0 frm (E s t (LetPar lb e2)) (AbortV q) h2
  (* remaining bad case is in tail position *)
  | eval_letseq_ :
      forall
        frm h0 h1 h2 lb dss es e2 v2 s t fi
        (UNZIP: unzipbs lb = (dss,es))
        (* Returns the innermost frame: *)
        (EVAL1: fill_slots_seq h0 frm dss es (FrameAV fi) h1)
        (EVAL2: eval_exp h1 fi e2 v2 h2),
        eval_exp h0 frm (E s t (LetSeq lb e2)) v2 h2
  | eval_letseq_b1 :
      forall
        frm h0 h1 lb dss es e2 s t q
        (UNZIP: unzipbs lb = (dss,es))
        (* Returns the innermost frame: *)
        (ABORT1 : fill_slots_seq h0 frm dss es (AbortAV q) h1),
        eval_exp h0 frm (E s t (LetSeq lb e2)) (AbortV q) h1
  (* remaining bad case is in tail position *)
  | eval_letrec_ :
      forall
        frm h0 h1 h2 h3 lvb ds evs e2 v2 ff sf s t
        (UNZIP: unzipb lvb = (ds,evs))
        (SF: scopeofFrame V fh h1 frm sf)
        (NF: initNewDefaultFrame DVT h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
        (EVAL1: fill_slots_rec h1 ff ds evs UnitAV h2)
        (EVAL2: eval_exp h2 ff e2 v2 h3),
        eval_exp h0 frm (E s t (LetRec lvb e2)) v2 h3
  | eval_letrec_b1 :
      forall
        frm h0 h1 h2 lb ds es e2 s t ff sf q
        (UNZIP: unzipb lb = (ds,es))
        (SF: scopeofFrame V fh h1 frm sf)
        (NF: initNewDefaultFrame DVT h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
        (ABORT1: fill_slots_rec h1 ff ds es (AbortAV q) h2),
        eval_exp h0 frm (E s t (LetRec lb e2)) (AbortV q) h2
  (* remaining bad case is in tail position *)
  | eval_asgn_ :
      forall
        h0 frm s t lhs e h1 h2 ff d v h3
        (EVLHS: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
        (EVAL: eval_exp h1 frm e v h2)
        (SET: setSlot V fh h2 ff d v h3),
        eval_exp h0 frm (E s t (Asgn lhs e)) v h3
  | eval_asgn_b1 :
      forall
        h0 frm s t lhs e h1 q
        (EVAL: eval_lhs h0 frm lhs (AbortAV q) h1),
        eval_exp h0 frm (E s t (Asgn lhs e)) (AbortV q) h1
  | eval_asgn_b2 :
      forall
        h0 frm s t lhs e h1 ff d q h2
        (EVAL: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
        (ABORT: eval_exp h1 frm e (AbortV q) h2), (* not quite in tail position *)
        eval_exp h0 frm (E s t (Asgn lhs e)) (AbortV q) h2
  | eval_asgn_b3 :
      forall
        h0 frm s t lhs e h1 h2 ff d v
        (EVLHS: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
        (EVAL: eval_exp h1 frm e v h2)
        (SET: forall h3, ~ setSlot V fh h2 ff d v h3),
        eval_exp h0 frm (E s t (Asgn lhs e)) (AbortV Wrong) h2
  | eval_if_t :
      forall
        frm e1 e2 e3 v h0 h1 h2 s t
        (EVAL1: eval_exp h0 frm e1 (BoolV true) h1)
        (EVAL2: eval_exp h1 frm e2 v h2),
        eval_exp h0 frm (E s t (If e1 e2 e3)) v h2
  | eval_if_f :
      forall
        frm e1 e2 e3 v h0 h1 h2 s t
        (EVAL1: eval_exp h0 frm e1 (BoolV false) h1)
        (EVAL3: eval_exp h1 frm e3 v h2),
        eval_exp h0 frm (E s t (If e1 e2 e3)) v h2
  | eval_if_b1:
      forall
        frm e1 e2 e3 h0 h1 v1 s t
        (EVAL1: eval_exp h0 frm e1 v1 h1)
        (ABORT1: forall b, v1 <> BoolV b),
        eval_exp h0 frm (E s t (If e1 e2 e3)) (abort v1) h1
  (* other bad bases are in tail position *)
  | eval_seq_ :
      forall
        frm e1 e2 v1 v2 h0 h1 h2 s t
        (EVAL1: eval_exp h0 frm e1 v1 h1)
        (GOOD1: good v1)
        (EVAL2: eval_exp h1 frm e2 v2 h2),
        eval_exp h0 frm (E s t (Seq e1 e2)) v2 h2
  | eval_seq_b1 :
      forall
        frm e1 e2 h0 h1 s t q
        (EVAL1: eval_exp h0 frm e1 (AbortV q) h1),
        eval_exp h0 frm (E s t (Seq e1 e2)) (AbortV q) h1
  (* other bad case in tail position *)
  | eval_new_ :
      forall
        frm r h0 h1 rf s t
        (INITR: eval_objinit h0 frm s r (FrameAV rf) h1),
        eval_exp h0 frm (E s t (New r)) (ObjectV rf) h1
  | eval_new_b1 :
      forall
        frm r h0 h1 s t av
        (INITR: eval_objinit h0 frm s r av h1)
        (BAD: match av with
              | FrameAV _ => False
              | _ => True
              end),
        eval_exp h0 frm (E s t (New r)) (aabort av) h1

  with eval_lhs {DVT: @DefaultVTyp T V VT} : H -> FrameId -> lhs -> AuxV -> H -> Prop :=
  | eval_lhs_var_ :
      forall
        h frm r a
        (ADDR: getAddr V fh wc h frm r a),
        eval_lhs h frm (Var r) (AddrAV a) h
  | eval_lhs_var_b :
      forall
        h frm r
        (ADDR: forall a, ~ getAddr V fh wc h frm r a),
        eval_lhs h frm (Var r) (AbortAV Wrong) h
  | eval_lhs_field :
      forall
        h0 frm e r s rf h1 h2 a rec_s rf' imp_f
        (EVAL: eval_exp h0 frm e (ObjectV rf) h1)
        (SCR: scopeofRefP wc r s)
        (IMP: llinksofScopeP (@g gat wc) s I [rec_s])
        (UPCAST: upcast h1 rf rec_s rf')
        (SCF: initNewDefaultFrame DVT h1 s [(I, [(rec_s, rf')])] imp_f h2)
        (ADDR: getAddr V fh wc h2 imp_f r a),
        eval_lhs h0 frm (Field e r) (AddrAV a) h2
  | eval_lhs_field_null :
      forall
        h0 frm e r h1
        (EVAL: eval_exp h0 frm e NullV h1),
        eval_lhs h0 frm (Field e r) (AbortAV NullPointer) h1
  | eval_lhs_field_b1:
      forall
        h0 frm e r h1 v
        (EVAL: eval_exp h0 frm e v h1)
        (BAD: match v with
              | ObjectV _ => False
              | NullV => False
              | _ => True
              end),
        eval_lhs h0 frm (Field e r) (aborta v) h1
  | eval_lhs_field_b2 :
      forall
        h0 frm e r s rf h1 rec_s
        (EVAL: eval_exp h0 frm e (ObjectV rf) h1)
        (SCR: scopeofRefP wc r s)
        (IMP: llinksofScopeP (@g gat wc) s I [rec_s])
        (UPCAST: forall rf', ~ upcast h1 rf rec_s rf'),
        eval_lhs h0 frm (Field e r) (AbortAV Wrong) h1
  | eval_lhs_field_b3:
      forall
        h0 frm e r s rf h1 h2 rec_s rf' imp_f
        (EVAL: eval_exp h0 frm e (ObjectV rf) h1)
        (SCR: scopeofRefP wc r s)
        (IMP: llinksofScopeP (@g gat wc) s I [rec_s])
        (UPCAST: upcast h1 rf rec_s rf')
        (SCF: initNewDefaultFrame DVT h1 s [(I, [(rec_s, rf')])] imp_f h2)
        (ADDR: forall a, ~ getAddr V fh wc h2 imp_f r a),
        eval_lhs h0 frm (Field e r) (AbortAV Wrong) h2

  with fill_slots_par {DVT: @DefaultVTyp T V VT} : H -> FrameId -> FrameId -> list D -> list exp -> AuxV -> H -> Prop :=
  | fill_par_nil :
      forall
        h frm fc,
        fill_slots_par h frm fc nil nil UnitAV h
  | fill_par_b1 :
      forall
        h frm fc ld,
        ld <> nil ->
        fill_slots_par h frm fc ld nil (AbortAV Wrong) h
  | fill_par_b2 :
      forall
        h frm fc le,
        le <> nil ->
        fill_slots_par h frm fc nil le (AbortAV Wrong) h
  | fill_par_cons :
      forall
        h0 frm e d es ds fc v h1 h2 h3 v1
        (EVAL: eval_exp h0 frm e v h1)
        (GOOD: good v)
        (SS: setSlot V fh h1 fc d v h2)
        (TAIL: fill_slots_par h2 frm fc ds es v1 h3),
        fill_slots_par h0 frm fc (d::ds) (e::es) v1 h3
  | fill_par_cons_b3 :
      forall
        h0 frm e d es ds fc v h1
        (EVAL: eval_exp h0 frm e v h1)
        (GOOD: good v)
        (SS: forall h2, ~ setSlot V fh h1 fc d v h2),
        fill_slots_par h0 frm fc (d::ds) (e::es) (AbortAV Wrong) h1
  | fill_par_cons_b :
      forall
        h0 frm e es d ds fc h1 q
        (EVAL: eval_exp h0 frm e (AbortV q) h1),
        fill_slots_par h0 frm fc (d :: ds) (e :: es) (AbortAV q) h1
  (* other bad case is in tail position*)

  with fill_slots_seq {DVT: @DefaultVTyp T V VT} : H -> FrameId -> list (ScopeId * D) -> list exp -> AuxV -> H -> Prop :=

       (* This relation could have been implemented by desugaring sequential
lets into nested parallel lets. *)

  | fill_seq_nil :
      forall
        h frm,
        fill_slots_seq h frm nil nil (FrameAV frm) h
  | fill_seq_b1 :
      forall
        h frm ld,
        ld <> nil ->
        fill_slots_seq h frm ld nil (AbortAV Wrong) h
  | fill_seq_b2 :
      forall
        h frm le,
        le <> nil ->
        fill_slots_seq h frm nil le (AbortAV Wrong) h
  | fill_seq_cons :
      forall
        h0 frm e es d ds fc v h1 h2 h3 h4 v1 sd sf
        (SF: scopeofFrame V fh h0 frm sf)
        (NF: initNewDefaultFrame DVT h0 sd [(P, [(sf, frm)])] fc h1)
        (EVAL: eval_exp h1 frm e v h2)   (* APT: could/should this come before the NF creation? *)
        (GOOD: good v)
        (SS: setSlot V fh h2 fc d v h3)
        (TAIL: fill_slots_seq h3 fc ds es v1 h4),
        fill_slots_seq h0 frm  ((sd, d) :: ds) (e :: es) v1 h4
  | fill_seq_cons_b1 :
      forall
        h0 frm e es d ds h1 sd fc h2 q sf
        (SF: scopeofFrame V fh h0 frm sf)
        (NF: initNewDefaultFrame DVT h0 sd [(P, [(sf, frm)])] fc h1)
        (EVAL: eval_exp h1 frm e (AbortV q) h2),
        fill_slots_seq h0 frm ((sd, d) :: ds) (e :: es) (AbortAV q) h2
  | fill_seq_cons_b2 :
      forall
        h0 frm e es d ds fc v h1 h2 sd sf
        (SF: scopeofFrame V fh h0 frm sf)
        (NF: initNewDefaultFrame DVT h0 sd [(P, [(sf, frm)])] fc h1)
        (EVAL: eval_exp h1 frm e v h2)   (* APT: could/should this come before the NF creation? *)
        (GOOD: good v)
        (SS: forall h3, ~ setSlot V fh h2 fc d v h3),
        fill_slots_seq h0 frm  ((sd, d) :: ds) (e :: es) (AbortAV Wrong) h2
  (* other bad case is in tail position *)

  with fill_slots_rec {DVT: @DefaultVTyp T V VT} : H -> FrameId -> list D -> list exp -> AuxV -> H -> Prop :=

       (* This relation could have been implemented as a special case of
fill_slots_par, where the context frame and the slots frame
coincide. *)

  | fill_rec_nil :
      forall
        h frm,
        fill_slots_rec h frm nil nil UnitAV h
  | fill_rec_b1 :
      forall
        h frm ld,
        ld <> nil ->
        fill_slots_rec h frm ld nil (AbortAV Wrong) h
  | fill_rec_b2 :
      forall
        h frm le,
        le <> nil ->
        fill_slots_rec h frm nil le (AbortAV Wrong) h
  | fill_rec_cons :
      forall
        h0 frm e d es ds v h1 h2 h3 v1
        (EVAL: eval_exp h0 frm e v h1)
        (GOOD: good v)
        (SS: setSlot V fh h1 frm d v h2)
        (TAIL: fill_slots_rec h2 frm ds es v1 h3),
        fill_slots_rec h0 frm (d::ds) (e::es) v1 h3
  | fill_rec_cons_b1 :
      forall
        h0 frm e es d ds h1 q
        (EVAL: eval_exp h0 frm e (AbortV q) h1),
        fill_slots_rec h0 frm (d :: ds) (e :: es) (AbortAV q) h1
  | fill_rec_cons_b2 :
      forall
        h0 frm e d es ds v h1 v1
        (EVAL: eval_exp h0 frm e v h1)
        (GOOD: good v)
        (SS: forall h2, ~ setSlot V fh h1 frm d v h2),
        fill_slots_rec h0 frm (d::ds) (e::es) v1 h1
  (* other bad case is in tail position *)

  with eval_objinit {DVT: @DefaultVTyp T V VT} : H -> FrameId -> ScopeId -> R -> AuxV -> H -> Prop :=
  | eval_objinit_:
      forall
        s1 h0 frm rf r ff d h1 rs es h2 spar rpar f rfpar s0 h3 h4 s sf sfpar
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d (ConstructorV s1 d (Some (spar, rpar)) (rs,es) f))
        (* initialize the imported parent *)
        (INIT: eval_objinit h1 f spar rpar (FrameAV rfpar) h2)
        (* initialize frame scope with the right lexical parent *)
        (ASR: assocScopeofRef T G s r s0)
        (SF: scopeofFrame V fh h2 f sf)
        (SFP: scopeofFrame V fh h2 rfpar sfpar)
        (RECF: initNewDefaultFrame DVT h2 s0 [(P, [(sf, f)]); (I, [(sfpar, rfpar)])] rf h3)
        (* initializers evaluated in the scope of the record *)
        (ASGN: assign_refs h3 rf rf rs es UnitAV h4),
        eval_objinit h0 frm s r (FrameAV rf) h4
  | eval_objinit_b1:
      forall
        s h0 frm r h1 v
        (LHS: eval_lhs h0 frm (Var r) v h1)
        (BAD: match v with
              | AddrAV _ => False
              | _ => True
              end),
        eval_objinit h0 frm s r (aaborta v) h1
  | eval_objinit_b2:
      forall
        s h0 frm v h1 ff d r
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: forall v, ~ getSlot V fh h1 ff d v),
        eval_objinit h0 frm s r (aborta v) h1
  | eval_objinit_b3:
      forall
        s h0 frm v h1 ff d r
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d v)
        (BAD: match v with
              | ConstructorV _ _ _ _ _ => False
              | _ => True
              end),
        eval_objinit h0 frm s r (aborta v) h1
  | eval_objinit_b4:
      forall
        s h0 frm r ff s1 d h1 rs es h2 v f spar rpar
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d (ConstructorV s1 d (Some (spar, rpar)) (rs,es) f))
        (* initialize the imported parent *)
        (INIT: eval_objinit h1 f spar rpar v h2)
        (BAD: match v with
              | FrameAV _ => False
              | _ => True
              end),
        eval_objinit h0 frm s r (aaborta v) h2
  | eval_objinit_b5:
      forall
        s1 s h0 frm rf r ff d h1 rs es h2 spar rpar f rfpar s0 h3 h4 v sf sfpar
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d (ConstructorV s1 d (Some (spar, rpar)) (rs,es) f))
        (* initialize the imported parent *)
        (INIT: eval_objinit h1 f spar rpar (FrameAV rfpar) h2)
        (* initialize frame scope with the right lexical parent *)
        (ASR: assocScopeofRef T G s r s0)
        (SF: scopeofFrame V fh h2 f sf)
        (SFP: scopeofFrame V fh h2 rfpar sfpar)
        (RECF: initNewDefaultFrame DVT h2 s0 [(P, [(sf, f)]); (I, [(sfpar, rfpar)])] rf h3)
        (* initializers evaluated in the scope of the record *)
        (ASGN: assign_refs h3 rf rf rs es v h4)
        (BAD: match v with
              | UnitAV => False
              | _ => True
              end),
        eval_objinit h0 frm s r (aaborta v) h4
  | eval_objinit_orphan:
      forall
        s h0 frm rf r ff d h1 rs es h2 f s0 h3 s1 sf
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d (ConstructorV s1 d None (rs,es) f))
        (* initialize frame scope with the right lexical parent *)
        (ASR: assocScopeofRef T G s r s0)
        (SF: scopeofFrame V fh h1 f sf)
        (RECF: initNewDefaultFrame DVT h1 s0 [(P, [(sf, f)])] rf h2)
        (* initializers evaluated in the scope of the record *)
        (ASGN: assign_refs h2 rf rf rs es UnitAV h3),
        eval_objinit h0 frm s r (FrameAV rf) h3
  | eval_objinit_orphan_b1:
      forall
        h0 frm r ff d h1 s
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: forall v, ~ getSlot V fh h1 ff d v),
        eval_objinit h0 frm s r (AbortAV Wrong) h1
  | eval_objinit_orphan_b2:
      forall
        h0 frm rf r ff d h1 rs es h2 f s0 h3 v s sf s1
        (LHS: eval_lhs h0 frm (Var r) (AddrAV (Addr_ ff d)) h1)
        (GS: getSlot V fh h1 ff d (ConstructorV s1 d None (rs,es) f))
        (* initialize frame scope with the right lexical parent *)
        (ASR: assocScopeofRef T G s r s0)
        (SF: scopeofFrame V fh h1 f sf)
        (RECF: initNewDefaultFrame DVT h1 s0 [(P, [(sf, f)])] rf h2)
        (* initializers evaluated in the scope of the record *)
        (ASGN: assign_refs h2 rf rf rs es v h3)
        (BAD: match v with
              | UnitAV => False
              | _ => True
              end),
        eval_objinit h0 frm s r (aaborta v) h3

  with assign_refs {DVT: @DefaultVTyp T V VT} : H -> FrameId -> FrameId -> list (ScopeId * R) -> list exp -> AuxV -> H -> Prop :=
  | assign_refs_nil:
      forall
        h frm fs,
        assign_refs h frm fs nil nil UnitAV h
  | assign_refs_cons:
      forall
        h0 eval_frm imp_frm e v h1 h2 h3 ff d r es rs av s
        (ADDR: getAddr V fh wc h0 imp_frm r (Addr_ ff d))
        (EVAL: eval_exp h0 eval_frm e v h1)
        (GOOD: good v)
        (SET: setSlot V fh h1 ff d v h2)
        (TAIL: assign_refs h2 eval_frm imp_frm rs es av h3),
        assign_refs h0 eval_frm imp_frm ((s, r) :: rs) (e :: es) av h3
  | assign_refs_b1:
      forall
        h eval_frm imp_frm rs,
        rs <> nil ->
        assign_refs h eval_frm imp_frm rs nil (AbortAV Wrong) h
  | assign_refs_b2:
      forall
        h eval_frm imp_frm es,
        es <> nil ->
        assign_refs h eval_frm imp_frm nil es (AbortAV Wrong) h
  | assign_refs_cons_b1:
      forall
        h0 eval_frm imp_frm e r es rs s
        (ADDR: forall ff d, ~ getAddr V fh wc h0 imp_frm r (Addr_ ff d)),
        assign_refs h0 eval_frm imp_frm ((s, r) :: rs) (e :: es) UnitAV h0
  | assign_refs_cons_b2:
      forall
        h0 eval_frm imp_frm e h1 ff d r es rs q s
        (ADDR: getAddr V fh wc h0 imp_frm r (Addr_ ff d))
        (EVAL: eval_exp h0 eval_frm e (AbortV q) h1),
        assign_refs h0 eval_frm imp_frm ((s, r) :: rs) (e :: es) (AbortAV q) h1
(* other bad case is in tail position*)
  .

  (* Combined induction scheme *)
  Scheme eval_exp_ind2 := Minimality for eval_exp Sort Prop
  with fill_par_ind2 := Minimality for fill_slots_par Sort Prop
  with fill_seq_ind2 := Minimality for fill_slots_seq Sort Prop
  with fill_rec_ind2 := Minimality for fill_slots_rec Sort Prop
  with eval_lhs_ind2 := Minimality for eval_lhs Sort Prop
  with eval_objinit_ind2 := Minimality for eval_objinit Sort Prop
  with assign_refs_ind2 := Minimality for assign_refs Sort Prop.
  Combined Scheme eval_exp_ind3
           from eval_exp_ind2, fill_par_ind2, fill_seq_ind2, fill_rec_ind2, eval_lhs_ind2, eval_objinit_ind2, assign_refs_ind2.

  Inductive init_decls : H -> FrameId -> list decl -> H -> Prop :=
  | init_decl_rdef :
      forall
        h0 frm s rd optr fds ids h1 h2
        (SS: setSlot V fh h0 frm rd (ConstructorV s rd optr (unzipfs fds) frm) h1)
        (IDS: init_decls h1 frm ids h2),
        init_decls h0 frm ((Cdef s rd optr fds) :: ids) h2
  | init_decl_nil :
      forall
        h0 frm,
        init_decls h0 frm nil h0
  .

  Inductive eval_prog {DVT: @DefaultVTyp T V VT} : prog -> V -> Prop :=
  | eval_prog_ : forall
      e v f h0 h1 rds
      (* empty root frame *)
      (TOPFRM: initNewDefaultFrame DVT (emptyHeap) (expScope e) [] f h0)
      (INITDS: init_decls h0 f rds h1)
      (EVALB: eval_exp h0 f e v h1),
      eval_prog (Prog rds e) v
  .

End WithG.
