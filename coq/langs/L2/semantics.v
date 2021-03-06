Require Export frames L2.syntax L2.well_typedness L2.well_boundness.

(** Semantic evaluation rules for L2, as in paper Fig. 19 and Appendix
B. *)

(** L2 can abruptly terminate either by getting stuck ("going
[Wrong]"), or by attempting to use a [NullV] where an actual value was
expected ([NullPointer] exception). *)

Inductive Error :=
| NullPointer : Error
| Wrong : Error
.

(** Values *)
Inductive V :=

(** Number *)
| NumV : Z -> V

(** Boolean *)
| BoolV : bool -> V

(** Closure recording its formal parameter [D]eclarations, function
body [exp]ression, and the lexical parent [FrameId] *)
| ClosV : list D -> exp -> FrameId -> V

(** Default function, which always returns a value [V] of the expected
type *)
| DefFunV : V -> V

(** Record, given by [FrameId] *)
| RecordV : FrameId -> V

(** [NullV] value *)
| NullV : V

(** Aborted computation due to [Error] *)
| AbortV : Error -> V
.

(** We use auxiliary relations for iterating iterating through n-ary
lets, etc. These produce auxiliary values. *)
Inductive AuxV :=

(** Units -- for indicating successful termination for relations that
only affect the store *)
| UnitAV

(** Frame *)
| FrameAV : FrameId -> AuxV

(** Address *)
| AddrAV : Addr -> AuxV

(** Aborted computation due to [Error] *)
| AbortAV : Error -> AuxV
.

(** [abort] either propagates the current reason for aborting, or it
aborts by "going wrong". Similarly for [aborta]. *)

Definition abort (v: V) :=
  match v with
  | AbortV e => AbortV e
  | _ => AbortV Wrong
  end.

Definition aborta (v: V) :=
  match v with
  | AbortV e => AbortAV e
  | _ => AbortAV Wrong
  end.

(** A value is [good] if it is not an [AbortV]. *)
Definition good (v: V) :=
  match v with
  | AbortV _ => False
  | _ => True
  end.

(** * Dynamic Semantics *)

Section DynamicSemantics.

(** We postpone defining [default] values. [DVT] asserts that there is
a type class instance which defines it *)

Context `{G: Graph (@AT T)} `{DVT: DefaultVTyp T V} .

Inductive eval_exp : H -> FrameId -> exp -> V -> H -> Prop :=
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
      (GET: getSlot h1 ff d v),
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
      (GET: forall v, ~ getSlot h1 ff d v),
      eval_exp h0 frm (E s t (Lhs lhs)) (AbortV Wrong) h1
| eval_fn_ :
    forall
      frm h s t ds e,
      eval_exp h frm (E s t (Fn ds e)) (ClosV ds e frm) h
| eval_app :
    forall
      frm h0 h1 h2 h3 h4 e1 e2s s t vb ff sf f e ds
      (EVAL1: eval_exp h0 frm e1 (ClosV ds e ff) h1)
      (SF: scopeofFrame h1 ff sf)
      (NF: initDefault h1 (expScope e) [(P, [(sf, ff)])] f h2)
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
      (SF: scopeofFrame h1 ff sf)
      (NF: initDefault h1 (expScope e) [(P, [(sf, ff)])] f h2)
      (ABORT2: fill_slots_par h2 frm f ds e2s (AbortAV q) h3),
      eval_exp h0 frm (E s t (App e1 e2s)) (AbortV q) h3
(* remaining bad case in tail position *)
| eval_letpar_ :
    forall
      frm h0 h1 h2 h3 lb ds es e2 v2 ff sf s t
      (UNZIP: unzipb lb = (ds,es))
      (SF: scopeofFrame h1 frm sf)
      (NF: initDefault h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
      (EVAL1: fill_slots_par h1 frm ff ds es UnitAV h2)
      (EVAL2: eval_exp h2 ff e2 v2 h3),
      eval_exp h0 frm (E s t (LetPar lb e2)) v2 h3
| eval_letpar_b1 :
    forall
      frm h0 h1 h2 lb ds es e2 s t ff sf q
      (UNZIP : unzipb lb = (ds,es))
      (SF: scopeofFrame h1 frm sf)
      (NF: initDefault h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
      (ABORT1: fill_slots_par h1 frm ff ds es (AbortAV q) h2),
      eval_exp h0 frm (E s t (LetPar lb e2)) (AbortV q) h2
(* remaining bad case is in tail position *)
| eval_letseq_ :
    forall
      frm h0 h1 h2 lb ds es e2 v2 s t fi
      (UNZIP: unzipb lb = (ds, es))
      (* Returns the innermost frame: *)
      (EVAL1: fill_slots_seq h0 frm ds es (FrameAV fi) h1)
      (EVAL2: eval_exp h1 fi e2 v2 h2),
      eval_exp h0 frm (E s t (LetSeq lb e2)) v2 h2
| eval_letseq_b1 :
    forall
      frm h0 h1 lb ds es e2 s t q
      (UNZIP: unzipb lb = (ds, es))
      (* Returns the innermost frame: *)
      (ABORT1 : fill_slots_seq h0 frm ds es (AbortAV q) h1),
      eval_exp h0 frm (E s t (LetSeq lb e2)) (AbortV q) h1
(* remaining bad case is in tail position *)
| eval_letrec_ :
    forall
      frm h0 h1 h2 h3 lvb ds evs e2 v2 ff sf s t
      (UNZIP: unzipb lvb = (ds,evs))
      (SF: scopeofFrame h1 frm sf)
      (NF: initDefault h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
      (EVAL1: fill_slots_rec h1 ff ds evs UnitAV h2)
      (EVAL2: eval_exp h2 ff e2 v2 h3),
      eval_exp h0 frm (E s t (LetRec lvb e2)) v2 h3
| eval_letrec_b1 :
    forall
      frm h0 h1 h2 lb ds es e2 s t ff sf q
      (UNZIP: unzipb lb = (ds,es))
      (SF: scopeofFrame h1 frm sf)
      (NF: initDefault h0 (expScope e2) [(P, [(sf, frm)])] ff h1)
      (ABORT1: fill_slots_rec h1 ff ds es (AbortAV q) h2),
      eval_exp h0 frm (E s t (LetRec lb e2)) (AbortV q) h2
(* remaining bad case is in tail position *)
| eval_asgn_ :
    forall
      h0 frm s t lhs e h1 h2 ff d v h3
      (EVLHS: eval_lhs h0 frm lhs (AddrAV (Addr_ ff d)) h1)
      (EVAL: eval_exp h1 frm e v h2)
      (SET: setSlot h2 ff d v h3),
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
      (SET: forall h3, ~ setSlot h2 ff d v h3),
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
      frm r h0 h1 rf s t s0 p s' d'
      (RLOOK: rlookup r p s' d')
      (ASC: assocScope d' s0)
      (RECF: initDefault h0 s0 [] rf h1),
      eval_exp h0 frm (E s t (New r)) (RecordV rf) h1
| eval_new_b1 :
    forall
      frm r h0 s t
      (RLOOK: forall p s' d' s0, ~ (rlookup r p s' d' /\ assocScope d' s0)),
      eval_exp h0 frm (E s t (New r)) (AbortV Wrong) h0

with eval_lhs : H -> FrameId -> lhs -> AuxV -> H -> Prop :=
| eval_lhs_var_ :
    forall
      h frm r a
      (ADDR: getAddr h frm r a),
      eval_lhs h frm (Var r) (AddrAV a) h
| eval_lhs_var_b :
    forall
      h frm r
      (ADDR: forall a, ~ getAddr h frm r a),
      eval_lhs h frm (Var r) (AbortAV Wrong) h
| eval_lhs_field :
    forall
      h0 frm e r s rf scf h1 h2 a sf
      (EVAL: eval_exp h0 frm e (RecordV rf) h1)
      (SF: scopeofFrame h1 rf sf)
      (SCF: initDefault h1 s [(I, [(sf, rf)])] scf h2)
      (SCR: scopeofRefP r s)
      (ADDR: getAddr h2 scf r a),
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
            | RecordV _ => False
            | NullV => False
            | _ => True
            end),
      eval_lhs h0 frm (Field e r) (aborta v) h1
| eval_lhs_field_b2:
    forall
      h0 frm e r s rf scf h1 h2 sf
      (EVAL: eval_exp h0 frm e (RecordV rf) h1)
      (SCR: scopeofRefP r s)
      (SF: scopeofFrame h1 rf sf)
      (SCF: initDefault h1 s [(I, [(sf, rf)])] scf h2)
      (ADDR: forall a, ~ getAddr h2 scf r a),
      eval_lhs h0 frm (Field e r) (AbortAV Wrong) h2

with fill_slots_par : H -> FrameId -> FrameId -> list D -> list exp -> AuxV -> H -> Prop :=
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
      (SS: setSlot h1 fc d v h2)
      (TAIL: fill_slots_par h2 frm fc ds es v1 h3),
      fill_slots_par h0 frm fc (d::ds) (e::es) v1 h3
| fill_par_cons_b1 :
    forall
      h0 frm e es d ds fc h1 q
      (EVAL: eval_exp h0 frm e (AbortV q) h1),
      fill_slots_par h0 frm fc (d :: ds) (e :: es) (AbortAV q) h1
| fill_par_cons_b2 :
    forall
      h0 frm e d es ds fc v h1
      (EVAL: eval_exp h0 frm e v h1)
      (GOOD: good v)
      (SS: forall h2, ~ setSlot h1 fc d v h2),
      fill_slots_par h0 frm fc (d::ds) (e::es) (AbortAV Wrong) h1
(* other bad case is in tail position*)

with fill_slots_seq : H -> FrameId -> list D -> list exp -> AuxV -> H -> Prop :=

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
      (SD: scopeofDecl d = Some sd)
      (SF: scopeofFrame h0 frm sf)
      (NF: initDefault h0 sd [(P, [(sf, frm)])] fc h1)
      (EVAL: eval_exp h1 frm e v h2)   (* APT: could/should this come before the NF creation? *)
      (GOOD: good v)
      (SS: setSlot h2 fc d v h3)
      (TAIL: fill_slots_seq h3 fc ds es v1 h4),
      fill_slots_seq h0 frm (d :: ds) (e :: es) v1 h4
| fill_seq_cons_b1 :
    forall
      h0 frm e es d ds h1 sd fc h2 q sf
      (SD: scopeofDecl d = Some sd)
      (SF: scopeofFrame h0 frm sf)
      (NF: initDefault h0 sd [(P, [(sf, frm)])] fc h1)
      (EVAL: eval_exp h1 frm e (AbortV q) h2),
      fill_slots_seq h0 frm (d :: ds) (e :: es) (AbortAV q) h2
| fill_seq_cons_b2 :
    forall
      h0 frm e es d ds fc v h1 h2 sd sf
      (SD: scopeofDecl d = Some sd)
      (SF: scopeofFrame h0 frm sf)
      (NF: initDefault h0 sd [(P, [(sf, frm)])] fc h1)
      (EVAL: eval_exp h1 frm e v h2)   (* APT: could/should this come before the NF creation? *)
      (GOOD: good v)
      (SS: forall h3, ~ setSlot h2 fc d v h3),
      fill_slots_seq h0 frm  (d :: ds) (e :: es) (AbortAV Wrong) h2
(* other bad case is in tail position *)

with fill_slots_rec : H -> FrameId -> list D -> list exp -> AuxV -> H -> Prop :=

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
      (SS: setSlot h1 frm d v h2)
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
      (SS: forall h2, ~ setSlot h1 frm d v h2),
      fill_slots_rec h0 frm (d::ds) (e::es) v1 h1
(* other bad case is in tail position *)
.

(** Combined induction scheme, used for mutual induction. See also:
https://coq.inria.fr/cocorico/Mutual%20Induction *)
Scheme eval_exp_ind2 := Minimality for eval_exp Sort Prop
with fill_par_ind2 := Minimality for fill_slots_par Sort Prop
with fill_seq_ind2 := Minimality for fill_slots_seq Sort Prop
with fill_rec_ind2 := Minimality for fill_slots_rec Sort Prop
with eval_lhs_ind2 := Minimality for eval_lhs Sort Prop.
Combined Scheme eval_exp_ind3
         from eval_exp_ind2, fill_par_ind2, fill_seq_ind2, fill_rec_ind2, eval_lhs_ind2.

Inductive eval_prog : prog -> V -> Prop :=
| eval_prog_ : forall
    e v f h0 h1 rds
    (* empty root frame *)
    (TOPFRM: initDefault (emptyHeap) (expScope e) [] f h0)
    (EVALB: eval_exp h0 f e v h1),
    eval_prog (Prog rds e) v
.

End DynamicSemantics.
