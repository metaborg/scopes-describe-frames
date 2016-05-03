Require Import L2.GCsemantics prop_fold.

(** Type soundness for [GCsemantics.v]. The main difference is that we must keep track
    of the auxiliary root set properly. *)

Instance FH : @FrameHeap V := {}.

Section TypeSoundness.

Context `{G: Graph (@AT T)} `{DVT: DefaultVTyp T V} .

(** * Value typing *)

Inductive vtyp' (h: H) : V -> T -> Prop :=
| vtyp'_n : forall z, vtyp' h (NumV z) Tint
| vtyp'_b : forall b, vtyp' h (BoolV b) Tbool
| vtyp'_f :
    forall
      ds e f tas tr sp
      (FS: scopeofFrame h f sp)
      (WT: wt_exp (E sp (Tarrow tas tr) (Fn ds e)))
      (WB: wb_exp (E sp (Tarrow tas tr) (Fn ds e))),
      vtyp' h (ClosV ds e f) (Tarrow tas tr)
| vtyp'_df :
    forall
      ts t v
      (VT: vtyp' h v t),
      vtyp' h (DefFunV v) (Tarrow ts t)
| vtyp'_r :
    forall
      f d s
      (SF: scopeofFrame h f s)
      (ASC: assocScope d s),
      vtyp' h (RecordV f) (Trecord d)

(** [NullV] values are typed by records: *)
| vtyp'_nr : forall d, vtyp' h NullV (Trecord d)

(** Trying to access a null value as a record raises a [NullPointer]
exception, which is allowed in any context: *)
| vtyp'_q : forall t, vtyp' h (AbortV NullPointer) t
.

Hint Constructors vtyp' : sgraph.

Lemma setSlot_vtyp' :
  forall
    h0 f d v h1 v0 t0
    (SET: setSlot h0 f d v h1)
    (VT': vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv SET; induction VT'; sgauto.
  - econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
    rewrite H1 in H0; inv H0. econstructor; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H1 in H0; inv H0; eauto.
    econstructor. rewrite get_set_other; eauto.
Qed.

Lemma newFrame_vtyp' :
  forall
    h0 s f h1 ks v0 t0
    (NF: newFrame h0 s ks f h1)
    (VT': vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv NF; induction VT'; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - apply keys_in in H0; contradiction.
  - econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst. apply keys_in in H0. contradiction.
    econstructor. rewrite get_set_other; eauto.
Qed.

Lemma fillFrame_vtyp' :
  forall
    slots f h1 h2 v0 t0
    (FF: fillFrame f h1 slots h2)
    (VT': vtyp' h1 v0 t0),
    vtyp' h2 v0 t0.
Proof.
  intros; destruct FF as [? [? [? [? ?]]]]; subst; induction VT'; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - rewrite H in H0; inv H0. econstructor; rewrite get_set_same; eauto.
  - econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H0 in H; inv H; eauto.
    econstructor. rewrite get_set_other; eauto.
Qed.

Hint Resolve setSlot_vtyp' : sgraph.
Hint Resolve newFrame_vtyp' : sgraph.
Hint Resolve fillFrame_vtyp' : sgraph.

(** * Default Values *)

Inductive default : T -> V -> Prop :=
| def_n : default Tint (NumV 0)
| def_b : default Tbool (BoolV false)
| def_df : forall ts t v,
    default t v ->
    default (Tarrow ts t) (DefFunV v)
| def_r : forall d, default (Trecord d) NullV
.

Hint Constructors default : sgraph.

Lemma default_vtyp' :
  forall
    v t,
    default t v ->
    forall h,
      vtyp' h v t.
Proof.
  induction 1; intros; sgauto.
Qed.

Instance VT' : VTyp.
Proof.
  econstructor.
  apply setSlot_vtyp'.
  apply newFrame_vtyp'.
  apply fillFrame_vtyp'.
Defined.

Instance DVT' : DefaultVTyp.
Proof.
  econstructor.
  instantiate (1:=default).
  apply default_vtyp'.
Qed.

(** * Auxiliary Lemmas *)

(** Must show that removing unreferenced frames preserves value typing: *)
Lemma removeFrames_vtyp:
  forall
    h1 fs h2 v0 t0
    (RF: removeFrames h1 fs h2)
    (NR: forall f, vrefers v0 f -> ~ In f fs)
    (VT: vtyp h1 v0 t0),
    vtyp h2 v0 t0.
Proof.
  intros. induction RF. auto.
  apply IHRF.  intros. intro. eapply NR; eauto.  right;auto.
  clear IHRF RF.
  induction VT0; try constructor.

  intros. econstructor; eauto.
  eapply removeFrameScope; eauto.  split; auto.
  intro. subst.  eapply NR.  eapply vr_clos; eauto. left; auto.

  eapply IHVT0.  intros.  apply NR. eapply vr_deffun; eauto.

  econstructor; eauto.
  eapply removeFrameScope; eauto.  split; auto.
  intro. subst. eapply NR. eapply vr_record. eauto. left; auto.
Qed.

Instance VTR : VTypRefers := { removeFrames_vtyp := removeFrames_vtyp }.

(* A Hint database for list membership operations. *)
Hint Resolve in_eq : ins.
Hint Resolve in_cons : ins.

Lemma in_2 : forall {A:Type} (x1 x2 y: A) (xs:list A), In y (x1::xs) -> In y (x1::x2::xs).
Proof.
  intros. inv H; eauto with ins.
Qed.

Hint Resolve in_2 : ins.


Lemma eval_exp_scopeofFrame_aux :
  (forall h0 f0 roots e v h1,
      eval_exp h0 f0 roots e v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        In f (f0::roots) ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 roots e v h1,
      eval_lhs h0 f0 roots e v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        In f (f0::roots) ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 roots f1 ds es v h1,
      fill_slots_par h0 f0 roots f1 ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        In f (f0::roots) ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 roots ds es v h1,
      fill_slots_seq h0 f0 roots ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        In f (f0::roots) ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 roots ds es v h1,
      fill_slots_rec h0 f0 roots ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        In f (f0::roots) ->
        scopeofFrame h1 f s).
Proof.
  apply eval_exp_ind3; [| (eauto 7 using initDefaultDiff_scopeofFrame, setSlotScope with ins)  ..].
  intros. inv H. eapply H2; eauto. eapply removeFramesScope; intuition eauto.
Qed.

Definition eval_exp_scopeofFrame     := proj1 eval_exp_scopeofFrame_aux.
Definition eval_lhs_scopeofFrame     := proj1 (proj2 eval_exp_scopeofFrame_aux).
Definition fill_par_scopeofFrame     := proj1 (proj2 (proj2 eval_exp_scopeofFrame_aux)).
Definition fill_seq_scopeofFrame     := proj1 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).
Definition fill_rec_scopeofFrame     := proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).

Hint Resolve eval_exp_scopeofFrame : sgraph.
Hint Resolve eval_lhs_scopeofFrame : sgraph.
Hint Resolve fill_par_scopeofFrame : sgraph.
Hint Resolve fill_seq_scopeofFrame : sgraph.
Hint Resolve fill_rec_scopeofFrame : sgraph.
Hint Unfold abort : sgraph.
Hint Constructors vtyp' : sgraph.


(** Predicate stating that a set of root frames are in the heap: *)
Definition good_roots (h: H) (fs: list FrameId) : Prop := (forall f, In f fs -> frame h f).

(** Preservation facts about good roots: *)

Lemma removeFrame_good_roots: forall h0 fs h1 f,
    removeFrame h0 f h1 ->
    good_roots h0 fs ->
    ~In f fs ->
    good_roots h1 fs.
Proof.
  unfold good_roots; intros.
  eapply removeFrameFrames; eauto.
  intuition (try subst; auto).
Qed.

Lemma removeFrames_good_roots : forall h0 rs h1 fs,
    removeFrames h0 fs h1 ->
    good_roots h0 rs ->
    (forall f, In f fs -> ~ In f rs) ->
    good_roots h1 rs.
Proof.
  intros. induction H.  auto.
  eauto 7 using removeFrame_good_roots with ins.
Qed.

Lemma initDefault_good_roots: forall h0 fs h1 ks s f,
    initDefault h0 s ks f h1 ->
    good_roots h0 fs ->
    good_roots h1 (f::fs).
Proof.
  unfold good_roots; intros.
  eapply initDefaultFrames; eauto.  inv H1. left; auto. right; eauto.
Qed.

Lemma setSlot_good_roots: forall h0 fs f d v h1,
    setSlot h0 f d v h1 ->
    good_roots h0 fs ->
    good_roots h1 fs.
Proof.
  unfold good_roots; intros.
  erewrite <- setSlotFrames; eauto.
Qed.


(** Some silly utility lemmas to improve automation *)

Lemma good_roots_swap:
  forall h f1 f2 r,
    good_roots h (f1::f2::r) ->
    good_roots h (f2::f1::r).
Proof.
  unfold good_roots; intros.
  apply H. inv H0.  right;left;auto.
  inv H1. left; auto. right; right; auto.
Qed.

Lemma good_roots_drop:
  forall h f r,
    good_roots h (f::r) ->
    good_roots h r.
Proof.
  unfold good_roots; intros.
  apply H.  right; auto.
Qed.


Lemma good_roots_drop2:
  forall h f1 f2 r,
    good_roots h (f1::f2::r) ->
    good_roots h (f2::r).
Proof.
  unfold good_roots; intros.
  apply H. inv H0.  right;left;auto. right;right;auto.
Qed.

Lemma good_roots_decomp:
  forall h f r,
    frame h f ->
    good_roots h r ->
    good_roots h (f::r).
Proof.
  unfold good_roots; intros.
  inv H1. auto.
  apply H0; auto.
Qed.

(** * Type Preservation *)

(* An alternative, more selective hint database for this proof. *)
Hint Constructors vtyp' : pres.
Hint Constructors wb_exp wt_exp : pres.
Hint Resolve eval_exp_scopeofFrame : pres.
Hint Resolve fill_par_scopeofFrame : pres.
Hint Resolve fill_seq_scopeofFrame : pres.
Hint Resolve fill_rec_scopeofFrame : pres.
Hint Resolve eval_lhs_scopeofFrame : pres.
Hint Resolve initDefault_good_roots : pres.
Hint Resolve initDefaultDiff_scopeofFrame : pres.
Hint Resolve initDefaultSame_scopeofFrame : pres.
Hint Resolve initDefault_good_heap1 : pres.
Hint Resolve initDefault_good_heap0 : pres.
Hint Resolve setSlot_good_roots : pres.
Hint Resolve setSlot_good_heap : pres.
Hint Resolve setSlot_vtyp' : pres.
Hint Resolve setSlotScope : pres.
Hint Resolve scopeofFrameFrame : pres.
Hint Resolve good_roots_swap : pres.
Hint Resolve good_roots_drop : pres.
Hint Resolve good_roots_drop2 : pres.
Hint Resolve good_roots_decomp : pres.

Ltac peauto := eauto with pres ins.

(** Compared to proof for standard semantics, this one must maintain the [good_roots]
    property. *)

Lemma exp_preservation:
  (forall
      h0 f roots e v h1
      (EVAL: eval_exp h0 f roots e v h1)
      s t pe
      (UNPACK: e = (E s t pe))
      (FS: scopeofFrame h0 f s)
      (GR: good_roots h0 (f::roots))
      (GH: good_heap h0)
      (WT: wt_exp (E s t pe))
      (WB: wb_exp (E s t pe)),
      (good_roots h1 (f::roots) /\ good_heap h1 /\ vtyp h1 v t))
  /\
  (forall
      h0 f roots lhs v h1
      (EVAL: eval_lhs h0 f roots lhs v h1)
      s t
      (FS: scopeofFrame h0 f s)
      (WB: wb_lhs s lhs)
      (WT: wt_lhs t lhs)
      (GR: good_roots h0 (f::roots))
      (GH: good_heap h0),
      good_roots h1 (f::roots) /\
      good_heap h1 /\ match v with
                      | AddrAV (Addr_ ff d) =>
                        exists s' ds,
                        scopeofFrame h1 ff s' /\
                        declsofScopeP s' ds /\
                        In d ds /\
                        typofDecl d t
                      | AbortAV NullPointer => True
                      | _ => False
                      end)
  /\
  (forall
      h0 f roots f1 ds e2s v h1
      (FSPAR: fill_slots_par h0 f roots f1 ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      (FCR: In f1 roots)   (* maybe better ways to handle this *)
      (GR: good_roots h0 (f::roots))
      s1
      (FS1: scopeofFrame h0 f1 s1)
      (GH: good_heap h0)
      ds0
      (DS0: declsofScopeP s1 ds0)
      (DS: forall d, In d ds -> In d ds0)
      t2s
      (TYPDECS: typofDecls ds t2s)
      (WB: forall e,
          In e e2s ->
          expScope e = s /\ wb_exp e)
      (WT: Forall2 (fun (e : exp) (t : T) => expType e = t /\ wt_exp e) e2s
                   t2s),
      good_roots h1 (f::roots) /\ good_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
  /\
  (forall
      h0 f roots ds e2s v h1
      (FSSEQ: fill_slots_seq h0 f roots ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      (GR: good_roots h0 (f::roots))
      (GH: good_heap h0)
      t2s
      (TYPDECS: typofDecls ds t2s)
      s'
      (WB1: ForallFold2 (fun d e ps newPs =>
                           (linksofScopeP newPs [(P, [ps])]) /\
                           declsofScopeP newPs [d] /\
                           (expScope e) = ps /\
                           wb_exp e)
                        ds e2s s s')
      (WT: Forall2 (fun (e : exp) (t : T) => expType e = t /\ wt_exp e) e2s
                   t2s),
      good_roots h1 (f::roots) /\
      good_heap h1 /\ ((exists f, v = FrameAV f /\ scopeofFrame h1 f s') \/
                       v = AbortAV NullPointer))
  /\
  (forall
      h0 f roots ds e2s v h1
      (FSREC: fill_slots_rec h0 f roots ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      (GR: good_roots h0 (f::roots))
      (GH: good_heap h0)
      ds0
      (DS0: declsofScopeP s ds0)
      (DS: forall d, In d ds -> In d ds0)
      t2s
      (TYPDEC: typofDecls ds t2s)
      (WB: forall e,
          In e e2s ->
          expScope e = s /\ wb_exp e)
      (WT: Forall2 (fun (e : exp) (t : T) =>
                      is_val e /\
                      match t with
                      | Tarrow _ _ => t = expType e
                      | _ => False
                      end /\
                      wt_exp e) e2s
                   t2s),
      good_roots h1 (f::roots) /\ good_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer)).
Proof.
  apply eval_exp_ind3; intros; [| (simpl; try (inv UNPACK; inv WT; inv WB); subst) ..].
  - (* GC case *)
    eapply H2; eauto.
    inv H. eapply removeFramesScope; eauto. intuition peauto.
    inv H. eapply removeFrames_good_roots; eauto.
    eapply good_heap_safeRemoval; eauto.
  - (* cnum *)
    peauto.
  - (* true *)
    peauto.
  - (* false *)
    peauto.
  - (* plus good case *)
    edestruct H as [? [? ?]]; eauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* plus bad case 1 *)
    edestruct H as [? [? VT1]]; eauto.
    intuition auto.
    inv VT1; simpl; eauto with ins pres.
    edestruct ABORTL; eauto.
  - (* plus bad case 2 *)
    edestruct H as [? [? ?]]; eauto.
    edestruct H0 as [? [? VT2]]; peauto.
    intuition auto.
    inv VT2; peauto.
    edestruct ABORTR; eauto.
  - (* gt good case *)
    edestruct H as [? [? ?]]; eauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* gt bad case 1 *)
    edestruct H as [? [? VT1]]; eauto.
    intuition auto.
    inv VT1; simpl; peauto.
    edestruct ABORTL; eauto.
  - (* gt bad case 2 *)
    edestruct H as [? [? ?]]; eauto.
    edestruct H0 as [? [? VT2]]; peauto.
    intuition auto.
    inv VT2; peauto.
    edestruct ABORTR; eauto.
  - (* lhs good case *)
    edestruct H as [? [GH1 [? [? [SF [DS [IN TD]]]]]]]; eauto.
    intuition auto.
    edestruct (GH1 ff) as [WB WT]; peauto.
    inv WT.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply declsofScopeDet in DS; eauto; subst.
    eapply WT1; eauto.
  - (* lhs bad case 1 *)
    edestruct H; eauto.
    destruct q; inv H1; intuition peauto.
  - (* lhs bad case 2 *)
    edestruct H as [? [GH1 [? [? [SF [DS [IN TD]]]]]]]; eauto.
    edestruct good_frame_getSlot with (f := ff) (h:=h1) as [v P]; peauto.
    exfalso; eapply GET; eauto.
  - (* fn *)
    split; peauto.
  - (* app good case *)
    edestruct H as [? [? VT']]; peauto. inv VT'. inv WT. inv WB. inv H5.
    eapply scopeofFrameDet in SF; eauto; subst.
    edestruct H0 as [? [? _]]; peauto.
    edestruct H1 as [? [? ?]]; peauto.
  - (* app dfun case *)
    edestruct H as [? [? VT']]; peauto. inv VT'. eauto.
  - (* app bad case 1 *)
    edestruct H as [? [? VT']]; peauto.
    inv VT'; simpl; peauto; contradiction.
  - (* app bad case 2 *)
    edestruct H as [? [? VT']]; peauto. inv VT'. inv WT. inv WB. inv H4.
    eapply scopeofFrameDet in SF; eauto; subst.
    edestruct H0 as [? [? [X|X]]]; peauto; inv X.
    peauto.
  - (* letpar good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s1) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [? _]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* letpar bad case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s1) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [? [X|X]]]; peauto; inv X.
    peauto.
  - (* letseq good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    edestruct H as [? [? [[ff [FEQ SF]]|X]]]; peauto; [inv FEQ|inv X].
    edestruct H0 as [? [? ?]]; peauto.
  - (* letseq bad case 1 *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    edestruct H as [? [? [[? [FEQ SF]]|X]]]; peauto; [inv FEQ|inv X].
    peauto.
  - (* letrec good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s0) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [? _]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* letrec bad case 1 *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s0) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [? [X|X]]]; peauto; inv X.
    peauto.
  - (* asgn good case *)
    edestruct H as [? [? [? [? [SF [DS [IN TD]]]]]]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
    intuition peauto.
  - (* asgn bad case 1 *)
    edestruct H as [? [? X]]; peauto. destruct q; inv X; peauto.
  - (* asgn bad case 2 *)
    edestruct H as [? [? [? [? [SF [DS [IN TD]]]]]]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* asgn bad case 3 *)
    edestruct H as [? [? [? [? [SF [DS [IN [TD GF]]]]]]]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
    exfalso.
    edestruct good_frame_setSlot with (f:= ff) (h:= h2) as [h' P]; peauto.
    eapply SET; eauto.
  - (* if good case t *) subst.
                         edestruct H as [? [? ?]]; peauto.
  - (* if good case f *) subst.
                         edestruct H as [? [? ?]]; peauto.
  - (* if bad case *) subst.
                      edestruct H as [? [? VT']]; peauto.
                      destruct v1; inv VT'; peauto.
                      edestruct ABORT1; eauto.
  - (* seq good case *)
    edestruct H as [? [? ?]]; peauto.
  - (* seq bad case 1 *)
    edestruct H as [? [? VT']]; peauto.
    inv VT'; peauto.
  - (* new good case *)
    eapply rlookupDet in RLOOK; eauto. destruct RLOOK as [? [? ?]]; subst.
    eapply rlookupDet in RL; eauto. destruct RL as [? [? ?]]; subst.
    eapply assocScopeDet in ASC; eauto; subst.
    intuition peauto.
  - (* new bad case 1 *)
    edestruct RLOOK; peauto.
  - (* eval_lhs var good case *)
    inv WB; inv WT. split; auto.
    eapply scopeofRefDet in SR; eauto; subst.
    edestruct good_addr as [? [ADDR' [SF' [? [DS IN]]]]]; eauto.
    eapply getAddrDet in ADDR; eauto; subst.
    eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
    eauto 7.
  - (* eval_lhs var bad case *)
    inv WB; inv WT.
    eapply scopeofRefDet in SR; eauto; subst.
    edestruct good_addr as [? [? ?]]; peauto; peauto.
    intuition eauto.
  - (* eval_lhs field good case *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? VT']]; peauto.
    eapply scopeofRefDet in SCR; eauto; subst.
    eapply linksofScopeDet in LS; eauto; inv LS.
    inv VT'.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply assocScopeDet in ASC; eauto; subst.
    assert (good_heap h2) by peauto.
    edestruct good_addr as [? [ADDR' [SF' [? [DS IN]]]]]; peauto.
    eapply getAddrDet in ADDR; eauto; inv ADDR.
    intuition peauto; eauto 7.
  - (* eval_lhs field good null case *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? ?]]; peauto.
  - (* eval_lhs field bad case 1 *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? ?]]; peauto.
    destruct v; inv BAD;  inv H2; simpl; eauto.
  - (* eval_lhs field bad case 2 *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? VT']]; peauto.
    eapply scopeofRefDet in SCR; eauto; subst.
    eapply linksofScopeDet in LS; eauto; inv LS.
    inv VT'.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply assocScopeDet in ASC; eauto; subst.
    assert (good_heap h2) by peauto.
    edestruct good_addr as [? [ADDR' [SF' [? [DS IN]]]]]; peauto.
    intuition; eauto; peauto.
  - (* fill_par good case *)
    peauto.
  - (* fill_par nil bad case 1 *)
    inv WT. inv TYPDECS. intuition.
  - (* fill_par nil bad case 2 *)
    inv TYPDECS. inv WT. intuition.
  - (* fill_par cons good case *)
    inv WT. destruct H3. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? ?]];  peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* fill_par cons bad case 1 *)
    inv WT. destruct H2. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? VT']]; peauto.
    destruct q; inv VT'; auto.
  - (* fill_par cons bad case 2 *)
    inv WT. destruct H2. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? ?]]; peauto.
    exfalso.
    edestruct good_frame_setSlot with (h:=h1) (f:=fc) as [h' SS']; peauto.
    eapply SS; eauto.
  - (* fill_seq nil good case *)
    inv WB1. intuition eauto.
  - (* fill_seq nil bad case 1 *)
    inv WB1. intuition.
  - (* fill_seq nil bad case 2 *)
    inv WB1. intuition.
  - (* fill_seq cons good case *)
    inv WB1. destruct REL as [LKS [DD [ESEQ WB]]]. subst.
    inv WT. destruct H3; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DD; peauto; rewrite DD in SD; inv SD; auto); subst.
    edestruct H as [? [? ?]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* fill_seq cons bad case 1 *)
    inv WB1. destruct REL as [LKS [DD [ESEQ WB]]]. subst.
    inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DD; peauto; rewrite DD in SD; inv SD; auto); subst.
    edestruct H as [? [? VT']]; peauto.
    destruct q; inv VT'; peauto.
    intuition peauto.
  - (* fill_seq cons bad case 2 *)
    inv WB1. destruct REL as [LKS [DD [ESEQ WB]]]. subst.
    inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DD; peauto; rewrite DD in SD; inv SD; auto); subst.
    edestruct H as [? [? ?]]; peauto.
    exfalso.
    edestruct good_frame_setSlot with (h:=h2) (f:=fc) as [h' SS']; peauto.
    eapply SS; eauto.
  - (* fill_rec nil good case *)
    intuition eauto.
  - (* fill_rec nil bad case 1 *)
    inv WT. inv TYPDEC. intuition.
  - (* fill_rec nil bad case 2 *)
    inv TYPDEC. inv WT. intuition.
  - (* fill_rec cons good case *)
    inv WT. destruct H3 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    destruct y; inv ISFUN. simpl in *; subst.
    edestruct H as [? [? ?]]; peauto.
    edestruct H0 as [? [? ?]]; peauto.
  - (* fill_rec cons bad case 1 *)
    inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    destruct y; inv ISFUN. simpl in *; subst.
    edestruct H as [? [? VT']]; peauto.
    destruct q; inv VT'; eauto.
  - (* fill_rec cons bad case 2 *)
    inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    destruct y; inv ISFUN. simpl in *; subst.
    edestruct H as [? [? ?]]; peauto.
    exfalso.
    edestruct good_frame_setSlot with (f:=frm) (h:=h1) as [f' SS']; peauto.
    eapply SS; eauto.
Qed.

Lemma prog_sound :
  forall
    p v
    (WT: wt_prog p)
    (WB: wb_prog p)
    (EVAL: eval_prog p v),
    ~ v = AbortV Wrong.
Proof.
  intros. inv EVAL.
  inv WT. simpl in TOPFRM.
  inv WB.
  assert (scopeofFrame h0 f s) by peauto.
  assert (good_heap emptyHeap) by inversion 1.
  assert (good_heap h0) by peauto.
  destruct exp_preservation as [expP _].
  edestruct expP as [_ VT0]; peauto.
  eapply initDefault_good_roots; eauto.
  unfold good_roots. inversion 1.
  intro; subst. destruct VT0 as [_ VT0]. inv VT0.
Qed.

End TypeSoundness.
