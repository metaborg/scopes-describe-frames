Require Import maps scopes frames.

(** * Frames with Subtyping *)

(** A subtyping relation is reflexive and transitive.  We will
   instantiate the relation appropriately for each language using
   subtyping (e.g. L3 in the paper). *)

Class SubTyping {T: Type} :=
  { sub : T -> T -> Prop ;
    sub_refl : forall t, sub t t ;
    sub_trans : forall t1 t2 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3 ;
  }.

(** The rest of the definitions in this file are based on a
straightforward adaptation (summarized in Fig. 30 in the paper) of the
[well_typed] property in [frames.v] to incorporate subtyping. The
notion of well-boundness remains the same, and the key lemmas about
good heaps and frames are straightforwardly extended, largely by
cut-and-paste.  A few additional lemmas needed for the L3 proof appear
only in this version.

It would be possible to avoid all this duplicated code by building
subtyping into the basic definitions in [frames.v], and instantiating
the subtype relation to type equality, but we chose to leave the basic
framework a little simpler to match the paper.  *)

Section TV.
  Context {T V: Type} `{VT: VTyp T} {ST: @SubTyping T}.

  Inductive well_sub_typed  (h: H) (f: FrameId) : Prop :=
  | well_typed_ :
      forall
        s
        (SC: scopeofFrame h f s)
        ds
        (DS: declsofScopeP s ds)
        (WT: forall d t v,
            In d ds ->
            typofDecl d t ->
            getSlot h f d v ->
            exists t', vtyp h v t' /\ sub t' t),
        well_sub_typed h f.

  Definition good_sub_frame h f := well_bound h f /\ well_sub_typed h f.
  Definition good_sub_heap h := forall f, frame h f -> good_sub_frame h f.

End TV.

Hint Constructors well_sub_typed : sgraph.

Lemma good_frame2good_sub_frame :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f
    (GF: good_frame h f),
    good_sub_frame h f.
Proof.
  inversion 1; subst; econstructor; eauto.
  inv H0; econstructor; eauto using sub_refl.
Qed.

Hint Resolve good_frame2good_sub_frame : sgraph.

Lemma good_heap2good_sub_heap :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h
    (GH: good_heap h),
    good_sub_heap h.
Proof.
  intros. intro; intros. eapply GH in H. sgauto.
Qed.

Hint Resolve good_heap2good_sub_heap : sgraph.

Lemma setSlot_well_typed_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 f d v h1 t
    (SET: setSlot h0 f d v h1)
    (TD: typofDecl d t)
    (WT: well_sub_typed h0 f)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    well_sub_typed h1 f.
Proof.
  intros; inv WT; sgauto.
  inversion SET; subst. inversion SC. rewrite H1 in H0; inv H0.
  econstructor; eauto.
  - econstructor; eauto. rewrite get_set_same; eauto.
  - intros. inv H3. rewrite get_set_same in H4. inv H4.
    destruct (Ddec d0 d); subst.
    + rewrite get_set_same in H5; inv H5.
      eapply typofDeclDet in TD; eauto; subst.
      eexists; split; eauto using setSlot_vtyp.
    + rewrite get_set_other in H5; eauto.
      eapply WT0 in H0; sgauto.
      destruct H0 as [? [VT'' SUB']].
      eexists; split; eauto using setSlot_vtyp.
Qed.

Hint Resolve setSlot_well_typed_sub : sgraph.

Lemma setSlot_other_well_sub_typed :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 f d v h1 t f0
    (SET: setSlot h0 f d v h1)
    (TD: typofDecl d t)
    (WT: well_sub_typed h0 f0)
    (DIFF: f <> f0)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    well_sub_typed h1 f0.
Proof.
  intros; inv WT. inv SC; inv SET.
  econstructor; eauto.
  - econstructor; rewrite get_set_other; eauto.
  - intros. inv H4. rewrite get_set_other in H5; eauto. rewrite H5 in H; inv H.
    eapply WT0 in H2; sgauto. destruct H2 as [? [VT'' SUB']].
    eexists; split; sgauto.
    eapply setSlot_vtyp; eauto. econstructor; eauto.
Qed.

Hint Resolve setSlot_other_well_sub_typed : sgraph.

Lemma setSlot_other_good_sub_frame :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 f d v h1 t f0
    (SET: setSlot h0 f d v h1)
    (TD: typofDecl d t)
    (WT: good_sub_frame h0 f0)
    (DIFF: f <> f0)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    good_sub_frame h1 f0.
Proof.
  intros; inv WT; sgauto.
  split; eauto using setSlot_other_well_sub_typed, setSlot_other_well_bound.
Qed.

Lemma setSlot_good_sub_frame :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 f d v h1 t
    (SET: setSlot h0 f d v h1)
    (TD: typofDecl d t)
    (WT: good_sub_frame h0 f)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    good_sub_frame h1 f.
Proof.
  intros. inv WT.
  split; eauto using setSlot_well_typed_sub, setSlot_well_bound.
Qed.

Hint Resolve setSlot_good_sub_frame : sgraph.

Lemma setSlot_good_heap_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 f d v h1 t
    (SET: setSlot h0 f d v h1)
    (TD: typofDecl d t)
    (WT: good_sub_heap h0)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    good_sub_heap h1.
Proof.
  intros. intro. intro. destruct (FrameIdDec f f0); subst.
  - eapply setSlot_good_sub_frame; eauto. eapply WT. unfold frame. inv SET; eapply keys_in; eauto.
  - eapply setSlot_other_good_sub_frame; eauto. eapply WT.
    inv SET. unfold frame in H. eapply in_keys in H.
    rewrite get_set_other in H; auto.
    destruct H. eapply keys_in; eauto.
Qed.

Hint Resolve setSlot_good_heap_sub : sgraph.

Lemma initFrame_well_typed_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 s ks slots f h1
    (INIT: initFrame h0 s ks slots f h1)
    (TDs: declsofScopeP s (keys slots))
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl d t ->
        get Ddec slots d = Some v -> exists t', vtyp h0 v t' /\ sub t' t),
    well_sub_typed h1 f.
Proof.
  intros; inversion INIT. inv NF. assert (FF':=FF).
  eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
  eexists; sgauto.
  intros. eapply declsofScopeDet in TDs; eauto; subst.
  inv H2. rewrite H3 in FF; inv FF.
  eapply TYP in H0; eauto. destruct H0 as [? [VT' SUB']].
  eexists; split; sgauto. eapply initFrame_vtyp; eauto.
Qed.

Hint Resolve initFrame_well_typed_sub : sgraph.

Lemma initFrame_good_frame_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 s ks slots f h1
    (INIT: initFrame h0 s ks slots f h1)
    (TDs: declsofScopeP s (keys slots))
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl d t ->
        get Ddec slots d = Some v -> exists t', vtyp h0 v t' /\ sub t' t)
    (LNS: forall l ss,
        llinksofScopeP s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP s l (keys m)),
    good_sub_frame h1 f.
Proof.
  intros; split; eauto using initFrame_well_bound, initFrame_well_typed_sub.
Qed.

Hint Resolve initFrame_good_frame_sub : sgraph.

Lemma initFrame_other_well_typed_sub :
  forall
    T `{ST: SubTyping T} `{VT : VTyp T} h0 s ks slots f h1
    (INIT: initFrame h0 s ks slots f h1)
    slots
    (TDs: declsofScopeP s (@keys D V slots))
    f'
    (WT: well_sub_typed h0 f'),
    well_sub_typed h1 f'.
Proof.
  intros. inversion INIT; subst.
  assert (NF':=NF); eapply newFrameSame in NF'.
  assert (FF':=FF); eapply fillFrameSame in FF; eauto. inv FF.
  inversion NF; subst. rewrite get_set_same in NF'. inv NF'. inv WT. inv SC.
  assert (f' <> f). intro. subst. apply H. eapply keys_in; eauto.
  assert (FF'':=FF').
  eapply fillFrameDiff in FF'; eauto. Focus 2.
  apply get_set_other with (Kdec:=FrameIdDec) (m:=h0) (v:=(s, ks, empty)) in H2.
  rewrite H2. eauto.
  econstructor; sgauto. intros.
  assert (FF''':=FF''). destruct FF''' as [? [? [? [? ?]]]]; subst.
  inv H5. rewrite H7 in FF'; inv FF'.
  edestruct WT0; eauto; eauto. econstructor; eauto.
  destruct H5.
  eapply fillFrame_vtyp in FF''; eauto.
  eapply newFrame_vtyp in NF; eauto.
Qed.

Hint Resolve initFrame_other_well_typed_sub : sgraph.

Lemma initFrame_other_good_frame_sub :
  forall
    T `{ST: SubTyping T} `{VT : VTyp T} h0 s ks slots f h1
    (INIT: initFrame h0 s ks slots f h1)
    (TDs: declsofScopeP s (keys slots))
    f'
    (GF: good_sub_frame h0 f'),
    good_sub_frame h1 f'.
Proof.
  intros; inv GF; sgauto.
  split; eauto using initFrame_other_well_typed_sub, initFrame_other_well_bound.
Qed.

Lemma initFrame_good_heap_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h0 s ks slots f h1
    (GH: good_sub_heap h0)
    (INIT: initFrame h0 s ks slots f h1)
    (TDs: declsofScopeP s (keys slots))
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl d t ->
        get Ddec slots d = Some v -> exists t', vtyp h0 v t' /\ sub t' t)
    (LNS: forall l ss,
        llinksofScopeP s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP s l (keys m)),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros.
  pose proof (initFrameFrames _ _ _ _ _ _ INIT f0). destruct H0.
  apply H1 in H. destruct H. subst. sgauto.
  eapply initFrame_other_good_frame_sub in INIT; sgauto.
Qed.

Lemma getAddr_scopeofFrame_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f r ff d
    (GH: good_sub_heap h)
    (FH: frame h f)
    (ADDR: getAddr h f r (Addr_ ff d)),
    exists sf, scopeofFrame h ff sf.
Proof.
  inversion 3; subst. clear PATH ADDR.
  induction LK; eauto.
  - unfold frame in FH. eapply in_keys in FH. destruct FH. destruct x. destruct p.
    eexists; try econstructor; eauto.
  - generalize (GH _ FH); intro GF. inv GF. inv H.
    specialize (LNF _ _ IMS).
    specialize (LNS _ _ LNF).
    destruct LNS as [? [LLF [KS WBL]]].
    eapply llinksofFrameDet in IMS; eauto; subst.
    assert (S':=S).
    apply keys_in in S. specialize (WBL _ S).
    destruct WBL as [? [SCF' SFF']].
    apply scopeofFrameFrame in SFF'.
    rewrite SCF' in S'; inv S'.
    eapply IHLK; eauto.
Qed.

Hint Resolve getAddr_scopeofFrame_sub : sgraph.

Lemma getAddr_in_ds_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f r ff d s sf
    (ADDR: getAddr h f r (Addr_ ff d))
    (GH: good_sub_heap h)
    (SF: scopeofFrame h f s)
    (SR: scopeofRefP r s)
    (SFF: scopeofFrame h ff sf),
    exists ds, declsofScopeP sf ds /\ In d ds.
Proof.
  inversion 1; subst; intros. eapply path_connectivity' in PATH; sgauto.
  destruct PATH as [? [? SL]]. clear ADDR SR.
  generalize dependent x.
  generalize dependent x0.
  generalize dependent s.
  induction LK; intros.
  - eapply scopeofFrameDet in SFF; eauto; subst.
    assert (frame h f) by sgauto. specialize (GH _ H0).
    destruct GH. destruct H1.
    eapply scopeofFrameDet in SC; eauto; subst.
    inv SF. assert (slotsofFrame h f slots) by sgauto.
    apply DSF in H3. destruct H3 as [? [DD' DE]]. inv DD'.
    eexists; split. econstructor; sgauto. destruct SL as [? [? [? [? ?]]]]; subst.
    rewrite H4 in H3.  inv H3. simpl; auto.
  - inv SL. destruct H as [? [LL [GL [INS SL]]]].
    assert (LL': llinksofScopeP s0 l x2) by (econstructor; eauto).
    inv LL'. destruct H.
    eapply IHLK; sgauto.
    assert (frame h f) by sgauto.
    specialize (GH _ H1). inv GH. inv H2.
    specialize (LNF _ _ IMS). inv LNF. destruct H2.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply linksofScopeDet in H; eauto; subst.
    assert (llinksofScopeP s0 l (keys ks)) by (econstructor; eauto).
    eapply LNS in H. destruct H as [? [LL' [K IN]]].
    assert (In s (keys ks)). eapply keys_in; eauto.
    eapply IN in H. eapply llinksofFrameDet in IMS; eauto; subst.
    destruct H as [? [GET SF]].
    rewrite GET in S; inv S. auto.
Qed.

Lemma getAddr_getSlot_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f r ff s d
    (SF: scopeofFrame h f s)
    (SR: scopeofRefP r s)
    (ADDR: getAddr h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_sub_heap h),
  exists v t t', getSlot h ff d v /\ vtyp h v t' /\ sub t' t.
Proof.
  intros.
  assert (ADDR':=ADDR). eapply getAddr_scopeofFrame_sub in ADDR; eauto. destruct ADDR.
  assert (ADDR:=ADDR'). eapply getAddr_in_ds_sub in ADDR; eauto. destruct ADDR as [? [DS IN]].
  assert (SF':=H). apply scopeofFrameFrame in H.
  specialize (GH _ H). destruct GH. destruct H0, H1.
  inv DS. destruct H0; subst.
  eapply scopeofFrameDet in SC; eauto; subst.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP s1 x1) by sgauto.
  eapply DSS in H1. destruct H1. destruct H1.
  assert (IN':=IN). eapply H2 in IN. eapply in_keys in IN. destruct IN.
  inv H1.
  assert (getSlot h ff d x0) by sgauto.
  inv DS0. destruct H5; subst. rewrite H5 in H0; inv H0.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  assert (IN'':=IN).
  eapply ddataofScope_scopeofDecl in IN''; eauto.
  eapply WT in IN; sgauto.
  destruct IN as [? [VT' SUB']].
  do 3 eexists; split; sgauto.
  econstructor; eauto. econstructor; eauto.
Qed.

Hint Resolve getAddr_getSlot_sub : sgraph.

Lemma getAddr_typofDecl_getSlot_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f r ff s d sf
    (SF: scopeofFrame h f s)
    (SR: scopeofRefP r s)
    (ADDR: getAddr h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_sub_heap h)
    (SFF: scopeofFrame h ff sf),
  exists v t t', getSlot h ff d v /\ vtyp h v t' /\ sub t' t /\ typofDecl d t.
Proof.
  intros.
  assert (ADDR':=ADDR). eapply getAddr_scopeofFrame_sub in ADDR; eauto. destruct ADDR.
  assert (ADDR:=ADDR'). eapply getAddr_in_ds_sub in ADDR; eauto. destruct ADDR as [? [DS IN]].
  assert (SF':=H). apply scopeofFrameFrame in H.
  specialize (GH _ H). destruct GH. destruct H0, H1.
  inv DS. destruct H0; subst.
  eapply scopeofFrameDet in SC; eauto; subst.
  eapply scopeofFrameDet in SC0; eauto; subst.
  eapply scopeofFrameDet in SFF; eauto; subst.
  assert (ddataofScopeP sf x1) by sgauto.
  eapply DSS in H1. destruct H1. destruct H1.
  assert (IN':=IN). eapply H2 in IN. eapply in_keys in IN. destruct IN.
  inv H1.
  assert (getSlot h ff d x0) by sgauto.
  inv DS0. destruct H5; subst. rewrite H5 in H0; inv H0.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  assert (IN'':=IN).
  eapply ddataofScope_scopeofDecl in IN''; eauto.
  eapply WT in IN; sgauto.
  destruct IN as [? [VT' SUB']];
    do 3 eexists; split; sgauto.
  split; sgauto. split; sgauto.
  econstructor; eauto. econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

Hint Resolve getAddr_typofDecl_getSlot_sub : sgraph.

(* Note: not currently used. *)
Lemma getAddr_good_frame_sub :
  forall
     T `{ST: SubTyping T} `{VT: VTyp T} h f r ff s d
     (SF: scopeofFrame h f s)
     (SR: scopeofRefP r s)
     (ADDR: getAddr h f r (Addr_ ff d))
     (FH: frame h f)
     (GH: good_sub_heap h),
  exists sf v t t',
    scopeofFrame h ff sf /\ getSlot h ff d v /\ vtyp h v t' /\ sub t' t /\ typofDecl d t.
Proof.
  intros. assert (ADDR':=ADDR).
  eapply getAddr_scopeofFrame_sub in ADDR'; sgauto. destruct ADDR'.
  exists x. eapply getAddr_typofDecl_getSlot_sub in ADDR; eauto.
  destruct ADDR as [? [? [? [GS [VT' [SUB TD]]]]]]. do 3 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_good_frame_sub : sgraph.

Lemma good_path_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T}
    h
    (GH: good_sub_heap h)
    p f s d s'
    (SF: scopeofFrame h f s)
    (SLK: slookup s p s' d),
  exists f', lookup h f p d f' /\ scopeofFrame h f' s'.
Proof.
  induction p; intros.
  - destruct SLK as [? [? [? [? ?]]]]; subst.
    eexists; split; eauto. econstructor.
    edestruct GH as [WB _]; sgauto.
    eapply well_bound_get; eauto. econstructor; eauto.
  - destruct SLK as [? [? [LL [GL [IN SL]]]]].
    assert (GF: good_sub_frame h f) by sgauto.
    inv GF. inv H. eapply scopeofFrameDet in SF; eauto; subst.
    assert (LL': llinksofScopeP s0 e x0) by (econstructor; eauto).
    eapply LNS in LL'.
    destruct LL' as [? [IMF [KEYS IMSC]]]; subst.
    eapply IMSC in IN. inv IN. inv H.
    eapply IHp in SL; eauto.
    destruct SL as [? [LOOK SF]].
    eexists; split; sgauto.
Qed.

Lemma good_addr_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h r p f s d s'
    (SR: scopeofRefP r s)
    (RLK: rlookup r p s' d)
    (GH: good_sub_heap h)
    (SF: scopeofFrame h f s),
  exists ff, getAddr h f r (Addr_ ff d) /\
             scopeofFrame h ff s' /\
             exists ds,
               declsofScopeP s' ds /\
               In d ds.
Proof.
  intros. destruct RLK as [? [? [? ?]]].
  eapply scopeofRefDet in SR; eauto; subst.
  assert (H1':=H1).
  eapply good_path_sub in H1; eauto.
  destruct H1. destruct H1.
  eexists; split; sgauto. econstructor; sgauto.
  inv H0.
  edestruct path_connectivity' as [? [? SL]]; eauto.
  eapply slookupDet in H1'; eauto. destruct H1'; subst.
  edestruct slookup_ddata as [dd [P1 P2]]; eauto.
Qed.

Lemma good_frame_setSlot_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f s ds d
    (GF: good_sub_frame h f)
    (SC: scopeofFrame h f s)
    (DS: declsofScopeP s ds)
    (IN: In d ds),
  forall v,
  exists h', setSlot h f d v h'.
Proof.
  intros. inv GF. inv H0. eapply scopeofFrameDet in SC; eauto; subst.
  inv DS. destruct H0. subst. inv H.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP s x) by sgauto.
  eapply DSS in H. destruct H as [? [? ?]].
  destruct H. inv SC. erewrite H2 in H; inv H.
  eexists. econstructor; sgauto. eapply H1. assumption.
Qed.

Corollary good_frame_getSlot_sub :
  forall
    T `{ST: SubTyping T} `{VT: VTyp T} h f s d ds
    (GF: good_sub_frame h f)
    (SF: scopeofFrame h f s) 
    (DS: declsofScopeP s ds)
    (IN: In d ds),
  exists v, getSlot h f d v.
Proof.
  intros. inv GF. eapply well_bound_get; eauto.
Qed.


Hint Resolve good_addr_sub : sgraph.
Hint Resolve good_frame_setSlot_sub : sgraph.


Lemma initDefault_good_frame_sub :
  forall
    T `{ST: SubTyping T} `{DVT: DefaultVTyp T} h0 s ks f h1
    (INIT: initDefault h0 s ks f h1)
    (LNS: forall l ss,
        llinksofScopeP s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP s l (keys m)),
    good_sub_frame h1 f.
Proof.
  intros. inversion INIT. sgauto.
Qed.

Hint Resolve initDefault_good_frame_sub : sgraph.

Lemma initDefault_good_heap_sub :
  forall
    T `{ST: SubTyping T} `{DVT: DefaultVTyp T} h0 s ks f h1
    (GH: good_sub_heap h0)
    (INIT: initDefault h0 s ks f h1)
    (LNS: forall l ss,
        llinksofScopeP s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP s l (keys m)),
    good_sub_heap h1.
Proof.
  intros. inversion INIT. eapply initFrame_good_heap_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
Qed.

Lemma initDefault_good_heap1_sub :
  forall
    T `{ST: SubTyping T} `{DVT: DefaultVTyp T} h0 s f h1 l sl fl
    (GH: good_sub_heap h0)
    (INIT: initDefault h0 s [(l, [(sl, fl)])] f h1)
    (LNS: linksofScopeP s [(l, [sl])])
    (SL: scopeofFrame h0 fl sl),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros. inversion INIT.
  pose proof (initFrameFrames _ _ _ _ _ _ NF f0). destruct H0.
  apply H1 in H. destruct H. subst.
  split; eauto using initFrame_well_bound1.
  eapply initFrame_well_typed_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
  eapply initFrame_other_good_frame_sub in NF; sgauto.
Qed.

Lemma initDefault_good_heap0_sub :
  forall
    T `{ST: SubTyping T} `{DVT: DefaultVTyp T} h0 s f h1
    (GH: good_sub_heap h0)
    (PS: linksofScopeP s [])
    (INIT: initDefault h0 s [] f h1),
    good_sub_heap h1.
Proof.
  intros. unfold good_heap. intros.
  eapply initDefault_good_heap_sub; sgauto.
  + intros. inv H. destruct H0.
    eapply linksofScopeDet in PS; eauto; subst.  inv H0.
  + intros. inv H.
Qed.

Lemma initDefault_good_heap2_sub :
  forall
    T `{ST: SubTyping T} `{DVT: DefaultVTyp T} h0 s f h1 l sl fl l' sl' fl'
    (GH: good_sub_heap h0)
    (INIT: initDefault h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] f h1)
    (LNS: linksofScopeP s [(l, [sl]); (l', [sl'])])
    (SL: scopeofFrame h0 fl sl)
    (SL: scopeofFrame h0 fl' sl'),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros. inversion INIT.
  pose proof (initFrameFrames _ _ _ _ _ _ NF f0). destruct H0.
  apply H1 in H. destruct H. subst.
  split; eauto using initFrame_well_bound2.
  eapply initFrame_well_typed_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
  eapply initFrame_other_good_frame_sub in NF; sgauto.
Qed.


Hint Resolve initDefault_good_frame_sub : sgraph.
Hint Resolve initDefault_good_heap_sub : sgraph.
Hint Resolve initDefault_good_heap0_sub : sgraph.
Hint Resolve initDefault_good_heap1_sub : sgraph.
Hint Resolve initDefault_good_heap2_sub : sgraph.
