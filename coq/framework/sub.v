Require Import maps scopes frames.

Class SubTyping (T: Type) :=
  { sub : T -> T -> Prop ;
    sub_refl : forall t, sub t t ;
    sub_trans : forall t1 t2 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3 ;
  }.

Section TV.
  Context {T V: Type} {VT: @VTyp T V} {ST: SubTyping T}.

  Inductive well_sub_typed  (h: @H V fh) (f: FrameId) : Prop :=
  | well_typed_ :
      forall
        s
        (SC: scopeofFrame V fh h f s)
        ds
        (DS: declsofScopeP (@wc T dwc) s ds)
        (WT: forall d t v,
            In d ds ->
            typofDecl T dwc s d t ->
            getSlot V fh h f d v ->
            exists t', vtyp h v t' /\ sub t' t),
        well_sub_typed h f.

  Definition good_sub_frame h f := well_bound T V VT h f /\ well_sub_typed h f.
  Definition good_sub_heap h := forall f, frame h f -> good_sub_frame h f.

End TV.

Hint Constructors well_sub_typed : sgraph.

Lemma good_frame2good_sub_frame :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h f
    (GF: good_frame T V VT h f),
    good_sub_frame h f.
Proof.
  inversion 1; subst; econstructor; eauto.
  inv H0; econstructor; eauto using sub_refl.
Qed.

Hint Resolve good_frame2good_sub_frame : sgraph.

Lemma good_heap2good_sub_heap :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h
    (GH: good_heap T V VT h),
    good_sub_heap h.
Proof.
  intros. intro; intros. eapply GH in H. sgauto.
Qed.

Hint Resolve good_heap2good_sub_heap : sgraph.

Lemma setSlot_well_typed_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 f d v h1 t s
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
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
      eapply scopeofFrameDet in SF; eauto; subst.
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
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 f d v h1 t s f0
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
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
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 f d v h1 t s f0
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (WT: good_sub_frame h0 f0)
    (DIFF: f <> f0)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    good_sub_frame h1 f0.
Proof.
  intros; inv WT; sgauto. split; sgauto.
Qed.

Lemma setSlot_good_sub_frame :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 f d v h1 s t
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (WT: good_sub_frame h0 f)
    t'
    (VT': vtyp h0 v t')
    (SUB: sub t' t),
    good_sub_frame h1 f.
Proof.
  intros. inv WT. split; sgauto.
Qed.

Hint Resolve setSlot_good_sub_frame : sgraph.

Lemma setSlot_good_heap_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 f d v h1 s t
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
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

Lemma initNewFrame_well_typed_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> exists t', vtyp h0 v t' /\ sub t' t),
    well_sub_typed h1 f.
Proof.
  intros; inversion INIT. inv NF. assert (FF':=FF).
  eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
  eexists; sgauto.
  intros. eapply declsofScopeDet in TDs; eauto; subst.
  inv H2. rewrite H3 in FF; inv FF.
  eapply TYP in H0; eauto. destruct H0 as [? [VT' SUB']].
  eexists; split; sgauto. eapply initNewFrame_vtyp; eauto.
Qed.

Hint Resolve initNewFrame_well_typed_sub : sgraph.

Lemma initNewFrame_good_frame_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> exists t', vtyp h0 v t' /\ sub t' t)
    (** WellBound links: *)
    (LNS: forall l ss,
        llinksofScopeP (@g gat (@wc T dwc)) s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame V fh h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP (@g gat (@wc T dwc)) s l (keys m)),
    good_sub_frame h1 f.
Proof.
  intros; split; sgauto.
Qed.

Hint Resolve initNewFrame_good_frame_sub : sgraph.

Lemma initNewFrame_other_well_typed_sub :
  forall
    T (ST: SubTyping T) V (VT : @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    slots
    (TDs: declsofScopeP (@wc T dwc) s (@keys D V slots))
    (* (* dynamic decls? *) *)
    (* (DDs: dynamicDecls (keys ds)) *)
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
  edestruct WT0; sgauto; destruct H6.
  eapply fillFrame_vtyp in FF''; eauto.
  eapply newFrame_vtyp in NF; eauto.
Qed.

Hint Resolve initNewFrame_other_well_typed_sub : sgraph.

Lemma initNewFrame_other_good_frame_sub :
  forall
    T (ST: SubTyping T) V (VT : @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (* (* dynamic decls? *) *)
    (* (DDs: dynamicDecls (keys ds)) *)
    f'
    (GF: good_sub_frame h0 f'),
    good_sub_frame h1 f'.
Proof.
  intros; inv GF; sgauto.
  split; sgauto.
Qed.

Lemma initNewFrame_good_heap_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h0 s ks slots f h1
    (GH: good_sub_heap h0)
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> exists t', (@vtyp T V VT) h0 v t' /\ sub t' t)
    (** WellBound links: *)
    (LNS: forall l ss,
        llinksofScopeP (@g gat (@wc T dwc)) s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame V fh h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP (@g gat (@wc T dwc)) s l (keys m)),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ INIT f0). destruct H0.
  apply H1 in H. destruct H. subst. sgauto.
  eapply initNewFrame_other_good_frame_sub in INIT; sgauto.
Qed.

Lemma getAddr_scopeofFrame_sub :
  forall
    T (ST: SubTyping T) (G: @WCGAT T) V (VT: @VTyp T V) h f r ff d
    (GH: good_sub_heap h)
    (FH: frame h f)
    (ADDR: getAddr V fh wc h f r (Addr_ ff d)),
    exists sf, scopeofFrame V fh h ff sf.
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
    T (ST: SubTyping T) (G: @WCGAT T) V (VT: @VTyp T V) h f r ff d s sf
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (GH: good_sub_heap h)
    (SF: scopeofFrame V fh h f s)
    (SR: scopeofRefP (@wc T dwc) r s)
    (SFF: scopeofFrame V fh h ff sf),
    exists ds, declsofScopeP (@wc T dwc) sf ds /\ In d ds.
Proof.
  inversion 2; subst; intros. eapply path_connectivity in PATH; sgauto.
  destruct PATH as [? [? [? [SL [DD IND]]]]]. clear ADDR SR.
  generalize dependent x.
  generalize dependent x0.
  generalize dependent s.
  induction LK; intros.
  - eapply scopeofFrameDet in SFF; eauto; subst.
    assert (frame h f) by sgauto. specialize (GH _ H).
    destruct GH. destruct H0.
    eapply scopeofFrameDet in SC; eauto; subst.
    inv SF. assert (getSlots V fh h f slots) by sgauto.
    apply DSF in H2. destruct H2 as [? [DD' DE]]. inv DD'.
    eexists; split. econstructor; sgauto. inv SL.
    rewrite H3 in DD; inv DD. simpl; auto.
  - inv SL. destruct H as [LL [INS SL]].
    inv LL. destruct H.
    eapply IHLK; sgauto.
    assert (frame h f) by sgauto.
    specialize (GH _ H1). inv GH. inv H2.
    specialize (LNF _ _ IMS). inv LNF. destruct H2.
    eapply scopeofFrameDet in SF; eauto; subst.
    rewrite H2 in H; inv H.
    assert (llinksofScopeP (@g gat (@wc T dwc)) s0 l (keys ks)) by (econstructor; eauto).
    eapply LNS in H. destruct H as [? [LL [K IN]]].
    assert (In s (keys ks)). eapply keys_in; eauto.
    eapply IN in H. eapply llinksofFrameDet in IMS; eauto; subst.
    destruct H as [? [GET SF]].
    rewrite GET in S; inv S. auto.
Qed.

Lemma getAddr_getSlot_sub :
  forall
    T (ST: SubTyping T) (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d
    (SF: scopeofFrame V fh h f s)
    (SR: scopeofRefP (@wc T dwc) r s)
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_sub_heap h),
  exists v t t', getSlot V fh h ff d v /\ (@vtyp T V VT) h v t' /\ sub t' t.
Proof.
  intros.
  assert (ADDR':=ADDR). eapply getAddr_scopeofFrame_sub in ADDR; eauto. destruct ADDR.
  assert (ADDR:=ADDR'). eapply getAddr_in_ds_sub in ADDR; eauto. destruct ADDR as [? [DS IN]].
  assert (SF':=H). apply scopeofFrameFrame in H.
  specialize (GH _ H). destruct GH. destruct H0, H1.
  inv DS. destruct H0; subst.
  eapply scopeofFrameDet in SC; eauto; subst.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP wc s1 x1) by sgauto.
  eapply DSS in H1. destruct H1. destruct H1.
  assert (IN':=IN). eapply H2 in IN. eapply in_keys in IN. destruct IN.
  inv H1.
  assert (getSlot V fh h ff d x0) by sgauto.
  inv DS0. destruct H5; subst. rewrite H5 in H0; inv H0.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  eapply WT in IN; sgauto.
  destruct IN as [? [VT' SUB']].
  do 3 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_getSlot_sub : sgraph.

Lemma getAddr_typofDecl_getSlot_sub :
  forall
    T (ST: SubTyping T) (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d sf
    (SF: scopeofFrame V fh h f s)
    (SR: scopeofRefP (@wc T dwc) r s)
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_sub_heap h)
    (SFF: scopeofFrame V fh h ff sf),
  exists v t t', getSlot V fh h ff d v /\ (@vtyp T V VT) h v t' /\ sub t' t /\ typofDecl T dwc sf d t.
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
  assert (ddataofScopeP wc sf x1) by sgauto.
  eapply DSS in H1. destruct H1. destruct H1.
  assert (IN':=IN). eapply H2 in IN. eapply in_keys in IN. destruct IN.
  inv H1.
  assert (getSlot V fh h ff d x0) by sgauto.
  inv DS0. destruct H5; subst. rewrite H5 in H0; inv H0.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  eapply WT in IN; sgauto.
  destruct IN as [? [VT' SUB']];
  do 3 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_typofDecl_getSlot_sub : sgraph.

Lemma getAddr_good_frame_sub :
  forall
     T (ST: SubTyping T) (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d
     (SF: scopeofFrame V fh h f s)
     (SR: scopeofRefP (@wc T dwc) r s)
     (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
     (FH: frame h f)
     (GH: good_sub_heap h),
  exists sf v t t',
    scopeofFrame V fh h ff sf /\ getSlot V fh h ff d v /\ (@vtyp T V VT) h v t' /\ sub t' t /\ typofDecl T dwc sf d t.
Proof.
  intros. assert (ADDR':=ADDR).
  eapply getAddr_scopeofFrame_sub in ADDR'; sgauto. destruct ADDR'.
  exists x. eapply getAddr_typofDecl_getSlot_sub in ADDR; eauto.
  destruct ADDR as [? [? [? [GS [VT' [SUB TD]]]]]]. do 3 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_good_frame_sub : sgraph.

(* Corollary of [good_path]: In a good heap, looking up an address
results in a frame that instantiates the expected scope *)

Lemma good_path_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V)
    h
    (GH: good_sub_heap h)
    p f s d s'
    (SF: scopeofFrame V fh h f s)
    (SLK: slookup (@g gat (@wc T dwc)) s p s' d),
  exists f', lookup V fh h f p f' /\ scopeofFrame V fh h f' s'.
Proof.
  induction p; intros; inv SLK; sgauto. destruct H as [LL [IN SL]].
  assert (GF: good_sub_frame h f) by sgauto.
  inv GF. inv H. eapply scopeofFrameDet in SF; eauto; subst.
  eapply LNS in LL.
  destruct LL as [? [IMF [KEYS IMSC]]]; subst.
  eapply IMSC in IN. inv IN. inv H.
  eapply IHp in SL; eauto.
  destruct SL as [? [LOOK SF]].
  eexists; split; sgauto.
Qed.

Lemma good_addr_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h r p f s d s'
    (SLK: rlookup (@wc T dwc) s r p s' d)
    (GH: good_sub_heap h)
    (SF: scopeofFrame V fh h f s),
  exists ff, getAddr V fh (@wc T dwc) h f r (Addr_ ff d) /\ scopeofFrame V fh h ff s'.
Proof.
  intros. destruct SLK as [? [? ?]].
  assert (H1':=H1).
  eapply good_path_sub in H1; eauto.
  destruct H1. destruct H1.
  eexists; split; sgauto. econstructor; sgauto.
  eapply slookup_declofPath; sgauto.
Qed.

Lemma good_frame_setSlot_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) h f s ds d
    (SF: good_sub_frame h f)
    (SC: scopeofFrame V fh h f s)
    (DS: declsofScopeP (@wc T dwc) s ds)
    (IN: In d ds),
  forall v,
  exists h3, setSlot V fh h f d v h3.
Proof.
  intros. inv SF. inv H0. eapply scopeofFrameDet in SC; eauto; subst.
  inv DS. destruct H0. subst. inv H.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP wc s x) by sgauto.
  eapply DSS in H. destruct H as [? [? ?]].
  destruct H. inv SC. erewrite H2 in H; inv H.
  eexists. econstructor; sgauto. eapply H1. assumption.
Qed.

Hint Resolve good_addr_sub : sgraph.
Hint Resolve good_frame_setSlot_sub : sgraph.


Lemma initNewDefaultFrame_good_frame_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s ks f h1
    (INIT: initNewDefaultFrame DVT h0 s ks f h1)
    (** WellBound links: *)
    (LNS: forall l ss,
        llinksofScopeP (@g gat (@wc T dwc)) s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame V fh h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP (@g gat (@wc T dwc)) s l (keys m)),
    good_sub_frame h1 f.
Proof.
  intros. inversion INIT. sgauto.
Qed.

Hint Resolve initNewDefaultFrame_good_frame_sub : sgraph.

Lemma initNewDefaultFrame_good_heap_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s ks f h1
    (GH: good_sub_heap h0)
    (INIT: initNewDefaultFrame DVT h0 s ks f h1)
    (** WellBound links: *)
    (LNS: forall l ss,
        llinksofScopeP (@g gat (@wc T dwc)) s l ss ->
        exists m,
          get ELdec ks l = Some m /\
          keys m = ss /\
          forall s,
            In s ss ->
            exists f', get ScopeIdDec m s = Some f' /\
                       scopeofFrame V fh h0 f' s)
    (LNF: forall l m,
        get ELdec ks l = Some m ->
        llinksofScopeP (@g gat (@wc T dwc)) s l (keys m)),
    good_sub_heap h1.
Proof.
  intros. inversion INIT. eapply initNewFrame_good_heap_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
Qed.

Lemma initNewDefaultFrame_good_heap1_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s f h1 l sl fl
    (GH: good_sub_heap h0)
    (INIT: initNewDefaultFrame DVT h0 s [(l, [(sl, fl)])] f h1)
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl])])
    (SL: scopeofFrame V fh h0 fl sl),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros. inversion INIT.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ NF f0). destruct H0.
  apply H1 in H. destruct H. subst. split; sgauto.
  eapply initNewFrame_well_typed_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
  eapply initNewFrame_other_good_frame_sub in NF; sgauto.
Qed.

Lemma initNewDefaultFrame_good_heap2_sub :
  forall
    T (ST: SubTyping T) V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s f h1 l sl fl l' sl' fl'
    (GH: good_sub_heap h0)
    (INIT: initNewDefaultFrame DVT h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] f h1)
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl]); (l', [sl'])])
    (SL: scopeofFrame V fh h0 fl sl)
    (SL: scopeofFrame V fh h0 fl' sl'),
    good_sub_heap h1.
Proof.
  intros. unfold good_sub_heap. intros. inversion INIT.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ NF f0). destruct H0.
  apply H1 in H. destruct H. subst. split; sgauto.
  eapply initNewFrame_well_typed_sub in NF; sgauto.
  intros. eapply defaults_vtyp' in DF; sgauto. eexists; split; eauto using sub_refl.
  eapply initNewFrame_other_good_frame_sub in NF; sgauto.
Qed.

Hint Resolve initNewDefaultFrame_good_frame_sub : sgraph.
Hint Resolve initNewDefaultFrame_good_heap_sub : sgraph.
Hint Resolve initNewDefaultFrame_good_heap1_sub : sgraph.
Hint Resolve initNewDefaultFrame_good_heap2_sub : sgraph.
