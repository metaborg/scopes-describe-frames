Require Import ZArith scopes frames L1.syntax L1.well_typedness L1.well_boundness L1.semantics.

Inductive vtyp' {G: @WCGAT T} (h:@H V FH) : V -> T -> Prop :=
| vtyp'_n : forall z, vtyp' h (NumV z) Tint
| vtyp'_c : forall
    d s e f t1 t2 sp
    (FS: scopeofFrame V FH h f sp)
    (TD: typofDecl T G s d t1)
    (DS: declsofScopeP wc s [d])
    (NOIMP: linksofScopeP wc s [(P, [sp])])
    (WT: @wt_exp G (E s t2 e))
    (WB: @wb_exp G (E s t2 e)),
    vtyp' h (ClosV d (E s t2 e) f) (Tarrow t1 t2)
.
Hint Constructors vtyp' : sgraph.

Lemma setSlot_vtyp' :
  forall
    (G: @WCGAT T) h0 f d v h1 v0 t0
    (SET: setSlot V FH h0 f d v h1)
    (VT: vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv SET; induction VT; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - rewrite H1 in H0; inv H0. econstructor; rewrite get_set_same; eauto.
  - econstructor; rewrite get_set_other; eauto.
Qed.

Lemma newFrame_vtyp' :
  forall
    (G: @WCGAT T) h0 s f h1 ks v0 t0
    (NF: newFrame V FH h0 s ks f h1)
    (VT: vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv NF; induction VT; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - apply keys_in in H0; contradiction.
  - econstructor; rewrite get_set_other; eauto.
Qed.

Lemma fillFrame_vtyp' :
  forall
    (G: @WCGAT T) slots f h1 h2 v0 t0
    (FF: fillFrame V FH f h1 slots h2)
    (VT: vtyp' h1 v0 t0),
    vtyp' h2 v0 t0.
Proof.
  intros; destruct FF as [? [? [? [? ?]]]]; subst; induction VT; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - rewrite H in H0; inv H0. econstructor; rewrite get_set_same; eauto.
  - econstructor; rewrite get_set_other; eauto.
Qed.


Hint Resolve setSlot_vtyp : sgraph.  
Hint Resolve newFrame_vtyp : sgraph.
Hint Resolve fillFrame_vtyp : sgraph.

Instance VT {G: @WCGAT T} : @VTyp T V :=
  { fh := FH }.
Proof.
  apply vtyp'.
  apply setSlot_vtyp'.
  apply newFrame_vtyp'.
  apply fillFrame_vtyp'.
Defined.


Section TypeSoundness.

  Context {G: @WCGAT T}.

  Lemma eval_exp_scopeofFrame :
    forall h0 f0 e v h1,
      eval_exp h0 f0 e v h1 ->
      forall f s,
        scopeofFrame V FH h0 f s ->
        scopeofFrame V FH h1 f s.
  Proof.
    induction 1; intros; sgauto.
  Qed.

  Hint Resolve eval_exp_scopeofFrame : sgraph.
  Hint Unfold abort : sgraph.

  Lemma exp_preservation:
    (forall h0 f e v h1
            (EVAL: eval_exp h0 f e v h1)
            s t pe
            (UNPACK: e = (E s t pe))
            (FS: scopeofFrame V (@fh T V VT) h0 f s)
            (GH: good_heap T V VT h0)
            (WT: wt_exp (E s t pe))
            (WB: wb_exp (E s t pe)),
        (good_heap T V VT h1 /\ (@vtyp T V VT) h1 v t)).
  Proof.
    induction 1; intros; simpl; try (inv UNPACK; inv WT; inv WB); subst; try (sgauto; fail).
    - (* plus good case *)
      edestruct IHEVAL1; sgauto.
      edestruct IHEVAL2; sgauto.
    - (* plus bad case 1 *)
      edestruct IHEVAL; sgauto.
      inv H0; edestruct ABORTL; sgauto.
    - (* plus bad case 2 *)
      edestruct IHEVAL2; sgauto.
      edestruct IHEVAL1; sgauto.
      inv H0; edestruct ABORTR; sgauto.
    - (* var good case *)
      assert (DR':=DR). inv DR'. inv H0.
      eapply (good_addr T V VT) in DR; sgauto.
      destruct DR as [? [ADDR' SF']].
      eapply getAddrDet in ADDR; eauto; inv ADDR.
      eapply getAddr_good_frame in ADDR'; sgauto.
      destruct ADDR' as [? [? [? [SF'' [GS [VT TD']]]]]]. simpl in *.
      eapply scopeofFrameDet in SF'; eauto; subst.
      eapply typofDeclDet in TD; eauto; subst.
      eapply getSlotDet in GET; eauto; subst.
      sgauto.
    - (* var bad case 1 *)
      assert (DR':=DR). inv DR'. inv H0.
      eapply (good_addr T V VT) in DR; sgauto.
      destruct DR as [? [ADDR' SF']].
      eapply ADDR in ADDR'. contradiction.
    - (* var bad case 2 *)
      assert (DR':=DR). inv DR'. inv H0.
      eapply (good_addr T V VT) in DR; sgauto.
      destruct DR as [? [ADDR' SF']].
      eapply getAddrDet in ADDR; eauto; inv ADDR.
      eapply getAddr_good_frame in ADDR'; sgauto.
      destruct ADDR' as [? [? [? [SF'' [GS [VT TD']]]]]]. simpl in *.
      eapply NGET in GS. contradiction.
    - (* app good case *)
      edestruct IHEVAL1; sgauto.
      edestruct IHEVAL2; sgauto. destruct e. inv H0.
      edestruct IHEVAL3; sgauto.
      assert (SF':scopeofFrame V FH h2 ff sp0) by sgauto.
      eapply scopeofFrameDet in SF; eauto; subst.
      eapply initNewFrame_good_heap1; sgauto.
      intros. inv H0. Focus 2. inv H5.
      simpl in H3. inv H4. destruct (Ddec d d); [|intuition]. inv H5.
      eapply typofDeclDet in TD; sgauto; subst; sgauto.
    - (* app bad case 1 *)
      edestruct IHEVAL; sgauto. destruct v1; inv ABORT1; inv H0.
    - (* app bad case 2 *)
      edestruct IHEVAL1; sgauto.
      edestruct IHEVAL2; sgauto. inv H2.
  Qed.

End TypeSoundness.
