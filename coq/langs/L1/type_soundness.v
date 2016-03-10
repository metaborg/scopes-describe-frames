Require Import scopes frames L1.syntax L1.well_typedness L1.well_boundness L1.semantics.

Section TypeSoundness.

Context `{G: Graph (@AT T)}.

(** * Value typing *)

(** Corresponds to paper Figure 15 bottom. *)

Inductive vtyp' (h:H) : V -> T -> Prop :=
| vtyp'_n : forall z, vtyp' h (NumV z) Tint
| vtyp'_c : forall
    d s e f t1 t2 sp
    (FS: scopeofFrame h f sp)
    (TD: typofDecl d t1)
    (DS: declsofScopeP s [d])
    (NOIMP: linksofScopeP s [(P, [sp])])
    (WT: wt_exp (E s t2 e))
    (WB: wb_exp (E s t2 e)),
    vtyp' h (ClosV d (E s t2 e) f) (Tarrow t1 t2)
.

Hint Constructors vtyp' : sgraph.

(** [vtyp] is preserved by the following frame operations. *)

Lemma setSlot_vtyp' :
  forall h0 f d v h1 v0 t0
    (SET: setSlot h0 f d v h1)
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
    h0 s f h1 ks v0 t0
    (NF: newFrame h0 s ks f h1)
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
    slots f h1 h2 v0 t0
    (FF: fillFrame f h1 slots h2)
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

(** The [VTyp] type class is instantiated using the lemmas above. *)
Instance VT : VTyp.
Proof.
  econstructor.
  apply setSlot_vtyp'.
  apply newFrame_vtyp'.
  apply fillFrame_vtyp'.
Defined.

(** * Auxiliary Lemmas *)

(** Evaluation does not change the frame-to-scope association. *)
Lemma eval_exp_scopeofFrame :
  forall h0 f0 e v h1,
    eval_exp h0 f0 e v h1 ->
    forall f s,
      scopeofFrame h0 f s ->
      scopeofFrame h1 f s.
Proof.
  induction 1; intros; sgauto.
Qed.


(** * Type Preservation *)

(** A selective hint database for the proof. *)
Hint Constructors vtyp' : pres.
Hint Resolve eval_exp_scopeofFrame : pres.
Hint Resolve initFrameSame_scopeofFrame : pres.
Hint Resolve initFrame_good_heap1 : pres.
Hint Resolve initFrame_good_heap0 : pres.
Hint Resolve setSlot_good_heap : pres.
Hint Resolve setSlot_vtyp' : pres.
Hint Resolve setSlotScope : pres.

Ltac peauto := eauto with pres.

Lemma exp_preservation:
  (forall h0 f e v h1
          (EVAL: eval_exp h0 f e v h1)
          s t pe
          (UNPACK: e = (E s t pe))
          (FS: scopeofFrame h0 f s)
          (GH: good_heap h0)
          (WT: wt_exp (E s t pe))
          (WB: wb_exp (E s t pe)),
      (good_heap h1 /\ vtyp h1 v t)).
Proof.
  induction 1; intros; simpl; try (inv UNPACK; inv WT; inv WB); subst; try (peauto; fail).
  - (* plus good case *)
    edestruct IHEVAL1; peauto.
    edestruct IHEVAL2; peauto.
  - (* plus bad case 1 *)
    edestruct IHEVAL; peauto.
    inv H0; edestruct ABORTL; sgauto.
  - (* plus bad case 2 *)
    edestruct IHEVAL2; peauto.
    edestruct IHEVAL1; peauto.
    inv H0; edestruct ABORTR; sgauto.
  - (* var good case *)
    edestruct good_addr as [? [ADDR' [SF [? [DS IN]]]]]; eauto.
    eapply getAddrDet in ADDR; eauto; inv ADDR.
    split; auto.
    edestruct GH as [WB WT]. inv SF. eapply keys_in in H. apply H.
    inv WT.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply declsofScopeDet in DS; eauto; subst.
    eapply rlookupDet in DR; eauto; subst. destruct DR as [? [? ?]]; subst.
    eapply WT0; peauto.
  - (* var bad case 1 *)
    edestruct good_addr as [? [ADDR' [SF [? [DS IN]]]]]; eauto.
    exfalso. eapply ADDR; eauto.
  - (* var bad case 2 *)
    edestruct good_addr as [? [ADDR' [SF [? [DS IN]]]]]; eauto.
    eapply getAddrDet in ADDR; eauto; inv ADDR.
    edestruct GH as [WB WT]. inversion SF. eapply keys_in; eauto.
    edestruct well_bound_get as [v P]; eauto.
    exfalso. eapply NGET; eauto.
  - (* app good case *)
    edestruct IHEVAL1; eauto.
    edestruct IHEVAL2; peauto. destruct e. inv H0.
    edestruct IHEVAL3; peauto.
    assert (SF':scopeofFrame h2 ff sp0) by peauto.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply initFrame_good_heap1; peauto.
    intros.
    simpl in IN. inv IN;  try contradiction.
    simpl in GET. destruct (Ddec d0 d0); inv GET.
    eapply typofDeclDet in TD0; eauto; subst.
    assumption.
  - (* app bad case 1 *)
    edestruct IHEVAL; peauto. destruct v1; inv ABORT1; inv H0.
  - (* app bad case 2 *)
    edestruct IHEVAL1; peauto.
    edestruct IHEVAL2; peauto. inv H2.
Qed.

Theorem prog_sound :
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
  assert (scopeofFrame h0 f s0) by peauto.
  assert (good_heap emptyHeap) by inversion 1.
  assert (good_heap h0) by peauto.
  edestruct exp_preservation as [? ?]; peauto.
  intro; subst v. inv H3.
Qed.

End TypeSoundness.
