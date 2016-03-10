Require Import L3.well_boundness L3.well_typedness L3.semantics prop_fold sub.

Instance FH : @FrameHeap V := {}.

Section TypeSoundness.

Context `{G: Graph (@AT T)}.

(** * Value Typing *)

(** Corresponds to Fig. 30 (where the class first and second premise
of [VtCDE] and [VtCD] have been unfolded and merged) *)

Inductive vtyp' (h: H) : V -> T -> Prop :=
| vtyp'_n : forall z, vtyp' h (NumV z) Tint
| vtyp'_b : forall b, vtyp' h (BoolV b) Tbool
| vtyp'_f :
    forall
      ds s e f tas tr sp
      (FS: scopeofFrame h f sp)
      (TD: typofDecls ds tas)
      (DS: declsofScopeP s ds)
      (NOIMP: linksofScopeP s [(P, [sp])])
      (WT: wt_exp (E s tr e))
      (WB: wb_exp (E s tr e)),
      vtyp' h (ClosV ds (E s tr e) f) (Tarrow tas tr)
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
      vtyp' h (ObjectV f) (Tclass d)

(** Class constructors: *)
| vtyp_cc : forall
    s0 d rs es optr f s sp ds ts
    (ASC: assocScope d s)
    (DS: declsofScopeP s ds)
    (TS: typofDecls ds ts)
    (FS: scopeofFrame h f sp)
    (OPTR: match optr with
           | Some r =>
             scopeofRefP r sp /\
             exists p spar dpar,
               rlookup r p sp dpar /\
               assocScope dpar spar /\
               typofDecl dpar (TclassDef dpar) /\
               linksofScopeP s [(P, [sp]); (I, [spar])]
           | None =>
             linksofScopeP s [(P, [sp])]
           end)
    (SRS: forall r, In r rs -> scopeofRefP r s)
    (WBE: forall e, In e es -> wb_exp e /\ expScope e = s)
    (WTE: Forall2 (fun e r =>
                     exists sr p s'' d' t',
                       scopeofRefP r sr /\
                       rlookup r p s'' d' /\
                       typofDecl d' t' /\ sub' (expType e) t' /\ wt_exp e) es rs),
    vtyp' h (ConstructorV s0 d optr (rs, es) f) (TclassDef d)

(** Null values are typed by classes: *)
| vtyp'_nr : forall d, vtyp' h NullV (Tclass d)

(** Trying to access a null value as an object raises a NullPointer
exception, which is allowed in any context: *)
| vtyp'_q : forall t, vtyp' h (AbortV NullPointer) t
.

Hint Constructors vtyp' : sgraph.

(** [vtyp] is preserved by the following frame operations. *)

Lemma setSlot_vtyp' :
  forall
    h0 f d v h1 v0 t0
    (SET: setSlot h0 f d v h1)
    (VT: vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv SET; induction VT; sgauto.
  - econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
    rewrite H1 in H0; inv H0. econstructor; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H1 in H0; inv H0; eauto.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    econstructor; rewrite H1 in H0; inv H0; eauto; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
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
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst. apply keys_in in H0. contradiction.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    eapply keys_in in H0; contradiction.
    econstructor; rewrite get_set_other; eauto.
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
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H0 in H; inv H; eauto.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    econstructor; rewrite H0 in H; inv H; eauto; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
Qed.

Hint Resolve setSlot_vtyp' : sgraph.
Hint Resolve newFrame_vtyp' : sgraph.
Hint Resolve fillFrame_vtyp' : sgraph.


Instance VT0 : VTyp.
Proof.
  econstructor.
  apply setSlot_vtyp'.
  apply newFrame_vtyp'.
  apply fillFrame_vtyp'.
Defined.

(** * Default Values *)

Inductive default : T -> V -> Prop :=
| def_n : default Tint (NumV 0)
| def_b : default Tbool (BoolV false)
| def_df : forall ts t v,
    default t v ->
    default (Tarrow ts t) (DefFunV v)
| def_r : forall d, default (Tclass d) NullV
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

Instance DVT : DefaultVTyp.
Proof.
  econstructor.
  instantiate (1:=default).
  apply default_vtyp'.
Qed.

(** * Subtyping *)

Hint Constructors sub' : sgraph.
Hint Constructors sub1 : sgraph.
Hint Constructors upcast : sgraph.

Lemma sub'_trans :
  forall t1 t2 t3,
    sub' t1 t2 ->
    sub' t2 t3 ->
    sub' t1 t3.
Proof.
  induction 1; intros; sgauto.
Qed.

Lemma sub'_refl :
  forall t,
    sub' t t.
Proof. sgauto. Qed.

Hint Resolve sub'_trans : sgraph.
Hint Resolve sub'_refl : sgraph.

Instance ST : @SubTyping T.
Proof.
  econstructor.
  eapply sub'_refl.
  eapply sub'_trans.
Defined.

Hint Unfold sub : sgraph.

Lemma sub_int :
  forall
    t t'
    (SUB: sub' t t')
    (TEQ: t' = Tint),
    t = Tint.
Proof.
  induction 1; intros; eauto; try discriminate.
  rewrite IHSUB in SUB1; auto. inv SUB1.
Qed.

Lemma sub_bool :
  forall
    t t'
    (SUB: sub' t t')
    (TEQ: t' = Tbool),
    t = Tbool.
Proof.
  induction 1; intros; eauto; try discriminate.
  rewrite IHSUB in SUB1; auto. inv SUB1.
Qed.

Lemma sub_tarrow :
  forall
    t t'
    (SUB: sub' t t')
    t1s' t2'
    (TEQ: t' = Tarrow t1s' t2'),
  exists t1s t2,
    t = Tarrow t1s t2 /\
    (Forall2 (fun t1 t1' => sub' t1 t1') t1s' t1s) /\
    sub' t2 t2'.
Proof.
  induction 1; intros; subst; eauto; try discriminate.
  - do 2 eexists; split; eauto.
    split; sgauto. clear t2'.
    induction t1s'; sgauto.
  - edestruct IHSUB as [t1s [t2 [TEQ [ARGS SUB']]]]; subst; eauto.
    inv SUB1.
    do 2 eexists; split; eauto.
    split; eauto using sub'_trans.
    clear - ARGS ARGS0.
    generalize dependent ARGS0. generalize dependent t1s0.
    induction ARGS; intros. inv ARGS0. constructor.
    inv ARGS0; eauto using sub'_trans.
Qed.

Lemma sub_tclass :
  forall
    t t'
    (SUB: sub' t t')
    d'
    (TEQ: t' = Tclass d')
    s'
    (ASC: assocScope d' s'),
  exists d s,
    t = Tclass d /\
    assocScope d s.
Proof.
  induction 1; intros; subst; sgauto; try discriminate.
  edestruct IHSUB; eauto. destruct H as [? [? [TEQ ASC']]]. subst. inv SUB1; sgauto.
Qed.

Lemma sub_tclassdef :
  forall
    t t'
    (SUB: sub' t t')
    d'
    (TEQ: t' = TclassDef d'),
  exists d,
    t = TclassDef d.
Proof.
  induction 1; intros; subst; eauto; try discriminate.
  edestruct IHSUB as [? EQ]; eauto. subst. inv SUB1.
Qed.

Lemma forall2_sub_trans :
  forall
    es ts P
    (P1: Forall2 (fun e t => sub' (expType e) t /\ P e)
                 es ts)
    ts'
    (P2: Forall2 (fun t t' => sub' t t') ts ts'),
    Forall2 (fun e t => sub' (expType e) t /\ P e) es ts'.
Proof.
  induction 1; intros; eauto; try inv P2; eauto using Forall2.
  destruct H. sgauto.
Qed.

Lemma upcast_scopeofFrame :
  forall h rf srec rf',
    upcast h rf srec rf' ->
    scopeofFrame h rf' srec.
Proof.
  induction 1; eauto.
Qed.

Lemma forall2_in :
  forall
    X xs (x:X) Y (ys:list Y) P
    (IN: In x xs),
    Forall2 (fun y x => P y x) ys xs ->
    exists y, P y x /\ In y ys.
Proof.
  induction xs; intros; inversion IN; subst; inv H; eauto.
  eexists; split; eauto. econstructor; eauto.
  eapply IHxs in H5; eauto. destruct H5 as [? [PY INY]].
  eexists; split; eauto. econstructor 2; eauto.
Qed.

(** Key subtyping lemma (Lemma 4 in Appendix C in the paper) *)
Lemma sub_class_upcast :
  forall
    t t'
    (SUB: sub' t t')
    d
    (TEQ: t = Tclass d)
    d'
    (TEQ': t' = Tclass d')
    h1 srec
    (GH: good_sub_heap h1)
    (ASC: assocScope d' srec)
    rf
    (VT: vtyp h1 (ObjectV rf) (Tclass d)),
  exists rf', upcast h1 rf srec rf'.
Proof.
  induction 1; intros; subst.
  - inv TEQ'. inv VT. eapply assocScopeDet in ASC; eauto; subst.
    sgauto.
  - inv SUB1. inv VT.
    assert (frame h1 rf) by sgauto.
    generalize (GH _ H); intro GFRF; destruct GFRF as [WB WT]. inv WB.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply assocScopeDet in ASC0; eauto; subst.
    assert (llinksofScopeP s I ims).
    { inv IMS; sgauto. econstructor; split; sgauto. simpl.
      destruct (ELdec I I); intuition. }
    destruct (LNS _ _ H0) as [? [IMF [EQ FSF]]]. subst.
    eapply FSF in IN_IMS. destruct IN_IMS as [? [EQ SF']].
    assert (vtyp h1 (ObjectV x0) (Tclass d'0)).
    econstructor; sgauto.
    eapply IHSUB in H1; eauto. destruct H1.
    sgauto.
Qed.

(** * Auxiliary Lemmas *)

Hint Resolve forall2_sub_trans : sgraph.

Lemma eval_exp_scopeofFrame_aux :
  (forall h0 f0 e v h1,
      eval_exp h0 f0 e v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 f1 ds es v h1,
      fill_slots_par h0 f0 f1 ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 ds es v h1,
      fill_slots_seq h0 f0 ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 ds es v h1,
      fill_slots_rec h0 f0 ds es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 e v h1,
      eval_lhs h0 f0 e v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 r v h1,
      eval_objinit h0 f0 r v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s) /\
  (forall h0 f0 f1 rs es v h1,
      assign_refs h0 f0 f1 rs es v h1 ->
      forall f s,
        scopeofFrame h0 f s ->
        scopeofFrame h1 f s).
Proof.
  apply eval_exp_ind3; sgauto.
Qed.

Definition eval_exp_scopeofFrame     := proj1 eval_exp_scopeofFrame_aux.
Definition fill_par_scopeofFrame     := proj1 (proj2 eval_exp_scopeofFrame_aux).
Definition fill_seq_scopeofFrame     := proj1 (proj2 (proj2 eval_exp_scopeofFrame_aux)).
Definition fill_rec_scopeofFrame     := proj1 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).
Definition eval_lhs_scopeofFrame     := proj1 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux)))).
Definition eval_objinit_scopeofFrame := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))))).
Definition assign_refs_scopeofFrame  := proj2 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux)))).

(** * Type Preservation *)

(** A Hint database for list membership operations. *)
Hint Resolve in_eq : ins.
Hint Resolve in_cons : ins.

Lemma in_2 : forall {A:Type} (x1 x2 y: A) (xs:list A), In y (x1::xs) -> In y (x1::x2::xs).
Proof.
  intros. inv H; eauto with ins.
Qed.

Hint Resolve in_2 : ins.

(** An alternative, more selective hint database for this proof. *)
Hint Constructors vtyp' : pres.
Hint Resolve eval_exp_scopeofFrame : pres.
Hint Resolve fill_par_scopeofFrame : pres.
Hint Resolve fill_seq_scopeofFrame : pres.
Hint Resolve fill_rec_scopeofFrame : pres.
Hint Resolve eval_lhs_scopeofFrame : pres.
Hint Resolve eval_objinit_scopeofFrame : pres.
Hint Resolve assign_refs_scopeofFrame : pres.
Hint Resolve initDefaultDiff_scopeofFrame : pres.
Hint Resolve initDefaultSame_scopeofFrame : pres.
Hint Resolve initDefault_good_heap2_sub : pres.
Hint Resolve initDefault_good_heap1_sub : pres.
Hint Resolve initDefault_good_heap_sub : pres.
Hint Resolve setSlot_good_heap : pres.
Hint Resolve setSlot_good_heap_sub : pres.
Hint Resolve setSlot_vtyp' : pres.
Hint Resolve setSlotScope : pres.
Hint Resolve scopeofFrameFrame : pres.
Hint Constructors wb_lhs : pres.
Hint Constructors wt_lhs : pres.

Ltac peauto := eauto 4 with pres ins.

(** An augmented database for subtyping *)
Hint Resolve sub'_refl : psub.
Hint Resolve sub'_trans : psub.
Hint Resolve sub_refl : psub.
Hint Resolve sub_trans : psub.

Ltac pseauto := eauto with pres ins psub.

Lemma exp_preservation:
  (forall
      h0 f e v h1
      (EVAL: eval_exp h0 f e v h1)
      s t pe
      (UNPACK: e = (E s t pe))
      (FS: scopeofFrame h0 f s)
      (GH: good_sub_heap h0)
      (WT: wt_exp (E s t pe))
      (WB: wb_exp (E s t pe)),
      (good_sub_heap h1 /\ exists t', vtyp h1 v t' /\ sub' t' t))
  /\
  (forall
      h0 f f1 ds e2s v h1
      (FSPAR: fill_slots_par h0 f f1 ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      s1
      (FS: scopeofFrame h0 f1 s1)
      (GH: good_sub_heap h0)
      ds0
      (DS0: declsofScopeP s1 ds0)
      (DS: forall d, In d ds -> In d ds0)
      t2s
      (TYPDECS: typofDecls ds t2s)
      (WB: forall e,
          In e e2s ->
          expScope e = s /\ wb_exp e)
      (WT: Forall2 (fun (e : exp) (t : T) => sub' (expType e) t /\ wt_exp e) e2s
                   t2s),
      good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
  /\
  (forall
      h0 f ds e2s v h1
      (FSSEQ: fill_slots_seq h0 f ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      (GH: good_sub_heap h0)
      t2s
      (TYPDECS: typofDecls ds t2s)
      s'
      (WB1: ForallFold2 (fun d e ps newPs =>
                           (linksofScopeP newPs [(P, [ps])]) /\
                           declsofScopeP newPs [d] /\
                           (expScope e) = ps /\
                           wb_exp e)
                        ds e2s s s')
      (WT: Forall2 (fun (e : exp) (t : T) => sub' (expType e) t /\ wt_exp e) e2s
                   t2s),
      good_sub_heap h1 /\
      ((exists f, v = FrameAV f /\ scopeofFrame h1 f s') \/
       v = AbortAV NullPointer))
  /\
  (forall
      h0 f ds e2s v h1
      (FSREC: fill_slots_rec h0 f ds e2s v h1)
      s
      (FS: scopeofFrame h0 f s)
      (GH: good_sub_heap h0)
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
                      | Tarrow _ _ => sub' (expType e) t
                      | _ => False
                      end /\
                      wt_exp e) e2s
                   t2s),
      good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
  /\
  (forall
      h0 f lhs v h1
      (EVAL: eval_lhs h0 f lhs v h1)
      s t
      (FS: scopeofFrame h0 f s)
      (WB: wb_lhs s lhs)
      (WT: wt_lhs t lhs)
      (GH: good_sub_heap h0),
      good_sub_heap h1 /\ match v with
                          | AddrAV (Addr_ ff d) =>
                            exists s' ds,
                            scopeofFrame h1 ff s' /\
                            declsofScopeP s' ds /\
                            In d ds /\
                            typofDecl d t
                          | AbortAV NullPointer => True
                          | _ => False
                          end) /\
  (forall
      h0 f r v h1
      (EVAL: eval_objinit h0 f r v h1)
      s
      (SR: scopeofRefP r s)
      p' s' d
      (DR: rlookup r p' s' d)
      (DR: typofDecl d (TclassDef d))
      (FS: scopeofFrame h0 f s)
      (FS: scopeofRefP r s)
      (GH: good_sub_heap h0),
      good_sub_heap h1 /\ match v with
                          | FrameAV rf =>
                            vtyp h1 (ObjectV rf) (Tclass d)
                          | AbortAV NullPointer => True
                          | _ => False
                          end) /\
  (forall
      h0 f0 f1 rs es v h1
      (ASREF: assign_refs h0 f0 f1 rs es v h1)
      s
      (FS: scopeofFrame h0 f0 s)
      (WBE: forall e, In e es -> wb_exp e /\ expScope e = s)
      (WTE: Forall2 (fun e r =>
                       exists sr p s'' d' t',
                         scopeofRefP r sr /\
                         rlookup r p s'' d' /\
                         typofDecl d' t' /\ sub' (expType e) t' /\ wt_exp e) es rs)
      (GH: good_sub_heap h0)
      s'
      (FS: scopeofFrame h0 f1 s')
      (SR: forall r,
          In r rs ->
          scopeofRefP r s'),
      good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer)).
Proof.
  apply eval_exp_ind3; intros; [(simpl; try (inv UNPACK; inv WT; inv WB); subst) ..].
  - (* cnum *)
    pseauto.
  - (* true *)
    pseauto.
  - (* false *)
    pseauto.
  - (* plus good case *)
    edestruct H as [? _]; peauto.
    edestruct H0 as [? _]; pseauto.
  - (* plus bad case 1 *)
    edestruct H as [? [? [VT SUB]]]; peauto.
    eapply sub_int in SUB; eauto; subst.
    inv VT; peauto; edestruct ABORTL; peauto.
  - (* plus bad case 2 *)
    edestruct H as [? [? _]]; peauto.
    edestruct H0 as [? [? [VT SUB]]]; peauto.
    eapply sub_int in SUB; subst; eauto.
    inv VT; peauto; edestruct ABORTR; peauto.
  - (* gt good case *)
    edestruct H as [? _]; peauto.
    edestruct H0 as [? _]; pseauto.
  - (* gt bad case 1 *)
    edestruct H as [? [? [VT SUB]]]; peauto.
    eapply sub_int in SUB; subst; eauto.
    inv VT; pseauto; edestruct ABORTL; eauto.
  - (* gt bad case 2 *)
    edestruct H as [? _]; peauto.
    edestruct H0 as [? [? [VT SUB]]]; peauto.
    eapply sub_int in SUB; subst; eauto.
    inv VT; pseauto; edestruct ABORTR; eauto.
  - (* lhs good case *)
    edestruct H as [GH1 [? [? [SF [DS [IN TD]]]]]]; eauto.
    intuition auto.
    edestruct GH1 as [WB WT]. inversion SF. eapply keys_in; eauto.
    inv WT.
    eapply scopeofFrameDet in SF; eauto; subst.
    eapply declsofScopeDet in DS; eauto; subst.
    eapply WT1; eauto.
  - (* lhs bad case 1 *)
    edestruct H as [? VT]; eauto.
    destruct q; inv VT; pseauto.
  - (* lhs bad case 2 *)
    edestruct H as [GH1 [? [? [SF [DS [IN [TD GF]]]]]]]; eauto.
    edestruct good_frame_getSlot_sub with (f := ff) (h:=h1) as [v P]; peauto.
    exfalso; eapply GET; eauto.
  - (* fn *)
    pseauto.
  - (* app good case *)
    edestruct H as [? [? [VT SUB]]]; peauto. inv VT.
    eapply sub_tarrow in SUB; peauto. destruct SUB as [? [? [EQ [FA SUB]]]]; inv EQ.
    eapply scopeofFrameDet in SF; eauto; subst.
    edestruct H0 as [? _]; eauto using forall2_sub_trans with pres.
    edestruct H1 as [? [? [VT SUB']]]; pseauto.
  - (* app default fun *)
    edestruct H as [? [? [VT SUB]]]; peauto.
    eapply sub_tarrow in SUB; peauto. destruct SUB as [? [? [EQ [FA SUB]]]]; subst.
    inv VT; pseauto.
  - (* app bad case 1 *)
    edestruct H as [? [? [VT SUB]]]; peauto.
    eapply sub_tarrow in SUB; peauto. destruct SUB as [? [? [EQ [FA SUB]]]]; subst.
    inv VT; simpl; peauto; contradiction.
  - (* app bad case 2 *)
    edestruct H as [? [? [VT1 SUB]]]; peauto.
    eapply sub_tarrow in SUB; peauto. destruct SUB as [? [? [EQ [FA SUB]]]]; subst.
    inv VT1.
    eapply scopeofFrameDet in SF; eauto; subst.
    edestruct H0 as [? [X|X]]; eauto using forall2_sub_trans with pres; inv X.
    peauto.
  - (* letpar good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s1) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? _]; peauto.
    edestruct H0 as [? [? [VT SUB']]]; eauto using sub'_trans with pres.
  - (* letpar bad case 1 *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s1) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [X|X]]; peauto; inv X.
    peauto.
  - (* letseq good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    edestruct H as [? [[ff [FEQ SF]]|X]]; peauto; [inv FEQ|inv X].
    edestruct H0 as [? [? [? ?]]]; eauto using sub'_trans with pres.
  - (* letseq bad case 1 *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    edestruct H as [? [[? [FEQ SF]]|X]]; peauto; [inv FEQ|inv X].
    peauto.
  - (* letrec good case *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s0) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? _]; peauto.
    edestruct H0 as [? [? [? ?]]]; eauto using sub'_trans with pres.
  - (* letrec bad case 1 *)
    rewrite UNZIP1 in UNZIP0; inv UNZIP0.
    rewrite UNZIP1 in UNZIP; inv UNZIP.
    assert (sf = s0) by (eapply scopeofFrameDet; peauto); subst.
    edestruct H as [? [X|X]]; peauto; inv X.
    peauto.
  - (* asgn good case *)
    edestruct H as [? [? [? [SF [DS [IN TD]]]]]]; peauto.
    edestruct H0 as [? [? [VT SUB']]]; peauto.
    split; eauto using setSlot_good_heap_sub, sub_trans, sub'_trans with pres ins.
  - (* asgn bad case 1 *)
    edestruct H as [? X]; peauto. destruct q; inv X; peauto.
  - (* asgn bad case 2 *)
    edestruct H as [? [? [SF [DS [IN [TD GF]]]]]]; peauto.
    edestruct H0 as [? [? [VT SUB']]]; eauto using sub'_trans with pres.
  - (* asgn bad case 3 *)
    edestruct H as [? [? [SF [DS [IN [TD GF]]]]]]; peauto.
    edestruct H0 as [? ?]; peauto.
    exfalso.
    edestruct good_frame_setSlot_sub with (f:= ff) (h:= h2) as [h' P]; peauto.
    eapply SET; eauto.
  - (* if good case t *)
    subst. edestruct H; peauto.
  - (* if good case f *)
    subst. edestruct H; peauto.
  - (* if bad case *)
    subst. edestruct H as [? [? [VT SUB']]]; peauto.
    eapply sub_bool in SUB'; eauto; subst.
    destruct v1; inv VT; pseauto.
    edestruct ABORT1; eauto.
  - (* seq good case *)
    edestruct H; peauto.
  - (* seq bad case 1 *)
    edestruct H as [? [? [VT SUB']]]; peauto.
    inv VT; pseauto.
  - (* new good case *)
    eapply rlookupDet in RL; eauto. destruct RL as [? [? ?]]; subst.
    eapply assocScopeDet in ASC; eauto; subst.
    edestruct H; pseauto.
  - (* new bad case 1 *)
    eapply rlookupDet in RL; peauto. destruct RL as [? [? ?]]; subst.
    eapply assocScopeDet in ASC; eauto; subst.
    edestruct H as [? ?]; peauto.
    destruct av; intuition.
    destruct e; pseauto; contradiction.
  - (* fill_par nil good case 1 *)
    inv WT. intuition.
  - (* fill_par nil bad case 1 *)
    inv WT. inv TYPDECS. intuition.
  - (* fill_par nil bad case 2 *)
    inv TYPDECS. inv WT. intuition.
  - (* fill_par cons good case *)
    inv WT. destruct H3. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? [? ?]]]; peauto.
    edestruct H0 as [? ?]; pseauto.
  - (* fill_par cons bad case 1 *)
    inv WT. destruct H2. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? [VT' ?]]]; peauto.
    destruct q; inv VT'; auto.
  - (* fill_par cons bad case 2 *)
    inv WT. destruct H2. inv TYPDECS. destruct e.
    edestruct WB. left; auto. simpl in H1; subst.
    edestruct H as [? [? [? ?]]]; peauto.
    exfalso.
    edestruct good_frame_setSlot_sub with (h:=h1) (f:=fc) as [h' SS']; peauto.
    eapply SS; eauto.
  - (* fill_seq nil good case *)
    inv WB1. pseauto.
  - (* fill_seq nil bad case 1 *)
    inv WB1. intuition.
  - (* fill_seq nil bad case 2 *)
    inv WB1. intuition.
  - (* fill_seq cons good case *)
    inv WB1. destruct REL as [LKS [DS [ESEQ WB]]]. subst.
    inv WT. destruct H3; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DS; peauto; rewrite DS in SD; inv SD; auto); subst.
    edestruct H as [? [? [? ?]]]; peauto.
    assert (scopeofFrame h2 fc sd) by peauto.
    edestruct H0 as [? ?]; pseauto.
  - (* fill_seq cons bad case 1 *)
    inv WB1. destruct REL as [LKS [DS [ESEQ WB]]]. subst.
    inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DS; peauto; rewrite DS in SD; inv SD; auto); subst.
    edestruct H as [? [? [VT SUB']]]; peauto.
    destruct q; inv VT; peauto.
  - (* fill_seq cons bad case 2 *)
    inv WB1. destruct REL as [LKS [DS [ESEQ WB]]]. subst.
    inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
    destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
    assert (z' = sd) by
        (eapply declsofScope_scopeofDecl in DS; peauto; rewrite DS in SD; inv SD; auto); subst.
    edestruct H as [GH1 ?]; peauto.
    exfalso.
    edestruct good_frame_setSlot_sub with (h:=h2) (f:=fc) as [h' SS']; pseauto.
    eapply SS; eauto.
  - (* fill_rec nil bad case 1 *)
    intuition.
  - (* fill_rec nil bad case 1 *)
    inv WT. inv TYPDEC. intuition.
  - (* fill_rec nil bad case 2 *)
    inv TYPDEC. inv WT. intuition.
  - (* fill_rec cons good case *)
    inv WT. destruct H3 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    assert (X: exists ts0 ts1, y = Tarrow ts0 ts1) by (destruct y; inv ISFUN; eauto).
    destruct X as [? [? EQ]]; subst. simpl in *.
    edestruct H as [? [? [? ?]]]; peauto.
    edestruct H0 as [? ?]; pseauto.
  - (* fill_rec cons bad case 1 *)
    inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    assert (X: exists ts0 ts1, y = Tarrow ts0 ts1) by (destruct y; inv ISFUN; eauto).
    destruct X as [? [? EQ]]; subst. simpl in *.
    edestruct H as [? [? [VT' ?]]]; peauto.
    destruct q; inv VT'; eauto.
  - (* fill_rec cons bad case 2 *)
    inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
    edestruct WB as [EE WBE]; peauto; simpl in EE; subst.
    assert (X: exists ts0 ts1, y = Tarrow ts0 ts1) by (destruct y; inv ISFUN; eauto).
    destruct X as [? [? EQ]]; subst. simpl in *.
    edestruct H as [? [? [? ?]]]; peauto.
    exfalso.
    edestruct good_frame_setSlot_sub with (f:=frm) (h:=h1) as [f' SS']; peauto.
    eapply SS; eauto.
  - (* eval_lhs var good case *)
    inv WB; inv WT. split; auto.
    eapply scopeofRefDet in SR; eauto; subst.
    edestruct good_addr_sub as [? [ADDR' [SF' [? [DS IN]]]]]; eauto.
    eapply getAddrDet in ADDR; eauto; subst.
    eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
    eauto 6.
  - (* eval_lhs var bad case *)
    inv WB; inv WT. split; auto.
    eapply scopeofRefDet in SR; eauto; subst.
    eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
    edestruct good_addr_sub as [? [ADDR' _]]; peauto.
    intuition; eauto.
  - (* eval_lhs field good case *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? [VT' SUB']]]; peauto.
    eapply scopeofRefDet in SCR; eauto; subst.
    eapply linksofScopeDet in LS; eauto; inv LS.
    eapply rlookupDet in SR0; eauto. destruct SR0 as [? [? ?]]; subst.
    eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [EQ ASC']]]; subst.
    eapply sub_tclass in SUB'; eauto. destruct SUB' as [? [? [EQ' ASC'']]]; subst.
    eapply upcast_scopeofFrame in UPCAST.
    eapply linksofScopeDet in IMP; eauto; inv IMP.
    assert (good_sub_heap h2) by peauto.
    assert (scopeofFrame h2 imp_f s) by peauto.
    edestruct good_addr_sub as [? [ADDR' [SF' [? [DS IN]]]]]; eauto.
    eapply getAddrDet in ADDR; eauto; inv ADDR.
    split; eauto 6 with pres.
  - (* eval_lhs field good null case *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H; peauto.
  - (* eval_lhs field bad case 1 *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? [VT SUB']]]; peauto.
    eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [EQ ASC']]]; subst.
    eapply sub_tclass in SUB'; eauto. destruct SUB' as [? [? [EQ ASC'']]]; subst.
    destruct v; inv BAD; inv VT; simpl; peauto.
  - (* eval_lhs field bad case 2 *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? [VT SUB']]]; peauto.
    eapply scopeofRefDet in SCR; eauto; subst.
    eapply linksofScopeDet in LS; eauto; inv LS.
    eapply rlookupDet in SR0; eauto. destruct SR0 as [? [? ?]]; subst.
    inversion VT; subst.
    assert (UPCAST': sub' (Tclass d) (Tclass sd0)) by pseauto.
    edestruct sub_class_upcast as [? UPCAST'']; peauto.
    eapply linksofScopeDet in IMP; eauto; inv IMP.
    intuition eauto.
  - (* eval_lhs field bad case 3 *)
    inv WB; inv WT. destruct e; simpl in *; subst.
    edestruct H as [? [? [VT' SUB']]]; peauto.
    eapply scopeofRefDet in SCR; eauto; subst.
    eapply linksofScopeDet in LS; eauto; inv LS.
    eapply rlookupDet in SR0; eauto. destruct SR0 as [? [? ?]]; subst.
    eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [EQ ASC']]]; subst.
    eapply sub_tclass in SUB'; eauto. destruct SUB' as [? [? [EQ ASC'']]]; subst.
    eapply upcast_scopeofFrame in UPCAST.
    eapply linksofScopeDet in IMP; eauto; inv IMP.
    assert (good_sub_heap h2) by peauto.
    assert (scopeofFrame h2 imp_f s) by peauto.
    edestruct good_addr_sub as [? [ADDR' [SF' [? [DS IN]]]]]; eauto.
    exfalso.
    eapply ADDR; eauto.
  - (* eval_objinit good case 1 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    destruct ASR as [? [? [? [SR2 AS2]]]].
    eapply rlookupDet in SR2; eauto. destruct SR2 as [? [? ?]]; subst.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    inv VT. destruct OPTR as [SR' [? [? [? [DR' [ASCR [TDR IMSR]]]]]]]; subst.
    assert (sf = sp) by
        (eapply scopeofFrameDet; [eapply SF|eapply eval_objinit_scopeofFrame; eauto; eapply FS1]); subst.
    edestruct H0 as [GH2 VT2]; peauto.
    inv VT2.
    eapply assocScopeDet in ASCR; eauto; subst.
    eapply scopeofFrameDet in SFP; eauto; subst.
    inv SUB; [|inv SUB1].
    eapply assocScopeDet in AS2; eauto; subst.
    edestruct H1 as [GH' [X|X]]; peauto; inv X.
    intuition. econstructor; eauto. eapply assign_refs_scopeofFrame; peauto.
  - (* eval_objinit bad case 1 *)
    edestruct H as [GH' VT]; peauto. destruct v; inv BAD; try inv VT.
    destruct e; peauto.
  - (* eval_objinit bad case 2 *)
    edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; peauto.
    inv LHS.
    eapply getAddr_getSlot_sub in ADDR; peauto.
    destruct ADDR as [? [? [? [GS' [VT SUB]]]]].
    exfalso.
    eapply GS; eauto.
  - (* eval_objinit bad case 3 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    eapply sub_tclassdef in SUB; eauto. destruct SUB as [? EQ]; subst.
    inv VT; inv BAD; simpl; peauto.
  - (* eval_objinit bad case 4 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    inv VT. destruct OPTR as [SR' [? [? [? [DR' [ASCR [TDR IMSR]]]]]]]; subst.
    edestruct H0 as [GH2 VT2]; peauto.
    destruct v; try inv VT2; peauto.
  - (* eval_objinit bad case 5 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    destruct ASR as [? [? [? [SR2 AS2]]]].
    eapply rlookupDet in SR2; peauto. destruct SR2 as [? [? ?]]; subst.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    inv VT. destruct OPTR as [SR' [? [? [? [DR' [ASCR [TDR IMSR]]]]]]]; subst.
    assert (sf = sp) by
        (eapply scopeofFrameDet; [eapply SF|eapply eval_objinit_scopeofFrame; eauto; eapply FS1]); subst.
    edestruct H0 as [GH2 VT2]; peauto.
    inv VT2.
    eapply assocScopeDet in ASCR; eauto; subst.
    eapply scopeofFrameDet in SFP; eauto; subst.
    inv SUB; [|inv SUB1].
    eapply assocScopeDet in AS2; eauto; subst.
    edestruct H1 as [GH' [X|X]]; peauto; subst; inv BAD.
    intuition. econstructor; eauto.
  - (* eval_objinit no parent good case *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    destruct ASR as [? [? [? [SR2 AS2]]]].
    eapply rlookupDet in SR2; peauto. destruct SR2 as [? [? ?]]; subst.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    inv VT. inv SUB; [|inv SUB1].
    assert (sf = sp) by (eapply scopeofFrameDet; eauto); subst.
    eapply assocScopeDet in AS2; eauto; subst.
    edestruct H0 as [GH2 [X|X]]; peauto; inv X.
    intuition. econstructor; eauto. eapply assign_refs_scopeofFrame; peauto.
  - (* eval_objinit no parent bad case 1 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    inv LHS.
    eapply getAddr_getSlot_sub in ADDR; sgauto.
    destruct ADDR as [? [? [? [GS' [VT SUB]]]]].
    exfalso.
    eapply GS; eauto.
  - (* eval_objinit no parent bad case 2 *)
    edestruct H as [? [? [? [SF' [DS' [IN TD]]]]]]; peauto.
    destruct ASR as [? [? [? [SR2 AS2]]]].
    eapply rlookupDet in SR2; peauto. destruct SR2 as [? [? ?]]; subst.
    inv LHS.
    edestruct getAddr_typofDecl_getSlot_sub as [? [? [? [GET [VT [SUB TD']]]]]]; peauto.
    eapply getSlotDet in GS; eauto; subst.
    eapply typofDeclDet in TD; eauto; subst.
    inv VT. inv SUB; [|inv SUB1].
    assert (sf = sp) by (eapply scopeofFrameDet; eauto); subst.
    eapply assocScopeDet in AS2; eauto; subst.
    edestruct H0 as [GH2 [X|X]]; peauto; subst; inv BAD.
    simpl. intuition.
  - (* assign_refs nil case *)
    peauto.
  - (* assign_refs good case *)
    edestruct WBE; [econstructor; reflexivity|].
    inv WTE. destruct H6 as [? [? [? [? [? [? [RL [TD [SUB WT]]]]]]]]].
    destruct e; simpl in *; subst.
    edestruct H as [? [? [? ?]]]; peauto.
    edestruct H0; peauto.
    edestruct SR; eauto; subst.
    specialize (SR r (or_introl eq_refl)).
    eapply scopeofRefDet in SR; eauto; subst.
    edestruct (good_addr_sub _ h0) as [? [GA [SF EX]]]; peauto.
    eapply getAddrDet in ADDR; eauto. inv ADDR.
    eapply setSlot_good_heap_sub; eauto using sub_trans; peauto.
  - (* assign_refs bad case 1 *)
    inv WTE. destruct H; auto.
  - (* assign_refs bad case 2 *)
    inv WTE. destruct H; auto.
  - (* assign_refs bad case 3 *)
    edestruct WBE; [econstructor; reflexivity|].
    inv WTE. destruct H4 as [? [? [? [? [? [? [RL [TD [SUB WT]]]]]]]]].
    destruct e; simpl in *; subst.
    specialize (SR r (or_introl eq_refl)).
    eapply scopeofRefDet in SR; eauto; subst.
    edestruct (good_addr_sub _ h0) as [? [GA [SF EX]]]; peauto.
    exfalso. eapply ADDR; eauto.
  - (* assign_refs bad case 4 *)
    edestruct WBE; [econstructor; reflexivity|].
    inv WTE. destruct H5 as [? [? [? [? [? [? [RL [TD [SUB WT]]]]]]]]].
    destruct e; simpl in *; subst.
    edestruct H as [? [? [VT' SUB']]]; peauto.
    destruct q; inv VT'; eauto.
Qed.

Lemma init_decls_sound :
  forall
    h0 frm ds h1
    (IDs: init_decls h0 frm ds h1)
    s
    (WT: wt_decls ds)
    (WB: wb_decls s ds)
    (GH: good_sub_heap h0)
    (SF: scopeofFrame h0 frm s),
    good_sub_heap h1 /\ scopeofFrame h1 frm s.
Proof.
  induction 1; intros; eauto.
  inv WT; inv WB. rewrite <- EQ in EQ0. inv EQ0.
  assert (vtyp h0 (ConstructorV s rd optr (unzipf fds) frm) (TclassDef rd)).
  rewrite <- EQ. eapply assocScopeDet in SD; eauto; subst.
  econstructor; sgauto.
  destruct optr.
  destruct PARENT0 as [? [? [? [? [? [? [? ?]]]]]]].
  split; eauto 10. assumption.
  eapply IHIDs; eauto using setSlotScope, setSlot_good_heap.
  eapply setSlot_good_heap_sub; sgauto. simpl. constructor.
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
  assert (good_sub_heap emptyHeap) by inversion 1.
  assert (good_sub_heap h0) by (eapply initDefault_good_heap0_sub; peauto).
  edestruct init_decls_sound as [ID _]; eauto.
  destruct exp_preservation as [expP _].
  edestruct expP as [_ VT']; sgauto.
  intro; subst v. destruct VT' as [? [VT' _]]. inv VT'.
Qed.

End TypeSoundness.
