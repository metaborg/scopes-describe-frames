Require Export scopes maps.

(** * Frames and Heaps *)
Definition FrameId := nat.
Lemma FrameIdDec : forall (frm1 frm2:FrameId), {frm1 = frm2} + {frm1 <> frm2}.
Proof.
  repeat (decide equality).
Qed.

Class FrameHeap {V : Type} :=
  { Frame := ((ScopeId * (map EdgeLabel (map ScopeId FrameId)))%type * map D V)%type ;
    H := map FrameId Frame ;
    emptyHeap : H := empty ;
    frame (h: H) (f: FrameId) : Prop :=
      In f (keys h)
  }.


Section FrameHeapProperties.

  Variables (V: Type) (FH : @FrameHeap V).

  Inductive Addr :=  (* address within a frame *)
  | Addr_ : FrameId -> D -> Addr.

  Inductive scopeofFrame (h: H) (f: FrameId) (s: ScopeId) : Prop :=
  | scopeofFrame_ :
      forall ks slots,
        get FrameIdDec h f = Some (s, ks, slots) ->
        scopeofFrame h f s.

  Lemma scopeofFrameFrame :
    forall h f s,
      scopeofFrame h f s ->
      frame h f.
  Proof.
    inversion 1; unfold frame; eauto with maps.
  Qed.

  Lemma scopeofFrameDet :
    forall h f s,
      scopeofFrame h f s ->
      forall s',
        scopeofFrame h f s' ->
        s = s'.
  Proof.
    do 2 inversion 1. rewrite H3 in H1. inv H1; auto.
  Qed.

  Inductive linksofFrame (h: H) (f: FrameId) (ks: map EdgeLabel (map ScopeId FrameId)) : Prop :=
  | linksofFrame_ :
      forall s slots,
        get FrameIdDec h f = Some (s, ks, slots) ->
        linksofFrame h f ks.

  Inductive llinksofFrame (h: H) (f: FrameId) (l: EdgeLabel) (lks: map ScopeId FrameId) : Prop :=
  | llinksofFrame_ :
      forall ks,
        linksofFrame h f ks ->
        get ELdec ks l = Some lks ->
        llinksofFrame h f l lks.

  Lemma linksofFrameDet :
    forall ks ks' h f ,
      linksofFrame h f ks ->
      linksofFrame h f ks' -> ks = ks'.
  Proof.
    induction ks; intros.
    - inv H0. inv H1. rewrite H0 in H2. inv H2; eauto.
    - inv H0. inv H1. rewrite H0 in H2. inv H2; eauto.
  Qed.

  Lemma llinksofFrameDet :
    forall ks ks' h f l,
      llinksofFrame h f l ks ->
      llinksofFrame h f l ks' -> ks = ks'.
  Proof.
    induction ks; intros.
    - inv H0. inv H1.
      eapply linksofFrameDet in H2; eauto; subst.
      rewrite H4 in H3. inv H3; eauto.
    - inv H0. inv H1.
      eapply linksofFrameDet in H2; eauto; subst.
      rewrite H4 in H3. inv H3; eauto.
  Qed.

  Lemma emptyHeapNoFrames :
    forall f,
      ~ frame emptyHeap f.
  Proof.
    intros. intro. unfold frame, emptyHeap in H0. simpl in H0. auto.
  Qed.

  (** Adding a new frame: *)
  Definition newFrame
            (h: H)
            (s: ScopeId)
            (ks: map EdgeLabel (map ScopeId FrameId))
            (f: FrameId)
            (h': H) : Prop :=
    ~ In f (keys h) /\
    h' = set FrameIdDec h f (s, ks, empty).

  Lemma newFrameNew :
    forall h0 s ks f h1,
      newFrame h0 s ks f h1 ->
      ~ frame h0 f.
  Proof.
    intros. inv H0. auto.
  Qed.

  Lemma newFrameFrames :
    forall h0 s ks f0 h1,
      newFrame h0 s ks f0 h1 ->
      forall f,
        frame h1 f <-> f = f0 \/ frame h0 f.
  Proof.
    intros. inv H0. split; intros.
    unfold frame in H1.
    eapply in_keys_set; eauto.
    eapply set_in_keys; eauto.
  Qed.

  Lemma newFrameSame :
    forall h0 s ks frm h1,
      newFrame h0 s ks frm h1 ->
      get FrameIdDec h1 frm = Some (s, ks, []).
  Proof.
    intros. inv H0. eapply get_set_same.
  Qed.

  Lemma newFrameDiff :
    forall h0 f0 s0 ks0 slots0 s ks f h1,
      get FrameIdDec h0 f0 = Some (s0, ks0, slots0) ->
      (* NB. Do not require frm0 <> frm1 *)
      newFrame h0 s ks f h1 ->
      get FrameIdDec h1 f0 = Some (s0, ks0, slots0).
  Proof.
    intros. inv H1. inv H0. rewrite get_set_other; eauto.
    intro; subst. eapply keys_in in H3. contradiction.
  Qed.

  Lemma newFrameDiff' :
    forall h0 s frm0 frm1 h1 ks ds s' ks',
      get FrameIdDec h1 frm0 = Some (s, ks, ds) ->
      frm0 <> frm1 ->
      newFrame h0 s' ks' frm1 h1 ->
      get FrameIdDec h0 frm0 = Some (s, ks, ds).
  Proof.
    intros. inv H2. rewrite get_set_other in H0; eauto.
  Qed.

  (** Removing a frame: *)
  Definition removeFrame (h0: H) (f:FrameId) (h1: H) : Prop :=
    h1 = remove FrameIdDec h0 f.

  Lemma removeFrameFrames0:
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      (frame h1 f0 <-> (f <> f0 /\ frame h0 f0)).
  Proof.
    intros. unfold frame. inv H0. split; intros. apply in_keys_remove in H0. intuition.
    eapply remove_in_keys; intuition.
  Qed.

  Lemma removeFrameFrames:
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      f <> f0 ->
      frame h0 f0 ->
      frame h1 f0.
  Proof.
    unfold frame; intros. inv H0. eapply remove_in_keys; eauto.
  Qed.

  Lemma removeFrameFrames':
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      frame h1 f0 ->
      (f <> f0 /\ frame h0 f0).
  Proof.
    unfold frame; intros. inv H0. apply in_keys_remove in H1. intuition.
  Qed.

  Lemma removeFrameSame :
    forall h0 frm0 s0 ks0 slots0 h1 frm,
      removeFrame h0 frm h1 ->
      (get FrameIdDec h1 frm0 = Some (s0, ks0, slots0) <->
       (get FrameIdDec h0 frm0 = Some (s0, ks0, slots0) /\ frm <> frm0)).
  Proof.
    intros. split; intros.
      inv H1. inv H0.
        destruct (FrameIdDec frm frm0); subst.
          rewrite get_remove_same in H3. inv H3.
          rewrite get_remove_other in H3; eauto.
        erewrite get_remove_other; eauto.
      inv H0. inv H1; eauto.
      rewrite get_remove_other; eauto.
  Qed.

  Lemma removeFrameScope:
    forall h0 frm0 s0 h1 frm,
      removeFrame h0 frm h1 ->
      (scopeofFrame h1 frm0 s0 <-> (scopeofFrame h0 frm0 s0 /\ frm <> frm0)).
  Proof.
    intros. split;intros.
      inv H1. eapply removeFrameSame in H2; eauto. destruct H2. split; eauto.
        econstructor; eauto.
      destruct H1. inv H1.  econstructor. eapply removeFrameSame; eauto.
  Qed.



  (** Removing multiple frames: *)
  Inductive removeFrames : H -> list FrameId -> H -> Prop :=
  | rfs_nil :
      forall h0, removeFrames h0 [] h0
  | rfs_cons :
      forall h0 h1 h2 f fs,
        removeFrame h0 f h1 ->
        removeFrames h1 fs h2 ->
        removeFrames h0 (f::fs) h2.

  Lemma removeFramesFrames :
    forall h0 fs h1 f0,
      removeFrames h0 fs h1 -> (frame h1 f0 <-> (~ In f0 fs /\ frame h0 f0)).
  Proof.
    intros.
    induction H0; intros.
    intuition.
    eapply removeFrameFrames0 with (f0:=f0) in H0.
    split; intros.
    rewrite IHremoveFrames in H2.  destruct H2.  rewrite H0 in H3.  destruct H3.
    split; auto.  intro; exfalso. inv H5. eapply H3; eauto. eapply H2; contradiction.
    rewrite IHremoveFrames. destruct H2. split.  intro. apply H2. right; auto.
    eapply H0. split; auto. intro; eapply H2; left; auto.
  Qed.

  Lemma removeFramesSame :
    forall h0 frm0 s0 h1 frms ks0 slots0,
      removeFrames h0 frms h1 ->
      (get FrameIdDec h1 frm0 = Some (s0, ks0, slots0) <->
       (~ In frm0 frms /\ get FrameIdDec h0 frm0 = Some (s0, ks0, slots0))).
  Proof.
    intros. induction H0; intros.
    intuition.
    eapply removeFrameSame with (frm0:=frm0) (s0:=s0) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0. split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  Lemma removeFramesScope: forall h0 frm0 s0 h1 frms,
                            removeFrames h0 frms h1 ->
                            (scopeofFrame h1 frm0 s0 <-> (~ In frm0 frms /\ scopeofFrame h0 frm0 s0)).
  Proof.
    intros. induction H0; intros.
    intuition.
    eapply removeFrameScope with (frm0 := frm0) (s0:=s0) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0.  split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  (** Setting a slot: *)
  Inductive setSlot (h: H) (f:FrameId) (d:D) (v:V) (h': H) : Prop :=
  | setSlot_ :
      forall
        scope links slots slots',
        In d (keys slots) ->
        get FrameIdDec h f = Some (scope, links, slots) ->
        slots' = set Ddec slots d v ->
        h' = set FrameIdDec h f (scope, links, slots') ->
        setSlot h f d v h'.

  Lemma setSlotFrame :
    forall h0 f d v h1,
      setSlot h0 f d v h1 ->
      frame h0 f.
  Proof.
    intros. inv H0. apply keys_in in H2. auto.
  Qed.

  Lemma setSlotFrames :
    forall h0 d v h1 f0,
      setSlot h0 f0 d v h1 ->
      forall f,
        frame h0 f <-> frame h1 f.
  Proof.
    intros. split; intros.
      inv H0. eapply set_in_keys. auto.
      inv H0.
       unfold frame in H1; apply in_keys_set in H1. inv H1; subst.
       eapply keys_in; eauto.
       auto.
  Qed.

  (** Getting all slots: *)
  Inductive getSlots (heap: H) (f: FrameId) (slots:map D V) : Prop :=
  | getSlots_ : forall
      scope links,
      get FrameIdDec heap f = Some (scope, links, slots) ->
      getSlots heap f slots.

  (** Getting a slot: *)
  Inductive getSlot (heap: H) (f: FrameId) (d: D) (v: V) : Prop :=
  | getSlot_ : forall
      scope links slots,
      get FrameIdDec heap f = Some (scope, links, slots) ->
      Some v = get Ddec slots d ->
      getSlot heap f d v.

  Lemma getSlotFrame :
    forall h f d v,
      getSlot h f d v ->
      frame h f.
  Proof.
    intros. inv H0. eapply keys_in; eauto.
  Qed.

  Lemma getSlotDet:
    forall h f d v1 v2,
      getSlot h f d v1 ->
      getSlot h f d v2 ->
      v1 = v2.
  Proof.
    intros. inv H0.  inv H1.
    rewrite H0 in H2; inv H2. rewrite <- H4 in H3; inv H3; auto.
  Qed.

  Lemma getSlotsDet:
    forall h f slots1 slots2,
      getSlots h f slots1 ->
      getSlots h f slots2 ->
      slots1 = slots2.
  Proof.
    intros. inv H0.  inv H1.
    rewrite H0 in H2; inv H2; auto.
  Qed.

  Lemma newFrameSlotSame :
    forall s frm h0 h1 d v ks,
      newFrame h0 s ks frm h1 ->
      ~ getSlot h1 frm d v.
  Proof.
    intros. inv H0. intro. inv H0. rewrite get_set_same in H2. inv H2. inv H3.
  Qed.

  Lemma newFrameSlotDiff :
    forall s frm0 frm1 h0 h1 d v ks,
      getSlot h0 frm0 d v ->
      newFrame h0 s ks frm1 h1 ->
      getSlot h1 frm0 d v .
  Proof.
    intros. inv H1. inv H0. econstructor; eauto. rewrite get_set_other; eauto.
    eapply keys_in in H1. intro; subst; contradiction.
  Qed.

  Lemma newFrameSlotDiff':
    forall s frm0 frm1 h0 h1 d v ks,
      getSlot h1 frm0 d v ->
      newFrame h0 s ks frm1 h1 ->
      frm0 <> frm1 ->
      getSlot h0 frm0 d v .
  Proof.
    intros. inv H1. inv H0. rewrite get_set_other in H1; auto.
    econstructor; eauto.
  Qed.

  Lemma removeFrameSlot :
    forall h0 f0 d v f h1,
      removeFrame h0 f h1 ->
      (getSlot h1 f0 d v <-> (getSlot h0 f0 d v /\ f <> f0)).
  Proof.
    intros. inv H0. split; intros.
      inv H0. inv H1. destruct (FrameIdDec f f0); subst.
        rewrite get_remove_same in H3; inv H3.
        rewrite get_remove_other in H3; eauto. split; eauto.
    inv H3. inv H2; econstructor; eauto.
    inv H0. inv H1.
    econstructor; eauto. erewrite get_remove_other; eauto.
  Qed.

  Lemma removeFramesSlot :
    forall h0 f0 d v fs h1,
      removeFrames h0 fs h1 ->
      (getSlot h1 f0 d v <-> (~ In f0 fs /\ getSlot h0 f0 d v)).
  Proof.
    intros.
    induction H0.
    intuition.
    eapply removeFrameSlot with (h0:= h0) (f := f) (h1:=h1) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0.  split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  Lemma setSlotSlotSame:
    forall frm d v h0 h1,
      setSlot h0 frm d v h1 ->
      getSlot h1 frm d v.
  Proof.
    intros. inv H0. econstructor.
    rewrite get_set_same; eauto.
    rewrite get_set_same; auto.
  Qed.

  Lemma setSlotSlotDiff :
    forall frm0 frm1 d0 d1 v0 v1 h0 h1,
      getSlot h0 frm0 d0 v0 ->
      setSlot h0 frm1 d1 v1 h1 ->
      frm1 <> frm0 \/  d1 <> d0 ->
      getSlot h1 frm0 d0 v0.
  Proof.
    intros. inv H0. inv H1. destruct H2.
      econstructor; eauto. rewrite get_set_other; eauto.
      destruct (FrameIdDec frm1 frm0); subst.
        rewrite H3 in H5; inv H5.
        econstructor. rewrite get_set_same; eauto.
          rewrite get_set_other; eauto.
        econstructor; eauto. rewrite get_set_other; eauto.
  Qed.

  Lemma setSlotSlotDiff' :
    forall frm0 frm1 d0 d1 v0 v1 h0 h1,
      setSlot h0 frm1 d1 v1 h1 ->
      getSlot h1 frm0 d0 v0 ->
      frm1 <> frm0 \/  d1 <> d0 ->
      getSlot h0 frm0 d0 v0.
  Proof.
    intros. inv H0. inv H1. destruct H2.
    rewrite get_set_other in H0.
    econstructor; eauto.  intro. subst. apply H1; auto.
    destruct (FrameIdDec frm1 frm0); subst.
    rewrite get_set_same in H0. inv H0; subst.
    econstructor; eauto.
    rewrite get_set_other in H5.  eauto. intro. subst. apply H1; auto.
    rewrite get_set_other in H0. econstructor; eauto.
    intro. subst. apply n; auto.
  Qed.

  Lemma setSlotSame :
    forall h0 frm0 frm1 d v h1 scope links slots,
      setSlot h0 frm1 d v h1 ->
      get FrameIdDec h0 frm0 = Some (scope, links, slots) ->
      exists slots, get FrameIdDec h1 frm0 = Some (scope, links, slots).
  Proof.
    intros. inv H0.
    destruct (FrameIdDec frm1 frm0); subst.
      unfold Frame in *; rewrite H1 in H3; inv H3. rewrite get_set_same. eexists; eauto.
      rewrite get_set_other. eexists; eauto. intuition.
  Qed.

  Lemma setSlotSame' :
    forall h0 frm0 frm1 d v h1 scope links slots,
      get FrameIdDec h1 frm0 = Some (scope, links, slots) ->
      setSlot h0 frm1 d v h1 ->
      exists slots, get FrameIdDec h0 frm0 = Some (scope, links, slots).
  Proof.
    intros. inv H1.
    destruct (FrameIdDec frm1 frm0); subst.
      rewrite get_set_same in H0. inv H0; eauto.
      rewrite get_set_other in H0. eexists; eauto. intuition.
  Qed.

  (** Dynamic lookup. *)
  Inductive lookup (h: H) : FrameId -> path -> FrameId -> Prop :=
  | lookupD : forall f d,
      lookup h f (Dp d) f
  | lookupI : forall
      f p f' f'' l s ks
      (IMS: llinksofFrame h f l ks)
      (S: get ScopeIdDec ks s = Some f')
      (REST: lookup h f' p f''),
      lookup h f (Ep l s p) f''
  .

  Lemma lookupDet: forall h f p f1,
      lookup h f p f1 ->
      forall f2,
        lookup h f p f2 -> f1 = f2.
  Proof.
    induction 1; intros.
    - inv H0; auto.
    - inv H1. eapply llinksofFrameDet in IMS; eauto; subst.
      rewrite S in S0; inv S0; eauto.
  Qed.

  Section CombiningStaticAndDynamic.

    Context {G : Graph} (C: WellConnected G).

    Inductive getAddr (h: H) (f: FrameId) (r: R) : Addr -> Prop :=
    | getAddr_ :
        forall
          p f' d
          (PATH: pathofRefP C r p)
          (LK: lookup h f p f'),
          d = declofPath p ->
        getAddr h f r (Addr_ f' d).

    Lemma getAddrDet :
      forall h f r a1 a2,
        getAddr h f r a1 ->
        getAddr h f r a2 ->
        a1 = a2.
    Proof.
      intros. inv H0.  inv H1.
      pose proof (pathofRefDet _ _ _ PATH _ PATH0). subst p0. clear PATH0.
      f_equal.
      eapply lookupDet; eauto.
    Qed.

    (** Some useful utilities. *)
    Inductive getRef (h: H) (f:FrameId) (r: R) (v: V) : Prop :=
    | getRef_ : forall
        ff d
        (ADDR: getAddr h f r (Addr_ ff d))
        (SLOT: getSlot h ff d v),
        getRef h f r v.

    Lemma getRefDet :
      forall h f r v1 v2,
        getRef h f r v1 -> getRef h f r v2 -> v1 = v2.
    Proof.
      intros. inv H0. inv H1.
      pose proof (getAddrDet _ _ _ _ _ ADDR ADDR0). inv H0. clear ADDR0.
      eapply getSlotDet; eauto.
    Qed.

    (* Inductive fillFrame (f: FrameId) : H -> map D V -> H -> Prop := *)
    (* | ff_nil : forall h, fillFrame f h nil h *)
    (* | ff_cons: forall h0 h1 h2 d slots v, *)
    (*     setSlot h0 f d v h1 -> *)
    (*     fillFrame f h1 slots h2 -> *)
    (*     fillFrame f h0 ((d,v)::slots) h2. *)
    Definition fillFrame (f: FrameId) (h0: H) (slots: map D V) (h1: H) : Prop :=
      exists s ks slots0,
        get FrameIdDec h0 f = Some (s, ks, slots0) /\
        h1 = set FrameIdDec h0 f (s, ks, slots).

    Lemma fillFrameFrames :
      forall f0 h0 slots h1,
        fillFrame f0 h0 slots h1 ->
        forall f, frame h0 f <-> frame h1 f.
    Proof.
      intros. destruct H0 as [? [? [? [GF SF]]]]. subst.
      split; unfold frame; intro. simpl.
      destruct (FrameIdDec f0 f); auto. right.
      eapply dom_remove'; eauto.
      destruct (FrameIdDec f0 f); auto.
      simpl in H0. inv H0. eapply keys_in; eauto. eapply keys_in; eauto.
      simpl in H0. inv H0; [intuition|]. eapply dom_remove; eauto.
    Qed.

    Hint Resolve fillFrameFrames : sgraph.

(* APT: While we're doing this much rework, we
   should be consistent about whether to have primed versions or <-> versions.
   (I suspect that former are a bit easier to work with.)
   Also: We should consistently put the "action" hypothesis about state change
         (e.g. fillFrame in this case) FIRST, because this generally makes eauto work better.
         So, e.g. fillFrameSame is good in this respect, but fillFrameSlotDiff is not.
*)

    Lemma fillFrameSame :
      forall
        h0 f slots h1
        (FF: fillFrame f h0 slots h1)
        scope links slots0
        (GF: get FrameIdDec h0 f = Some (scope, links, slots0)),
      get FrameIdDec h1 f = Some (scope, links, slots).
    Proof.
      intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
      rewrite get_set_same. rewrite GF in GF'. inv GF'; auto.
    Qed.

    Lemma fillFrameSame' :
      forall
        h0 f slots h1
        (FF: fillFrame f h0 slots h1)
        scope links slots
        (GF: get FrameIdDec h1 f = Some (scope, links, slots)),
      exists slots', get FrameIdDec h0 f = Some (scope, links, slots').
    Proof.
      intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
      rewrite get_set_same in GF. inv GF. eauto.
    Qed.

    Hint Resolve fillFrameSame' : sgraph.

    Lemma fillFrameDiff :
      forall
        h0 f1 slots h1
        (FF: fillFrame f1 h0 slots h1)
        f0 scope links slots
        (NEQ: f0 <> f1)
        (GF: get FrameIdDec h0 f0 = Some (scope, links, slots)),
        get FrameIdDec h1 f0 = Some (scope, links, slots).
    Proof.
      intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
      rewrite get_set_other; auto.
    Qed.

    Lemma fillFrameDiff' :
      forall
        h0 f1 slots h1
        (FF: fillFrame f1 h0 slots h1)
        f0 scope links slots
        (NEQ: f0 <> f1)
        (GF: get FrameIdDec h1 f0 = Some (scope, links, slots)),
        get FrameIdDec h0 f0 = Some (scope, links, slots).
    Proof.
      intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
      rewrite get_set_other in GF; auto.
    Qed.

    Lemma fillFrameSlotDiff :
      forall h0 f0 d v f1 h1 slots,
        fillFrame f1 h0 slots h1 ->
        getSlot h0 f0 d v ->
        f0 <> f1 (* \/ ~ In d (keys slots) *) -> (* Shouldn't be the case if we insist the domain of frames is statically determined *)
        getSlot h1 f0 d v.
    Proof.
      intros. inversion H0 as [? [? [? [GF' SF]]]]. subst.
      inv H1. econstructor. rewrite get_set_other; eauto. assumption.
    Qed.

    Lemma fillFrameSlotDiff' :
      forall h0 f0 d v f1 h1 slots,
        fillFrame f1 h0 slots h1 ->
        getSlot h1 f0 d v ->
        f0 <> f1 (* \/ ~ In d (keys slots) *) ->
        getSlot h0 f0 d v.
    Proof.
      intros; inversion H0 as [? [? [? [GF' SF]]]]. subst.
      inv H1. rewrite get_set_other in H3; eauto. econstructor; eauto.
    Qed.

    (* Create and fully initialize a frame from a list of values. *)
    Inductive initNewFrame
              (h1: H)
              (s: ScopeId)
              (ks: map EdgeLabel (map ScopeId FrameId))
              (slots: map D V)
              (f: FrameId)
              (h3: H) : Prop :=
    | initNewFrame_ : forall
        h2
        (NF: newFrame h1 s ks f h2)
        ds
        (DS: declsofScopeP C s ds)
        (FF: fillFrame f h2 slots h3),
        initNewFrame h1 s ks slots f h3.

    Lemma initNewFrameFrames :
      forall h0 s ks vs f0 h1,
        initNewFrame h0 s ks vs f0 h1 ->
        forall f, f = f0 \/ frame h0 f  <-> frame h1 f.
    Proof.
      intros. inv H0. eapply iff_trans.
      eapply iff_sym. eapply newFrameFrames; eauto.
      eapply fillFrameFrames; eauto.
    Qed.

    Lemma initNewFrameSame :
      forall h0 s ks vs f0 h1,
        initNewFrame h0 s ks vs f0 h1 ->
        exists slots, get FrameIdDec h1 f0 = Some (s, ks, slots).
    Proof.
      intros. inversion H0.
      eapply newFrameSame in NF; eauto. inv NF.
      eapply fillFrameSame in FF; eauto.
    Qed.

    Lemma initNewFrameDiff :
      forall h0 f0 s ks slots f h1 s' ks' vs',
        initNewFrame h0 s' ks' vs' f h1 ->
        get FrameIdDec h0 f0 = Some (s, ks, slots) ->
        get FrameIdDec h1 f0 = Some (s, ks, slots).
    Proof.
      intros. inv H0.
      assert (get FrameIdDec h2 f0 = Some (s, ks, slots)).
      eapply newFrameDiff; eauto. inv NF.
      eapply fillFrameDiff; eauto.
      intro. subst. eapply keys_in in H1. contradiction.
    Qed.

    Lemma initNewFrameDiff' :
      forall h0 f0 s ks slots f h1 s' ks' vs',
        initNewFrame h0 s' ks' vs' f h1 ->
        get FrameIdDec h1 f0 = Some (s, ks, slots) ->
        f <> f0 ->
        get FrameIdDec h0 f0 = Some (s, ks, slots).
    Proof.
      intros. inv H0.
      eauto using fillFrameDiff', newFrameDiff'.
    Qed.

    Lemma initNewFrameSlotDiff' :
      forall f0 d v f h1 vs ks s h0,
        initNewFrame h0 s ks vs f h1 ->
        getSlot h1 f0 d v ->
        f0 <> f ->
        getSlot h0 f0 d v.
    Proof.
      intros. inv H0.
      eapply newFrameSlotDiff'. 2: eauto. 2: auto. eapply fillFrameSlotDiff'; eauto.
    Qed.

    Section Sugar.

      Lemma initNewFrameSame_scopeofFrame :
        forall h0 s ks vs f0 h1,
          initNewFrame h0 s ks vs f0 h1 ->
          scopeofFrame h1 f0 s.
      Proof.
        intros. eapply initNewFrameSame in H0. inv H0; econstructor; eauto.
      Qed.

      Lemma initNewFrameDiff_scopeofFrame :
        forall h0 f0 s f h1 s' ks' vs',
          initNewFrame h0 s' ks' vs' f h1 ->
          scopeofFrame h0 f0 s ->
          scopeofFrame h1 f0 s.
      Proof.
        intros. inv H1. eapply initNewFrameDiff in H2; eauto; inv H2; econstructor; eauto.
      Qed.

      Lemma setSlotScope :
        forall
          h0 frm0 frm1 s d v h1,
          setSlot h0 frm1 d v h1 ->
          scopeofFrame h0 frm0 s ->
          scopeofFrame h1 frm0 s.
      Proof.
        inversion 1; intros; subst.
        eapply setSlotSame in H0; eauto.
        destruct H0. inv H5. destruct (FrameIdDec frm0 frm1). subst.
        rewrite H3 in H2; inv H2. econstructor; eauto.
        econstructor. rewrite get_set_other; eauto.
      Qed.

    End Sugar.

  End CombiningStaticAndDynamic.

End FrameHeapProperties.


Class VTyp {T V: Type} :=
  { dwc : @WCGAT T ;
    fh : @FrameHeap V ;
    vtyp : H -> V -> T -> Prop ;
    setSlot_vtyp :
      forall
        h0 f d v h1 v0 t0
        (SET: setSlot V fh h0 f d v h1)
        (VT: vtyp h0 v0 t0),
        vtyp h1 v0 t0 ;
    newFrame_vtyp :
      forall
        h0 s f h1 ks v0 t0
        (NF: newFrame V fh h0 s ks f h1)
        (VT: vtyp h0 v0 t0),
        vtyp h1 v0 t0 ;
    fillFrame_vtyp :
      forall
        slots f h1 h2 v0 t0
        (FF: fillFrame V fh f h1 slots h2)
        (VT: vtyp h1 v0 t0),
        vtyp h2 v0 t0;
  }.

Class DefaultVTyp {T V: Type} {VT: @VTyp T V} :=
  { default : T -> V -> Prop ;
    default_vtyp :
      forall v t,
        default t v -> forall h, vtyp h v t

  }.

Section VTypProperties.

  Variables (T V: Type) (VT : @VTyp T V).

  Lemma initNewFrame_vtyp :
    forall
      h0 s ks slots f h1 v0 t0
      (INF: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
      (VTYP: (@vtyp T V VT) h0 v0 t0),
      (@vtyp T V VT) h1 v0 t0.
  Proof.
    inversion 1; intros. eapply fillFrame_vtyp; eauto. eapply newFrame_vtyp; eauto.
  Qed.


  (** Good frame properties *)

  (* APT: Ideally, well_bound should not mention T *)
  Inductive well_bound (h: @H V fh) (f: FrameId) : Prop :=
  | well_bound_ :
      forall
        s
        (SC: scopeofFrame V fh h f s)
        (** WellBound declarations *)
        (DSS: forall ds,
            ddataofScopeP (@wc T dwc) s ds ->
            exists slots, getSlots V fh h f slots /\ DomEq slots ds)
        (DSF: forall slots,
            getSlots V fh h f slots ->
            exists ds, ddataofScopeP (@wc T dwc) s ds /\ DomEq slots ds)
        (** WellBound links: *)
        (LNS: forall l ss,
            llinksofScopeP (@g gat (@wc T dwc)) s l ss ->
            exists ks,
              llinksofFrame V fh h f l ks /\
              keys ks = ss /\
              forall s,
                In s ss ->
                exists f', get ScopeIdDec ks s = Some f' /\
                           scopeofFrame V fh h f' s)
        (LNF: forall l ks,
            llinksofFrame V fh h f l ks ->
            llinksofScopeP (@g gat (@wc T dwc)) s l (keys ks)),
        well_bound h f.

  Inductive well_typed (h: @H V fh) (f: FrameId) : Prop :=
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
            vtyp h v t),
        well_typed h f.

  Definition good_frame h f := well_bound h f /\ well_typed h f.
  Definition good_heap h := forall f, frame h f -> good_frame h f.

End VTypProperties.

Section DefaultVTypProperties.

  Context {T V: Type} {VT: @VTyp T V} (DVT : @DefaultVTyp T V VT).

  Definition DVT2VT : @DefaultVTyp T V VT -> @VTyp T V.
  Proof. destruct 1; eauto. Defined.

  Inductive defaults (s: ScopeId) : map D V -> Prop :=
  | defaults_nil : defaults s []
  | default_cons :
      forall
        d slots t v
        (TD: typofDecl T dwc s d t)
        (DF: default t v)
        (TAIL: defaults s slots),
        defaults s ((d,v) :: slots).

  Lemma defaults_vtyp :
    forall
      s slots
      (DF: defaults s slots)
      ts
      (TDs: typofDecls T dwc s (keys slots) ts)
      h,
      Forall2 (fun dv t =>
                 match dv, t with
                 | (_, v), t =>
                   vtyp h v t
                 end) slots ts.
  Proof.
    induction 1; intros. inv TDs; eauto.
    inv TDs. eapply typofDeclDet in TD; eauto; subst.
    eapply default_vtyp in DF; eauto.
  Qed.

  Lemma defaults_vtyp' :
    forall
      s slots
      (DF: defaults s slots),
    forall d t v,
      In d (keys slots) ->
      typofDecl T dwc s d t ->
      get Ddec slots d = Some v ->
      forall h,
        vtyp h v t.
  Proof.
    induction 1; intros.
    - inv H0.
    - simpl in *. destruct (Ddec d d0); subst.
      eapply typofDeclDet in H1; eauto; subst.
      destruct (Ddec d0 d0); inv H2; auto. apply default_vtyp; auto. intuition.
      destruct H0; [contradiction|]. destruct (Ddec d0 d); subst; [intuition|].
      eauto.
  Qed.

  Inductive initNewDefaultFrame
            (h0: @H V fh)
            (s: ScopeId) (ks: map EdgeLabel (map ScopeId FrameId))
            (f: FrameId) (h1: @H V fh) : Prop :=
  | initNewDefaultFrame_ : forall
      slots
      (DS: declsofScopeP (@wc T dwc) s (keys slots))
      (DF: defaults s slots)
      (NF: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1),
      initNewDefaultFrame h0 s ks f h1.

  Lemma initNewDefaultFrameFrames :
    forall h0 s ks f0 h1,
      initNewDefaultFrame h0 s ks f0 h1 ->
      forall f, f = f0 \/ frame h0 f <-> frame h1 f.
  Proof.
    inversion 1; eauto using initNewFrameFrames.
  Qed.

  Lemma initNewDefaultFrameSame :
    forall h0 s ks f h1,
      initNewDefaultFrame h0 s ks f h1 ->
      exists slots, get FrameIdDec h1 f = Some (s, ks, slots).
  Proof.
    intros. inv H0. eauto using initNewFrameSame.
  Qed.

  Lemma initNewDefaultFrameDiff :
    forall h0 f0 s ks slots f h1 s' ks',
      get FrameIdDec h0 f0 = Some (s, ks, slots) ->
      initNewDefaultFrame h0 s' ks' f h1 ->
      get FrameIdDec h1 f0 = Some (s, ks, slots).
  Proof.
    inversion 2; eauto using initNewFrameDiff.
  Qed.

  (* Derived properties: *)

  Lemma initNewDefaultFrameScope :
    forall h0 f0 s0 s ks f h1,
      initNewDefaultFrame h0 s ks f h1 ->
      scopeofFrame V fh h0 f0 s0 ->
      scopeofFrame V fh h1 f0 s0.
  Proof.
    inversion 2; intros.
    inv H0. inv NF. inv NF0. inv FF. destruct H3 as [? [? [GF HS]]]; subst.
    rewrite get_set_same in GF. inv GF. eapply declsofScopeDet in DS; eauto; subst.
    destruct (FrameIdDec f0 f). subst. apply keys_in in H2. contradiction.
    econstructor.
    rewrite get_set_other; eauto.
    rewrite get_set_other; eauto.
  Qed.

  (* inconsistent naming *)
  Lemma initNewDefaultFrameSame_scopeofFrame :
    forall h0 s ks f0 h1,
      initNewDefaultFrame h0 s ks f0 h1 ->
      scopeofFrame V fh h1 f0 s.
  Proof.
    intros. inv H0. eapply initNewFrameSame in NF. inv NF; econstructor; eauto.
  Qed.

  Lemma initNewDefaultFrame_vtyp: forall
      h0 s ks f h1 v0 t0
      (INF: initNewDefaultFrame h0 s ks f h1)
      (VT: vtyp h0 v0 t0),
      vtyp h1 v0 t0.
  Proof.
    inversion 1; intros; eauto using initNewFrame_vtyp.
  Qed.

End DefaultVTypProperties.

Hint Constructors Addr : sgraph.
Hint Constructors getAddr : sgraph.
Hint Constructors getSlots : sgraph.
Hint Constructors getSlot : sgraph.
Hint Constructors typofDecl : sgraph.
Hint Constructors scopeofFrame : sgraph.
Hint Constructors linksofFrame : sgraph.
Hint Constructors llinksofFrame : sgraph.
(* Hint Constructors ddataofScopeP : sgraph. *)
(* Hint Constructors declsofScopeP : sgraph. *)
Hint Constructors lookup : sgraph.
Hint Constructors well_bound : sgraph.
Hint Constructors well_typed : sgraph.

Hint Resolve scopeofFrameFrame : sgraph.
Hint Resolve setSlotSlotSame : sgraph.
Hint Resolve getAddrDet : sgraph.
Hint Resolve getRefDet : sgraph.
Hint Resolve fillFrameSame : sgraph.
Hint Resolve fillFrameDiff : sgraph.
Hint Resolve fillFrameDiff : sgraph.

Hint Resolve initNewFrameSame_scopeofFrame : sgraph.
Hint Resolve initNewFrameSame : sgraph.
Hint Resolve initNewFrameDiff_scopeofFrame : sgraph.
Hint Resolve initNewFrameDiff : sgraph.
Hint Resolve initNewFrameSlotDiff' : sgraph.
Hint Resolve setSlotScope : sgraph.
Hint Resolve initNewDefaultFrameScope : sgraph.

Hint Unfold declsofScopeP : sgraph.
Hint Unfold pathofRefP : sgraph.
Hint Unfold DomEq : sgraph.

Ltac sgauto := autounfold with sgraph; eauto with sgraph.
Ltac sgauto_force := autounfold with sgraph; eauto 7 with sgraph.

Lemma well_bound_get :
  forall T V (VT: @VTyp T V) h f s d ds
   (WB: well_bound T V VT h f)
   (SF: scopeofFrame V fh h f s) 
   (DS: declsofScopeP (@wc T dwc) s ds)
   (IN: In d ds),
    exists v, getSlot V fh h f d v.
Proof.
  intros. inv WB. 
  eapply scopeofFrameDet in SF; eauto; subst. 
  inv DS. inv H0. 
  edestruct DSS as [slots [GS DE]]; eauto.  
  inv GS. 
  assert (In d (keys slots)) by (apply DE; auto). 
  eapply in_keys in H2. destruct H2 as [v P].  
  exists v; econstructor; eauto. 
Qed.

Lemma good_path :
  forall
    T V (VT: @VTyp T V)
    h
    (GH: good_heap T V VT h)
    p f s d s'
    (SF: scopeofFrame V fh h f s)
    (SLK: slookup (@g gat (@wc T dwc)) s p s' d),
  exists f', lookup V fh h f p f' /\ scopeofFrame V fh h f' s'.
Proof.
  induction p; intros; inv SLK; sgauto. destruct H0 as [LL [IN SL]].
  assert (GF: good_frame T V VT h f) by sgauto.
  inv GF. inv H0. eapply scopeofFrameDet in SF; eauto; subst.
  eapply LNS in LL.
  destruct LL as [? [IMF [KEYS IMSC]]]; subst.
  eapply IMSC in IN. inv IN. inv H0.
  eapply IHp in SL; eauto.
  destruct SL as [? [LOOK SF]].
  eexists; split; sgauto.
Qed.

Lemma setSlot_well_bound :
  forall T V (VT: @VTyp T V) h0 f d v h1
    (SET: setSlot V fh h0 f d v h1)
    (WB: well_bound T V VT h0 f),
    well_bound T V VT h1 f.
Proof.
  intros; inv WB; sgauto.
  inversion SET; subst. inversion SC. rewrite H2 in H1; inv H1.
  econstructor.
  - econstructor; eauto. rewrite get_set_same; eauto.
  - intros. eapply DSS in H1. inv H1. inv H3.
    eexists; split. econstructor. simpl. destruct (FrameIdDec f f); [|intuition]. clear e.
    eauto. eapply DomEq_set; eauto.
    inv H1. rewrite H3 in H2. inv H2. auto.
  - intros. inv H1. rewrite get_set_same in H3. inv H3.
    assert (getSlots V fh h0 f slots). econstructor; eauto.
    eapply DSF in H1. inv H1. inv H3. eexists; split; eauto.
    eapply DomEq_set; eauto.
  - intros. eapply LNS in H1; eauto.
    destruct H1 as [? [LLN [KS SS]]]. subst. inv LLN.
    eexists; split; eauto. econstructor; eauto. inv H1. rewrite H4 in H2. inv H2.
    econstructor. rewrite get_set_same; eauto.
    split; auto. intros. apply SS in H4. destruct H4 as [? [? ?]].
    eexists; split; eauto. inv H5.
    destruct (FrameIdDec f x0). subst.
    rewrite H2 in H6. inv H6.
    econstructor. rewrite get_set_same; eauto.
    econstructor. rewrite get_set_other; eauto.
  - intros. inv H1. inv H3. rewrite get_set_same in H1. inv H1.
    assert (llinksofFrame V fh h0 f l ks).
    econstructor; eauto. econstructor; eauto.
    eapply LNF in H1. auto.
Qed.

Lemma setSlot_well_typed :
  forall
    T V (VT: @VTyp T V) h0 f d v h1 t s
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (VT': vtyp h0 v t)
    (WT: well_typed T V VT h0 f),
    well_typed T V VT h1 f.
Proof.
  intros; inv WT; sgauto.
  inversion SET; subst. inversion SC. rewrite H2 in H1; inv H1.
  econstructor; eauto.
  - econstructor; eauto. rewrite get_set_same; eauto.
  - intros. inv H4. rewrite get_set_same in H5. inv H5.
    eapply setSlot_vtyp; eauto. simpl in H6. eapply scopeofFrameDet in SF; eauto; subst.
    destruct (Ddec d0 d); subst. inv H6. simpl in H3. eapply typofDeclDet in TD; eauto; subst; eauto.
    eapply WT0 in H1; eauto. econstructor; eauto. assert (d <> d0). intuition.
    apply get_remove_other with (Kdec:=Ddec) (m:=slots) in H4.
    rewrite H4 in H6. auto.
Qed.

Hint Resolve setSlot_well_bound : sgraph.
Hint Resolve setSlot_well_typed : sgraph.
Hint Unfold good_frame : sgraph.

Lemma setSlot_good_frame :
  forall
    T V (VT: @VTyp T V) h0 f d v h1 s t
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (VT': vtyp h0 v t)
    (WT: good_frame T V VT h0 f),
    good_frame T V VT h1 f.
Proof.
  intros. inv WT. sgauto.
Qed.

Hint Resolve setSlot_good_frame : sgraph.

Lemma setSlot_other_well_bound :
  forall T V (VT: @VTyp T V) h0 f d v h1 f0
    (SET: setSlot V fh h0 f d v h1)
    (WB: well_bound T V VT h0 f0)
    (DIFF: f <> f0),
    well_bound T V VT h1 f0.
Proof.
  intros; inv WB; sgauto. inv SC; inv SET.
  econstructor.
  - econstructor; eauto. rewrite get_set_other; eauto.
  - intros. eapply DSS in H3. destruct H3 as [? [? ?]]. inv H3. rewrite H5 in H0; inv H0.
    eexists; split; eauto. econstructor; rewrite get_set_other; eauto.
  - intros. inv H3. rewrite get_set_other in H4; [|intuition]. rewrite H4 in H0; inv H0.
    assert (getSlots V fh h0 f0 slots). econstructor; eauto. eauto.
  - intros. eapply LNS in H3. destruct H3 as [? [? [? ?]]]; subst.
    inv H3. inv H4. rewrite H3 in H0; inv H0.
    eexists; split; eauto. econstructor; sgauto. econstructor; rewrite get_set_other; eauto.
    split; eauto. intros. eapply H5 in H0. destruct H0 as [? [? ?]].
    inv H4.
    eexists; split; eauto. destruct (FrameIdDec x0 f); subst.
    rewrite H7 in H2; inv H2. econstructor; rewrite get_set_same; sgauto.
    econstructor; rewrite get_set_other; sgauto.
  - intros. inv H3. inv H4. rewrite get_set_other in H3; auto. rewrite H3 in H0; inv H0.
    assert (llinksofFrame V fh h0 f0 l ks0); sgauto.
Qed.

Lemma setSlot_other_well_typed :
  forall
    T V (VT: @VTyp T V) h0 f d v h1 t s f0
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (VT': vtyp h0 v t)
    (WT: well_typed T V VT h0 f0)
    (DIFF: f <> f0),
    well_typed T V VT h1 f0.
Proof.
  intros; inv WT. inv SC; inv SET.
  econstructor; eauto.
  - econstructor; rewrite get_set_other; eauto.
  - intros. inv H5. rewrite get_set_other in H6; eauto.
    eapply setSlot_vtyp. econstructor; eauto. eapply WT0; eauto. econstructor; eauto.
Qed.

Hint Resolve setSlot_other_well_bound : sgraph.
Hint Resolve setSlot_other_well_typed : sgraph.

Lemma setSlot_other_good_frame :
  forall
    T V (VT: @VTyp T V) h0 f d v h1 t s f0
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (VT': vtyp h0 v t)
    (WT: good_frame T V VT h0 f0)
    (DIFF: f <> f0),
    good_frame T V VT h1 f0.
Proof.
  intros; inv WT; sgauto.
Qed.

Lemma setSlot_good_heap :
  forall
    T V (VT: @VTyp T V) h0 f d v h1 s t
    (SET: setSlot V fh h0 f d v h1)
    (SF: scopeofFrame V fh h0 f s)
    (TD: typofDecl T dwc s d t)
    (VT': vtyp h0 v t)
    (WT: good_heap T V VT h0),
    good_heap T V VT h1.
Proof.
  intros. intro. intro. destruct (FrameIdDec f f0); subst.
  - eapply setSlot_good_frame; eauto. eapply WT. unfold frame. inv SET; eapply keys_in; eauto.
  - eapply setSlot_other_good_frame; eauto. eapply WT.
    inv SET. unfold frame in H0. eapply in_keys in H0. rewrite get_set_other in H0; auto.
    destruct H0. eapply keys_in; eauto.
Qed.

Hint Resolve setSlot_good_heap : sgraph.

Lemma getAddr_scopeofFrame :
  forall
    T (G: @WCGAT T) V (VT: @VTyp T V) h f r ff d
    (GH: good_heap T V VT h)
    (FH: frame h f)
    (ADDR: getAddr V fh wc h f r (Addr_ ff d)),
    exists sf, scopeofFrame V fh h ff sf.
Proof.
  inversion 3; subst. clear PATH ADDR.
  induction LK; eauto.
  - unfold frame in FH. eapply in_keys in FH. destruct FH. destruct x. destruct p.
    eexists; try econstructor; eauto.
  - generalize (GH _ FH); intro GF. inv GF. inv H0.
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

Lemma getAddr_in_ds :
  forall
    T (G: @WCGAT T) V (VT: @VTyp T V) h f r ff d s sf
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (GH: good_heap T V VT h)
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
    assert (frame h f) by sgauto. specialize (GH _ H0).
    destruct GH. destruct H1.
    eapply scopeofFrameDet in SC; eauto; subst.
    inv SF. assert (getSlots V fh h f slots) by sgauto.
    apply DSF in H3. destruct H3 as [? [DD' DE]]. inv DD'.
    eexists; split. econstructor; sgauto. inv SL.
    rewrite H4 in DD; inv DD. simpl; auto.
  - inv SL. destruct H0 as [LL [INS SL]].
    inv LL. destruct H0.
    eapply IHLK; sgauto.
    assert (frame h f) by sgauto.
    specialize (GH _ H2). inv GH. inv H3.
    specialize (LNF _ _ IMS). inv LNF. destruct H3.
    eapply scopeofFrameDet in SF; eauto; subst.
    rewrite H3 in H0; inv H0.
    assert (llinksofScopeP (@g gat (@wc T dwc)) s0 l (keys ks)) by (econstructor; eauto).
    eapply LNS in H0. destruct H0 as [? [LL [K IN]]].
    assert (In s (keys ks)). eapply keys_in; eauto.
    eapply IN in H0. eapply llinksofFrameDet in IMS; eauto; subst.
    destruct H0 as [? [GET SF]].
    rewrite GET in S; inv S. auto.
Qed.

Lemma getAddr_getSlot :
  forall
    T (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d
    (SF: scopeofFrame V fh h f s)
    (SR: scopeofRefP (@wc T dwc) r s)
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_heap T V VT h),
  exists v t, getSlot V fh h ff d v /\ (@vtyp T V VT) h v t.
Proof.
  intros.
  assert (ADDR':=ADDR). eapply getAddr_scopeofFrame in ADDR; eauto. destruct ADDR.
  assert (ADDR:=ADDR'). eapply getAddr_in_ds in ADDR; eauto. destruct ADDR as [? [DS IN]].
  assert (SF':=H0). apply scopeofFrameFrame in H0.
  specialize (GH _ H0). destruct GH. destruct H1, H2.
  inv DS. destruct H1; subst.
  eapply scopeofFrameDet in SC; eauto; subst.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP wc s1 x1) by sgauto.
  eapply DSS in H2. destruct H2. destruct H2.
  assert (IN':=IN). eapply H3 in IN. eapply in_keys in IN. destruct IN.
  inv H2.
  assert (getSlot V fh h ff d x0) by sgauto.
  inv DS0. destruct H6; subst. rewrite H6 in H1; inv H1.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  eapply WT in IN; sgauto.
Qed.

Lemma getAddr_typofDecl_getSlot :
  forall
    T (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d sf
    (SF: scopeofFrame V fh h f s)
    (SR: scopeofRefP (@wc T dwc) r s)
    (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
    (FH: frame h f)
    (GH: good_heap T V VT h)
    (SFF: scopeofFrame V fh h ff sf),
  exists v t, getSlot V fh h ff d v /\ (@vtyp T V VT) h v t /\ typofDecl T dwc sf d t.
Proof.
  intros.
  assert (ADDR':=ADDR). eapply getAddr_scopeofFrame in ADDR; eauto. destruct ADDR.
  assert (ADDR:=ADDR'). eapply getAddr_in_ds in ADDR; eauto. destruct ADDR as [? [DS IN]].
  assert (SF':=H0). apply scopeofFrameFrame in H0.
  specialize (GH _ H0). destruct GH. destruct H1, H2.
  inv DS. destruct H1; subst.
  eapply scopeofFrameDet in SC; eauto; subst.
  eapply scopeofFrameDet in SC0; eauto; subst.
  eapply scopeofFrameDet in SFF; eauto; subst.
  assert (ddataofScopeP wc sf x1) by sgauto.
  eapply DSS in H2. destruct H2. destruct H2.
  assert (IN':=IN). eapply H3 in IN. eapply in_keys in IN. destruct IN.
  inv H2.
  assert (getSlot V fh h ff d x0) by sgauto.
  inv DS0. destruct H6; subst. rewrite H6 in H1; inv H1.
  assert (IN:=IN').
  eapply in_keys in IN'. destruct IN'.
  eapply WT in IN; sgauto. do 2 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_typofDecl_getSlot : sgraph.
Hint Resolve getAddr_in_ds : sgraph.
Hint Resolve getAddr_scopeofFrame : sgraph.

(* Getting the address of a reference by starting in a good frame in a
good heap results in an address that is both well-bound (the frame has
a scope where the declaration of the address is bound) and well-typed
(getting the value of the slot in the frame results in a value of the
expected type). *)

Lemma getAddr_good_frame :
  forall
     T (G: @WCGAT T) V (VT: @VTyp T V) h f r ff s d
     (SF: scopeofFrame V fh h f s)
     (SR: scopeofRefP (@wc T dwc) r s)
     (ADDR: getAddr V fh (@wc T dwc) h f r (Addr_ ff d))
     (FH: frame h f)
     (GH: good_heap T V VT h),
  exists sf v t,
    scopeofFrame V fh h ff sf /\ getSlot V fh h ff d v /\ (@vtyp T V VT) h v t /\ typofDecl T dwc sf d t.
Proof.
  intros. assert (ADDR':=ADDR). eapply getAddr_scopeofFrame in ADDR'; sgauto. destruct ADDR'.
  exists x. eapply getAddr_typofDecl_getSlot in ADDR; eauto.
  destruct ADDR as [? [? [GS [VT' TD]]]]. do 2 eexists; split; sgauto.
Qed.

Hint Resolve getAddr_good_frame : sgraph.

(* Corollary of [good_path]: In a good heap, looking up an address
results in a frame that instantiates the expected scope *)

Lemma good_addr :
  forall
    T V (VT: @VTyp T V) h r p f s d s'
    (SLK: rlookup (@wc T dwc) s r p s' d)
    (GH: good_heap T V VT h)
    (SF: scopeofFrame V fh h f s),
  exists ff, getAddr V fh (@wc T dwc) h f r (Addr_ ff d) /\ scopeofFrame V fh h ff s'.
Proof.
  intros. destruct SLK as [? [? ?]].
  assert (H2':=H2).
  eapply good_path in H2; eauto.
  destruct H2. destruct H2.
  eexists; split; sgauto. econstructor; sgauto.
  eapply slookup_declofPath; sgauto.
Qed.

Lemma good_frame_setSlot :
  forall
    T V (VT: @VTyp T V) h f s ds d
    (SF: good_frame T V VT h f)
    (SC: scopeofFrame V fh h f s)
    (DS: declsofScopeP (@wc T dwc) s ds)
    (IN: In d ds),
  forall v,
  exists h3, setSlot V fh h f d v h3.
Proof.
  intros. inv SF. inv H1. eapply scopeofFrameDet in SC; eauto; subst.
  inv DS. destruct H1. subst. inv H0.
  eapply scopeofFrameDet in SC0; eauto; subst.
  assert (ddataofScopeP wc s x) by sgauto.
  eapply DSS in H0. destruct H0 as [? [? ?]].
  destruct H0. inv SC. erewrite H3 in H0; inv H0.
  eexists. econstructor; sgauto. eapply H2. assumption.
Qed.

Hint Resolve good_addr : sgraph.

Lemma initNewFrame_other_well_bound :
  forall
    T V (VT : @VTyp T V) h0 s ks vs f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks vs f h1)
    f'
    (WB: well_bound T V VT h0 f'),
    well_bound T V VT h1 f'.
Proof.
  intros; inv WB. inv INIT.
  assert (NF':=NF); eapply newFrameSame in NF'.
  assert (FF':=FF); eapply fillFrameSame in FF; eauto. inv FF.
  inv NF. rewrite get_set_same in NF'. inv NF'.
  inv SC.
  assert (f' <> f). intro. subst. apply H0. eapply keys_in; eauto.
  assert (FF'':=FF').
  eapply fillFrameDiff in FF'; eauto. Focus 2.
  apply get_set_other with (Kdec:=FrameIdDec) (m:=h0) (v:=(s, ks, empty)) in H3.
  rewrite H3. eauto.
  econstructor; sgauto.
  - intros. eapply DSS in H4. destruct H4 as [? [GS DE]].
    eexists; split; sgauto. inv GS. rewrite H4 in H2. inv H2. auto.
  - intros. inversion H4. rewrite H5 in FF'. inv FF'.
    assert (getSlots V fh h0 f' slots). econstructor; eauto.
    eauto.
  - intros. eapply LNS in H4. destruct H4 as [? [LL [KS GS]]].
    inv LL. inv H4. rewrite H6 in H2. inv H2.
    eexists; split. econstructor; eauto. econstructor; eauto.
    split; eauto. intros. eapply GS in H2.
    destruct H2 as [? [? ?]]; eexists; split; eauto.
    inv H4.
    destruct (FrameIdDec x0 f). subst. destruct H0. eapply keys_in in H7; auto.
    destruct (FrameIdDec x0 f'). subst.
    rewrite H7 in H6; inv H6.
    econstructor; eauto.
    eapply fillFrameDiff in FF''; eauto.
    econstructor. eauto. rewrite get_set_other; eauto.
  - intros.
    assert (llinksofFrame V fh h0 f' l ks1).
    inv H4. inv H5. rewrite H4 in FF'. inv FF'. econstructor; sgauto.
    eapply LNF in H5; eauto.
Qed.

Lemma initNewFrame_other_well_typed :
  forall
    T V (VT : @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    slots
    (TDs: declsofScopeP (@wc T dwc) s (@keys D V slots))
    (* (* dynamic decls? *) *)
    (* (DDs: dynamicDecls (keys ds)) *)
    f'
    (WT: well_typed T V VT h0 f'),
    well_typed T V VT h1 f'.
Proof.
  intros. inv INIT.
  assert (NF':=NF); eapply newFrameSame in NF'.
  assert (FF':=FF); eapply fillFrameSame in FF; eauto. inv FF.
  inversion NF; subst. rewrite get_set_same in NF'. inv NF'. inv WT. inv SC.
  assert (f' <> f). intro. subst. apply H0. eapply keys_in; eauto.
  assert (FF'':=FF').
  eapply fillFrameDiff in FF'; eauto. Focus 2.
  apply get_set_other with (Kdec:=FrameIdDec) (m:=h0) (v:=(s, ks, empty)) in H3.
  rewrite H3. eauto.
  econstructor; sgauto. intros.
  eapply fillFrame_vtyp in FF''; eauto.
  eapply newFrame_vtyp in NF; eauto.
  inv H6. rewrite H7 in FF'; inv FF'.
  eapply WT0; eauto. econstructor; eauto.
Qed.

Hint Resolve initNewFrame_other_well_bound : sgraph.
Hint Resolve initNewFrame_other_well_typed : sgraph.

Lemma initNewFrame_other_good_frame :
  forall
    T V (VT : @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (* (* dynamic decls? *) *)
    (* (DDs: dynamicDecls (keys ds)) *)
    f'
    (GF: good_frame T V VT h0 f'),
    good_frame T V VT h1 f'.
Proof.
  intros; inv GF; sgauto.
Qed.

Lemma initNewFrame_well_bound :
  forall
    T V (VT: @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
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
    well_bound T V VT h1 f.
Proof.
  intros; inv INIT. inv NF. assert (FF':=FF).
  eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
  eexists; sgauto.
  - intros. eapply declsofScopeDet in TDs; eauto; subst.
    inv H1. inv DS. inv H1. rewrite H2 in H3. inv H3.
    eexists; split; sgauto. split; rewrite <- H4; auto.
  - intros. inv H1. rewrite H2 in FF; inv FF. inv TDs. inv H1.
    eexists; split; sgauto. split; rewrite <- H4; auto.
  - intros. eapply LNS in H1. destruct H1 as [? [M [KS SF]]]. subst.
    eexists; split. econstructor; eauto. econstructor; eauto.
    split; eauto. intros. apply SF in H1. destruct H1 as [? [GS SF']]. inv SF'.
    assert (x0 <> f). intro. subst. apply keys_in in H1. contradiction.
    eapply fillFrameDiff in FF'; eauto. Focus 2. rewrite get_set_other; eauto.
    eexists; split; sgauto.
  - intros. inv H1. inv H2. rewrite H1 in FF; inv FF.
    apply LNF in H3; auto.
Qed.

Lemma initNewFrame_well_typed :
  forall
    T V (VT: @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> vtyp h0 v t),
    well_typed T V VT h1 f.
Proof.
  intros; inversion INIT. inv NF. assert (FF':=FF).
  eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
  eexists; sgauto.
  intros. eapply declsofScopeDet in TDs; eauto; subst.
  inv H3. rewrite H4 in FF; inv FF.
  eapply TYP in H1; eauto. eapply initNewFrame_vtyp; eauto.
Qed.

Hint Resolve initNewFrame_well_bound : sgraph.
Hint Resolve initNewFrame_well_typed : sgraph.

Lemma initNewFrame_good_frame :
  forall
    T V (VT: @VTyp T V) h0 s ks slots f h1
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> vtyp h0 v t)
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
    good_frame T V VT h1 f.
Proof.
  intros; sgauto.
Qed.

Hint Resolve initNewFrame_good_frame : sgraph.

Lemma initNewFrame_good_heap :
  forall
    T V (VT: @VTyp T V) h0 s ks slots f h1
    (GH: good_heap T V VT h0)
    (INIT: initNewFrame V fh (@wc T dwc) h0 s ks slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> (@vtyp T V VT) h0 v t)
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
    good_heap T V VT h1.
Proof.
  intros. unfold good_heap. intros.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ INIT f0). destruct H1.
  apply H2 in H0. destruct H0. subst. sgauto.
  eapply initNewFrame_other_good_frame in INIT; eauto.
Qed.


Lemma initNewFrame_well_bound1 :
  forall
    T V (VT: @VTyp T V) h0 s  slots f h1 l sl fl
    (INIT: initNewFrame V fh (@wc T dwc) h0 s [(l, [(sl, fl)])] slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl])])
    (SL: scopeofFrame V fh h0 fl sl),
    well_bound T V VT h1 f.
Proof.
  intros; eapply initNewFrame_well_bound; eauto.
  intros. inv LNS. inv H0. inv H1. rewrite H2 in H0; inv H0.
  destruct (ELdec l0 l). subst; simpl in *. destruct (ELdec l l); [|intuition].
  inv H3. eexists; split; eauto. split; eauto. intros. inv H0.
  eexists; split; eauto. simpl. destruct (ScopeIdDec s0 s0); intuition.
  inv H1. simpl in H3. destruct (ELdec l0 l); intuition. inv H3.
  intros. simpl in H0. destruct (ELdec l0 l); intuition. subst. inv H0.
  inv LNS. econstructor; split; eauto. simpl. destruct (ELdec l l); intuition.
  inv H0.
Qed.

Hint Resolve initNewFrame_well_bound1 : sgraph.

Lemma initNewFrame_well_bound2 :
  forall
    T V (VT: @VTyp T V) h0 s  slots f h1 l sl fl l' sl' fl'
    (INIT: initNewFrame V fh (@wc T dwc) h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl]); (l', [sl'])])
    (SL: scopeofFrame V fh h0 fl sl)
    (SL: scopeofFrame V fh h0 fl' sl'),
    well_bound T V VT h1 f.
Proof.
  intros; eapply initNewFrame_well_bound; eauto.
  intros. inv LNS. inv H0. inv H1. rewrite H2 in H0; inv H0.
  destruct (ELdec l0 l). subst; simpl in *. destruct (ELdec l l); [|intuition].
  inv H3. eexists; split; eauto. split; eauto. intros. inv H0.
  eexists; split; eauto. simpl. destruct (ScopeIdDec s0 s0); intuition.
  inv H1. simpl in H3. simpl.
  destruct (ELdec l0 l); intuition.
  destruct (ELdec l0 l'); intuition.
  subst. inv H3. eexists; split; simpl; sgauto. split; sgauto. intros.
  destruct H0; inv H0. simpl. destruct (ScopeIdDec s0 s0); [|intuition].
  sgauto. inv H3.
  intros. simpl in H0.
  eexists; split; sgauto. simpl.
  destruct (ELdec l0 l); intuition. subst. inv H0.
  inv LNS. econstructor; split; eauto. simpl. destruct (ELdec l l); intuition.
  destruct (ELdec l0 l'); intuition. inv H0.
  eexists; split; sgauto. inv H0.
Qed.

Hint Resolve initNewFrame_well_bound2 : sgraph.


Lemma initNewFrame_good_heap1 :
  forall
    T V (VT: @VTyp T V) h0 s slots f h1 l sl fl
    (GH: good_heap T V VT h0)
    (INIT: initNewFrame V fh (@wc T dwc) h0 s [(l, [(sl, fl)])] slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> (@vtyp T V VT) h0 v t)
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl])])
    (SL: scopeofFrame V fh h0 fl sl),
    good_heap T V VT h1.
Proof.
  intros. unfold good_heap. intros.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ INIT f0). destruct H1.
  apply H2 in H0. destruct H0. subst. sgauto.
  eapply initNewFrame_other_good_frame in INIT; eauto.
Qed.

Hint Resolve initNewFrame_good_heap : sgraph.
Hint Resolve initNewFrame_good_heap1 : sgraph.
Hint Resolve defaults_vtyp' : sgraph.

Lemma initNewFrame_good_heap2 :
  forall
    T V (VT: @VTyp T V) h0 s slots f h1 l sl fl l' sl' fl'
    (GH: good_heap T V VT h0)
    (INIT: initNewFrame V fh (@wc T dwc) h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] slots f h1)
    (TDs: declsofScopeP (@wc T dwc) s (keys slots))
    (** WellTyped slots: *)
    (TYP: forall d t v,
        In d (keys slots) ->
        typofDecl T dwc s d t ->
        get Ddec slots d = Some v -> (@vtyp T V VT) h0 v t)
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl]); (l', [sl'])])
    (SL: scopeofFrame V fh h0 fl sl)
    (SL': scopeofFrame V fh h0 fl' sl'),
    good_heap T V VT h1.
Proof.
  intros. unfold good_heap. intros.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ INIT f0). destruct H1.
  apply H2 in H0. destruct H0. subst. sgauto.
  eapply initNewFrame_other_good_frame in INIT; eauto.
Qed.


Lemma initNewDefaultFrame_good_frame :
  forall
    T V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s ks f h1
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
    good_frame T V VT h1 f.
Proof.
  intros. inversion INIT. sgauto.
Qed.

Lemma initNewDefaultFrame_good_heap :
  forall
    T V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s ks f h1
    (GH: good_heap T V VT h0)
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
    good_heap T V VT h1.
Proof.
  inversion 2; intros; sgauto.
Qed.

Lemma initNewDefaultFrame_good_heap1 :
  forall
    T V (VT: @VTyp T V) (DVT: @DefaultVTyp T V VT) h0 s f h1 l sl fl
    (GH: good_heap T V VT h0)
    (INIT: initNewDefaultFrame DVT h0 s [(l, [(sl, fl)])] f h1)
    (** WellBound links: *)
    (LNS: linksofScopeP (@wc T dwc) s [(l, [sl])])
    (SL: scopeofFrame V fh h0 fl sl),
    good_heap T V VT h1.
Proof.
  intros. unfold good_heap. intros. inv INIT.
  pose proof (initNewFrameFrames _ _ _ _ _ _ _ _ _ NF f0). destruct H1.
  apply H2 in H0. destruct H0. subst. sgauto.
  eapply initNewFrame_other_good_frame in NF; eauto.
Qed.


Hint Resolve initNewDefaultFrame_good_frame : sgraph.
Hint Resolve initNewDefaultFrame_good_heap : sgraph.
Hint Resolve initNewDefaultFrame_good_heap1 : sgraph.


