Require Import maps scopes frames.

(** * References *)

Class VRefers {V: Type} :=
 { (** [vrefers v f] means [v] refers directly to [f] *)
   vrefers : V -> FrameId -> Prop
 }.

Section VRefersProperties.

  Context {V:Type} {VR: @VRefers V} {FH: @FrameHeap V}.

  (** [frefers f f'] means [f] refers directly to [f'] *)
  Inductive frefers (h: H) : FrameId -> FrameId -> Prop :=
  | fr_link : forall f links,
                linksofFrame h f links ->
                forall m, In m (values ELdec links) ->
                          forall f', In f' (values ScopeIdDec m) ->
                                     frefers h f f'
  | fr_slot : forall f slots,
                slotsofFrame h f slots ->
                forall v, In v (values Ddec slots) ->
                          forall f', vrefers v f' ->
                                     frefers h f f'.

  Hint Constructors frefers : sgraph.

  (** Interaction between frame removal and references. *)

  Lemma removeFrame_frefers:
    forall h0 h1 f0 f1 f2,
      removeFrame h0 f0 h1 ->
      (frefers h1 f1 f2 <-> (frefers h0 f1 f2 /\ f0 <> f1)).
  Proof.
    intros.
    split; intros.
    + inv H0.
    - inv H1. erewrite removeFrameSame in H0; eauto. inv H0; sgauto.
    - inv H1. erewrite removeFrameSame in H0; eauto. inv H0; sgauto.
      + inv H0. inv H1.
    - inv H0. econstructor; eauto. econstructor. erewrite removeFrameSame; sgauto.
    - inv H0. eapply fr_slot; eauto. econstructor. erewrite removeFrameSame; sgauto.
  Qed.

  Lemma removeFrames_frefers:
    forall h0 h1 fs f1 f2,
      removeFrames h0 fs h1 ->
      (frefers h1 f1 f2 <-> (frefers h0 f1 f2 /\ ~ In f1 fs)).
  Proof.
    intros. induction H. intuition.
    split; intros.
    + rewrite IHremoveFrames in H1. inv H1.
      eapply removeFrame_frefers in H.  rewrite H in H2.  inv H2. split; auto.
      intro. inv H2; auto.
    + rewrite IHremoveFrames. inv H1.  split.
    - eapply removeFrame_frefers; eauto.  split; eauto. intro. subst. apply H3. left; auto.
    - intro; apply H3; right; auto.
  Qed.

  (** [reachable f f'] means [f'] is reachable from [f].
   This is just the reflexive transitive closure of [frefers]. *)
  Inductive reachable (h: H) : FrameId -> FrameId -> Prop :=
  | re_refl : forall f, reachable h f f
  | re_fref: forall f f' f'', frefers h f f' -> reachable h f' f'' -> reachable h f f''.

  (** * Notions of Garbage Collection. *)

  Definition unreferenced (h: H) (f: FrameId) : Prop :=
    forall f0, frame h f0 -> ~ frefers h f0 f.

  (** It is "safe" to drop a set of frames from the heap
     if doing so does not result in any new dangling pointers.
     This gives a very high-level notion of safe garbage collection. *)

  Inductive safeRemoval (h0: H) (fs: list FrameId) (h1: H) : Prop :=
  | ds :   removeFrames h0 fs h1 ->
           (forall f, In f fs -> unreferenced h1 f) ->
           safeRemoval h0 fs h1.

  (** Modeling non-deterministic, incomplete reference counting. *)
  (** Drop an unreferenced frame. *)
  Inductive removeUnreferenced (h0: H) (f: FrameId) (h1: H) : Prop :=
  | dunr :   unreferenced h0 f ->
             removeFrame h0 f h1 ->
             removeUnreferenced h0 f h1.

  Lemma removeUnreferenced_safe :
    forall h0 f h1,
      removeUnreferenced h0 f h1 ->
      safeRemoval h0 [f] h1.
  Proof.
    intros.  inv H. econstructor.
    econstructor.  eauto. econstructor.
    intros. inv H.
    unfold unreferenced in *. intros. intro. eapply H0. eapply removeFrameFrames0 in H1.  apply H1 in H.  inv H.  apply H4.
    rewrite (removeFrame_frefers h0) in H2. inv H2; auto.   eauto.
    inv H2.
  Qed.

  (** Modeling complete reference counting. *)
  (** Drop exactly the unreferenced frames. *)
  Inductive removeAllUnreferenced (h0: H) (fs:list FrameId) (h1: H) : Prop :=
  | daunr:  (forall f, unreferenced h0 f <-> In f fs) ->
            removeFrames h0 fs h1 ->
            removeAllUnreferenced h0 fs h1.


  Lemma removeAllUnreferenced_safe :
    forall h0 fs h1,
      removeAllUnreferenced h0 fs h1 ->
      safeRemoval h0 fs h1.
  Proof.
    intros. inv H. econstructor; eauto.
    intros. rewrite <- H0 in H.  unfold unreferenced in *.
    intros.  intro. eapply (H f0).
    eapply removeFramesFrames in H2; eauto. intuition.
    erewrite removeFrames_frefers in H3; eauto. intuition.
  Qed.

  (** Modeling complete reachability-based gc with respect to a root set. *)
  (** Drop exactly the frames unreachable from some (arbitrary) root set. *)
  Inductive removeAllUnreachable (h0 : H) (roots: list FrameId) (fs: list FrameId) (h1: H): Prop :=
  | dunreach :   (forall f, In f fs <-> (forall f0, In f0 roots -> ~ reachable h0 f0 f)) ->
                 removeFrames h0 fs h1 ->
                 removeAllUnreachable h0 roots fs h1.

  Lemma removeAllUnreachable_safe :
    forall h0 h1 roots fs,
      removeAllUnreachable h0 roots fs h1 ->
      safeRemoval h0 fs h1.
  Proof.
    intros.
    inv H. econstructor; eauto.
    intros. rewrite H0 in H.
    unfold unreferenced. intros. intro.
    erewrite removeFrames_frefers in H3; eauto. inv H3.
    apply H5.
    rewrite H0.
    intros.
    intro.
    eapply H.
    eauto.
    clear - H4 H6.
    induction H6.
    econstructor.  eauto. econstructor.
    econstructor. eauto. eauto.
  Qed.


End VRefersProperties.

(** * Types and References *)

(** Extend definition of value typing to require that it is invariant
    under removal of frames not referenced by the value. *)
Class VTypRefers `{VT: VTyp} `{VTR: VRefers V} :=
  { removeFrames_vtyp :
      forall h1 fs h2 v0 t0
        (RM: removeFrames h1 fs h2)
        (NR: forall f, vrefers v0 f -> ~ In f fs)
        (VT: vtyp h1 v0 t0),
        vtyp h2 v0 t0
  }.

Section VTypRefersProperties.

  Context `{VTR: VTypRefers}.

  (** Key lemma (paper Lemma 2): safe frame dropping preserves heap goodness. *)
  Lemma good_heap_safeRemoval :
    forall h1,
      good_heap h1 ->
      forall fs h2, safeRemoval h1 fs h2 ->
                    good_heap h2.
  Proof.
    intros. inv H0.
    unfold good_heap in *.  intros.
    eapply removeFramesFrames in H0; eauto. destruct H0.
    pose proof (H f H3).
    inv H4.
    econstructor.

    inv H5. econstructor.

    eapply removeFramesScope; eauto.

    intros. destruct (DSS ds0 H4) as [slots [P1 P2]].
    exists slots. split. inv P1. econstructor. eapply removeFramesSame; eauto.  auto.

    intros. inv H4. eapply removeFramesSame in H5; eauto. destruct H5.
    edestruct (DSF slots) as [ds [P1 P2]]. econstructor; eauto.
    exists ds; eauto.

    intros. destruct (LNS l ss H4) as [ks [P1 [P2 P3]]]. subst ss.
    inv P1. inv H5. exists ks. split. econstructor. econstructor. eapply removeFramesSame; eauto.
    auto. split; auto. intros.  destruct (P3 s1 H5) as [f' [Q1 Q2]]. exists f'; split; eauto.
    eapply removeFramesScope; eauto. split; eauto.

    intro. apply H2 in H9. eapply H9.
    eapply removeFramesFrames; eauto.
    econstructor.
    econstructor. eapply removeFramesSame; eauto.
    eapply values_in; eauto.
    eapply values_in; eauto.

    intros. eapply LNF. inv H4. inv H5. econstructor; eauto.  econstructor.
    eapply removeFramesSame in H4; eauto. destruct H4; eauto.

    inv H6. econstructor; eauto.

    eapply removeFramesScope; eauto.

    intros.
    eapply removeFrames_vtyp; eauto.  intros.
    intro.  apply H2 in H9. eapply H9.
    eapply removeFramesFrames; eauto.
    inv H7.
    eapply fr_slot.
    econstructor; eauto.
    eapply values_in; eauto. eauto.
    eapply WT; eauto. inv H7. econstructor; eauto.
    eapply removeFramesSame in H8; eauto. destruct H8; eauto.
  Qed.

  (** Paper Lemma 3(a) *)
  Corollary good_heap_removeUnreferenced:
    forall (h1: H),
      good_heap h1 ->
      forall fs h2, removeUnreferenced h1 fs h2 ->
                    good_heap h2.
  Proof.
    intros.  eapply good_heap_safeRemoval; eauto.
    eapply removeUnreferenced_safe; eauto.
  Qed.

  Corollary good_heap_removeAllUnreferenced:
    forall (h1: H),
      good_heap h1 ->
      forall fs h2, removeAllUnreferenced h1 fs h2 ->
                    good_heap h2.
  Proof.
    intros.  eapply good_heap_safeRemoval; eauto.
    eapply removeAllUnreferenced_safe; eauto.
  Qed.

  (** Paper Lemma 3(b). *)
  Corollary good_heap_removeUnreachable:
    forall (h1: H),
      good_heap h1 ->
      forall rs fs h2, removeAllUnreachable h1 rs fs h2 ->
                       good_heap h2.
  Proof.
    intros.  eapply good_heap_safeRemoval; eauto.
    eapply removeAllUnreachable_safe; eauto.
  Qed.

End VTypRefersProperties.
