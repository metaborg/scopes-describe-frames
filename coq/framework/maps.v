(* A simple definition of maps as association lists with unique keys.

   It is such a pain to figure out how to invoke the FMaps library
   that I just ended up writing this myself.

*)

Require Import List.
Import ListNotations.

Ltac inv H := (inversion H; subst; clear H).

Definition map (K:Type) (V:Type) := list (K*V)%type.

Section Maps.

  Context {K:Type}.
  Context {V:Type}.

  Hypothesis Kdec : forall (k1 k2:K), {k1 = k2} + {k1 <> k2}.

  Definition empty : map K V := [].

  Fixpoint get (m: map K V) (k:K) : option V :=
    match m with
    | (k',v')::m' => if Kdec k k' then Some v' else get m' k
    | [] => None
    end.

  Fixpoint remove (m: map K V) (k:K) : map K V :=
    match m with
    | (k',v')::m' => if Kdec k k' then (remove m' k) else (k',v')::(remove m' k)
    | [] => []
    end.

  Definition set (m: map K V) (k:K) (v:V) : map K V := (k,v)::(remove m k).

  Definition keys (m:map K V) : list K :=
    List.map (@fst K V) m.

  Definition values (m:map K V) : list V :=
    List.map (@snd K V) m.

  Lemma get_remove_same: forall m k, get (remove m k) k = None.
  Proof.
    induction m; intros.
    auto.
    simpl. destruct a. destruct (Kdec k k0). subst. auto.
    simpl. destruct (Kdec k k0). subst; exfalso; apply n; auto. auto.
  Qed.

  Lemma get_remove_other: forall m k k', k <> k' -> get (remove m k) k' = get m k'.
  Proof.
    induction m; intros.
    auto.
    simpl. destruct a.
    destruct (Kdec k k0). subst. destruct (Kdec k' k0).  subst. exfalso; apply H; auto. auto.
    destruct (Kdec k' k0). subst. simpl. destruct (Kdec k0 k0). auto. exfalso; apply n0; auto.
    simpl. destruct (Kdec k' k0). subst. exfalso; apply n0; auto. auto.
  Qed.

  Lemma get_set_same: forall m k v, get (set m k v) k = Some v.
  Proof.
   intros. simpl. destruct (Kdec k k); auto. exfalso; apply n; auto.
  Qed.

  Lemma get_set_other: forall m k v k', k' <> k -> get (set m k v) k' = get m k'.
  Proof.
    intros. simpl. destruct (Kdec k' k).  subst k'; exfalso; apply H; auto. apply get_remove_other; auto.
  Qed.

  Lemma get_empty: forall k, get empty k = None.
  Proof.
    intros. auto.
  Qed.

  Lemma in_keys: forall m k, In k (keys m) -> exists v, get m k = Some v.
  Proof.
    induction m; intros.
    inversion H.
    inversion H; simpl.
      destruct a; subst.
        exists v.  simpl. destruct (Kdec k0 k0).  auto. exfalso; apply n; auto.
      destruct a. destruct (Kdec k k0). subst. exists v.  auto.
      apply IHm; auto.
  Qed.

  Lemma keys_in: forall m k v, get m k = Some v -> In k (keys m).
  Proof.
    induction m; intros.
    inv H.
    simpl in H. destruct a. destruct (Kdec k k0). subst k0. simpl. auto.
    simpl. right. eauto.
  Qed.

  Lemma not_in_keys: forall m k, ~ In k (keys m) -> get m k = None.
  Proof.
    induction m; intros.
    auto.
    simpl. destruct a.  destruct (Kdec k k0). subst. exfalso; apply H; simpl; auto.
    apply IHm. intro. apply H. simpl. auto.
  Qed.

  Lemma not_keys_in : forall m k, get m k = None -> ~ In k (keys m).
  Proof.
    induction m; intros.
    auto.
    simpl. destruct a.  simpl.  simpl in H. destruct (Kdec k k0). inv H.
    intro. eapply IHm; eauto. destruct H0.  subst; exfalso; apply n; auto. auto.
  Qed.

  (* Not provable 
  Lemma in_values: forall m v, In v (values m) -> exists k, get m k = Some v. 
  *)

  Lemma values_in: forall m k v, get m k = Some v -> In v (values m). 
  Proof. 
    induction m; intros.
    inv H. 
    simpl in H. destruct a.  destruct (Kdec k k0); subst.  inv H; subst.  left; auto.
    right; eauto. 
  Qed.

  (* some simple consequences  *)
  Lemma in_keys_set: forall m k k' v, In k' (keys (set m k v)) -> k' = k \/ In k' (keys m).
  Proof.
    intros. apply in_keys in H. destruct H as [v0 P].
    destruct (Kdec k' k).  left; auto. right.
    rewrite get_set_other in P; auto.
    eapply keys_in. eauto.
  Qed.

  Lemma set_in_keys: forall m k k' v, k' = k \/ In k' (keys m) -> In k' (keys (set m k v)).
  Proof.
    intros.
    destruct H; subst.
      eapply keys_in. eapply get_set_same; eauto.
      apply in_keys in H. destruct H as [v' P].
      destruct (Kdec k' k); subst.
        eapply keys_in. eapply get_set_same; eauto.
        eapply keys_in. erewrite get_set_other; eauto.
  Qed.

  Lemma in_keys_remove : forall m k k',  In k (keys (remove m k')) -> k <> k' /\ In k (keys m).
  Proof.
    intros. apply in_keys in H. destruct H as [v P].
      destruct (Kdec k' k).
         subst. rewrite get_remove_same in P.  inv P.
         split; auto. erewrite get_remove_other in P; auto. eapply keys_in; eauto.
  Qed.

  Lemma remove_in_keys: forall m k k', In k (keys m) -> k <> k' -> In k (keys (remove m k')).
  Proof.
    intros. apply in_keys in H. destruct H as [v P].
    erewrite <- get_remove_other in P; eauto.
    eapply keys_in; eauto.
  Qed.

End Maps.

Section MapDomains.

  Definition DomEq {K X Y: Type} (m1: map K X) (m2: map K Y) : Prop :=
    forall k, In k (keys m1) <-> In k (keys m2).

  Lemma dom_remove :
    forall K X (DecEq: forall (k1 k2 : K), {k1 = k2} + {k1 <> k2}) m k k1,
      In k1 (keys (remove DecEq m k)) ->
      k <> k1  ->
      In k1 (@keys K X m).
  Proof.
    induction m; intros. inv H. destruct a.
    simpl in *. destruct (DecEq k k0); subst. eauto.
    simpl in H. inv H; eauto.
  Qed.

  Lemma dom_remove' :
    forall K X (DecEq: forall (k1 k2 : K), {k1 = k2} + {k1 <> k2}) m k k1,
      In k1 (keys m) ->
      k <> k1  ->
      In k1 (@keys K X (remove DecEq m k)).
  Proof.
    induction m; intros. inv H. destruct a.
    simpl in *. destruct (DecEq k k0); subst. inv H. intuition.
    eapply IHm; auto. simpl. inv H; auto.
  Qed.

  Lemma DomEq_set :
    forall K X Y (DecEq: forall (k1 k2 : K), {k1 = k2} + {k1 <> k2}) m1 m2,
      @DomEq K X Y m1 m2 ->
      forall k,
        In k (keys m1)  ->
        forall (v: X),
          DomEq (set DecEq m1 k v) m2.
  Proof.
    destruct m1; intros. inv H0. destruct p.
    split; intro.
    - simpl in H1. inv H1. eapply H in H0; auto.
      destruct (DecEq k k0). subst. eapply H in H0.
      destruct (DecEq k0 k1); subst; eauto. eapply dom_remove in H2; eauto. eapply H.
      simpl. right; auto.
      simpl in H2. inv H2; subst. inv H0. simpl in *. intuition.
      eapply H. left; auto.
      destruct (DecEq k1 k); subst. eapply H; eauto.
      eapply H. apply dom_remove in H1; auto. right; auto.
    - destruct (DecEq k k1); auto. subst. simpl; auto.
      destruct (DecEq k k0); subst. simpl. destruct (DecEq k0 k0); [|intuition].
      eapply H in H1. inv H1; auto. right. eapply dom_remove'; eauto.
      simpl. destruct (DecEq k k0); subst; [intuition|]. simpl.
      eapply H in H1. inv H1; subst; simpl in *; auto.
      right; right. eapply dom_remove'; auto.
  Qed.

End MapDomains.

Hint Resolve keys_in : maps.