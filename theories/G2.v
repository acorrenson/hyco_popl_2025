From Paco Require Import paco.

(*
  An interface to [gpaco] that support up-to reasoning but ressembles 
  the simpler interface of [paco]
*)

Section G.

(** [Glock] is just an instance of [gpaco] where the closure is the companion
    and the left parameter is set to be [bot] (i.e., the hypothesis is guarded)
*)
Definition Glock {T} (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)) h :=
  gpaco2 f (cpn2 f) bot2 h.

(** [Gunlock] is just an instance of [gpaco] where the closure is the companion
    and the left AND right parameter are the same (i.e., the hypothesis is unguarded)
*)
Definition Gunlock {T} (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)) h :=
  gpaco2 f (cpn2 f) h h.

(** If the hypothesis is currently unguarded, we can use it to conclude a proof. *)
Lemma Gunlock_cycle:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h, h <2= Gunlock f h.
Proof.
  now gbase.
Qed.

(** If the hypothesis is currently unguarded, we can always restore the guard. *)
Lemma Gunlock_lock:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h, Glock f h <2= Gunlock f h.
Proof.
  intros * H2 h x1 x2 Hx. simpl in *.
  now eapply gpaco2_mon_gen; eauto.
Qed.

Lemma rclo_cpn:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)) R,
    monotone2 f ->
    rclo2 (cpn2 f) R <2= cpn2 f R.
Proof.
  intros T f R x1 x2 H. simpl in *.
  econstructor; eauto.
  apply rclo2_compat; auto.
  apply cpn2_compat; auto.
Qed.

Lemma Glock_unfold:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h, Glock f h <2= f (Gunlock f h).
Proof.
  intros * Hmon h x1 x2 Hx. simpl in *.
  gunfold Hx. apply rclo_cpn in Hx; auto.
  eapply Hmon.
  eapply cpn2_compat; auto.
  eapply cpn2_mon; eauto.
  - intros y1 y2 [H | []]. apply H.
  - intros y1 y2 H. gclo.
    eapply cpn2_mon; eauto.
    clear - Hmon. intros y1 y2 H.
    eapply gpaco2_mon_gen; eauto.
    all: now intros ? ? [ | []].
Qed.

(** [Glock] supports reasoning up-to any compatible closure *)
Lemma Glock_up_to:
  forall {T} {f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)} (clo : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    compatible2 f clo ->
    forall h, clo (Glock f h) <2= Glock f h.
Proof.
  intros * Hmon Hcomp h x1 x2 Hx.
  gclo. eapply cpn2_greatest; eauto.
Qed.

(** Up-to reasaoning can also be applied if the hypothesis is unlocked *)
Lemma Gunlock_up_to:
  forall T (f clo : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    compatible2 f clo ->
    forall h, clo (Gunlock f h) <2= Gunlock f h.
Proof.
  intros * Hmon Hcomp h x1 x2 Hx.
  gclo. eapply cpn2_greatest; eauto.
Qed.

(** [Glock] can be used instead of [paco] *)
Lemma Glock_init:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    Glock f bot2 <2= paco2 f bot2.
Proof.
  intros * Hmon.
  apply gpaco2_init; eauto.
  apply compat2_wcompat; auto.
  now apply cpn2_compat.
Qed.

Lemma Gunlock_init:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    Gunlock f bot2 <2= paco2 f bot2.
Proof.
  intros * Hmon.
  apply gpaco2_init; eauto.
  apply compat2_wcompat; auto.
  now apply cpn2_compat.
Qed.

(** [Glock] has a simple step rule to realease the guard. *)
Lemma Glock_step:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h, f (Gunlock f h) <2= Glock f h.
Proof.
  intros * Hmon; simpl in *.
  intros h x1 x2 Hx.
  gstep.
  eapply Hmon; eauto.
Qed.

(** [Glock] can also mimic the step rule of [paco] *)
Lemma Glock_step_2:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h, f (h \2/ Glock f h) <2= Glock f h.
Proof.
  intros * Hmon; simpl in *.
  intros h x1 x2 Hx.
  gstep.
  eapply Hmon; eauto.
  clear - Hmon. intros x1 x2 Hx.
  destruct Hx as [Hx | Hx]; auto.
  now gbase.
  now eapply gpaco2_mon_gen; eauto.
Qed.

(** ** Incremental Reasoning *)

(** [Glock] has a simple accumulation rule. *)
Lemma Glock_acc:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h X, X <2= Glock f (h \2/ X) -> X <2= Glock f h.
Proof.
  intros * Hmon; simpl in *.
  intros h X Hx y1 y2 Hy; auto.
  eapply gpaco2_cofix; cycle 1.
  - intros rr H1 H2 z1 z2 Hz.
    eapply gpaco2_mon_gen.
    apply Hx. all: auto.
    apply Hz.
    intros ? ? [? | ?]; auto.
  - apply Hy.
  - apply Hmon.
Qed.

(** [Gunlock] can also accumulate. *)
Lemma Gunlock_acc:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h X, X <2= Glock f (h \2/ X) -> X <2= Gunlock f h.
Proof.
  intros * H1 * H2 x1 x2 Hx. simpl in *.
  apply Gunlock_lock; auto.
  eapply Glock_acc; eauto.
Qed.

(** Reformulation of [Glock_acc] *)
Lemma Glock_incr:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h h' x1 x2,
      h' x1 x2 ->
      (forall x1 x2, h' x1 x2 -> Glock f (h \2/ h') x1 x2) ->
      Glock f h x1 x2.
Proof.
  intros * Hmon; simpl in *.
  intros h h' x1 x2 H1 H2.
  eapply Glock_acc; eauto.
Qed.

(** Reformulation of [Gunlock_acc] *)
Lemma Gunlock_incr:
  forall T (f : rel2 T (fun _ => T) -> rel2 T (fun _ => T)),
    monotone2 f ->
    forall h h' x1 x2,
      h' x1 x2 ->
      (forall x1 x2, h' x1 x2 -> Glock f (h \2/ h') x1 x2) ->
      Gunlock f h x1 x2.
Proof.
  intros * Hmon; simpl in *.
  intros h h' x1 x2 H1 H2.
  eapply Gunlock_acc; eauto.
Qed.

End G.