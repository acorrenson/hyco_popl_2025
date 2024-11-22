From Paco Require Import paco.

(*
  An interface to [gpaco] that support up-to reasoning but ressembles 
  the simpler interface of [paco]
*)

Section G.

Definition FUNC (T P : Type) := rel3 T (fun _ => T) (fun _ _ => P) -> rel3 T (fun _ => T) (fun _ _ => P).

(** [Glock] is just an instance of [gpaco] where the closure is the companion
    and the left parameter is set to be [bot] (i.e., the hypothesis is guarded)
*)
Definition Glock {T P} (f : FUNC T P) h :=
  gpaco3 f (cpn3 f) bot3 h.

(** [Gunlock] is just an instance of [gpaco] where the closure is the companion
    and the left AND right parameters are the same (i.e., the hypothesis is unguarded)
*)
Definition Gunlock {T P} (f : FUNC T P) h :=
  gpaco3 f (cpn3 f) h h.


(** If the hypothesis is currently unguarded, we can use it to conclude a proof. *)
Lemma Gunlock_cycle { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h, h <3= Gunlock f h.
Proof.
  now gbase.
Qed.

(** If the hypothesis is currently unguarded, we can always restore the guard. *)
Lemma Gunlock_lock { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h, Glock f h <3= Gunlock f h.
Proof.
  intros f Hmon h x1 x2 x3 Hx. simpl in *.
  now eapply gpaco3_mon_gen; eauto.
Qed.

Lemma rclo_cpn { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall R, rclo3 (cpn3 f) R <3= cpn3 f R.
Proof.
  intros R * H. simpl in *.
  econstructor; eauto.
  apply rclo3_compat; auto.
  apply cpn3_compat; auto.
Qed.

Lemma Glock_unfold { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h, Glock f h <3= f (Gunlock f h).
Proof.
  intros f Hmon h * H. simpl in *.
  gunfold H. apply rclo_cpn in H; auto.
  eapply Hmon.
  eapply cpn3_compat; auto.
  eapply cpn3_mon; eauto.
  - intros * [? | []]; eauto.
  - intros * ?. gclo.
    eapply cpn3_mon; eauto.
    intros * ?.
    eapply gpaco3_mon_gen; eauto.
    all: now intros * [ | []].
Qed.

Lemma Gunlock_bot_inv { T P }:
  forall (f : FUNC T P),
  monotone3 f ->
  Gunlock f bot3 <3= Glock f bot3.
Proof.
  now intros f Hmon x1 x2 x3 H.
Qed.

(** [Glock] supports reasoning up-to any compatible closure *)
Lemma Glock_up_to { T P }:
  forall (f clo : FUNC T P),
    monotone3 f ->
    compatible3 f clo ->
    forall h, clo (Glock f h) <3= Glock f h.
Proof.
  intros * Hcomp h * H.
  gclo. eapply cpn3_greatest; eauto.
Qed.

(** Up-to reasaoning can even be applied if the hypothesis is unlocked *)
Lemma Gunlock_up_to { T P }:
  forall (f clo : FUNC T P),
    monotone3 f ->
    compatible3 f clo ->
    forall h, clo (Gunlock f h) <3= Gunlock f h.
Proof.
  intros * Hcomp h * Hx.
  gclo. eapply cpn3_greatest; eauto.
Qed.

(** [Glock] can be used instead of [paco] *)
Lemma Glock_init { T P }:
  forall (f : FUNC T P),
    monotone3 f -> Glock f bot3 <3= paco3 f bot3.
Proof.
  intros f H.
  apply gpaco3_init; eauto.
  apply compat3_wcompat; auto.
  now apply cpn3_compat.
Qed.

Lemma Gunlock_init { T P }:
  forall (f : FUNC T P),
    monotone3 f -> Gunlock f bot3 <3= paco3 f bot3.
Proof.
  intros f H.
  apply gpaco3_init; eauto.
  apply compat3_wcompat; auto.
  now apply cpn3_compat.
Qed.

(** [Glock] has a simple step rule to realease the guard. *)
Lemma Glock_step { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h, f (Gunlock f h) <3= Glock f h.
Proof.
  intros f Hmon h * H.
  gstep. eapply Hmon; eauto.
Qed.

(** [Glock] can also mimic the step rule of [paco] *)
Lemma Glock_step_2 { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h, f (h \3/ Glock f h) <3= Glock f h.
Proof.
  intros f Hmon h * H.
  gstep. eapply Hmon; eauto.
  clear - Hmon. intros * [H | H].
  - now gbase.
  - now eapply gpaco3_mon_gen; eauto.
Qed.

(** [Glock] has a simple accumulation rule. *)
Lemma Glock_acc { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h X, X <3= Glock f (h \3/ X) -> X <3= Glock f h.
Proof.
  intros * Hmon h X H1 * H2; auto.
  eapply gpaco3_cofix; cycle 1.
  - intros. eapply gpaco3_mon_gen.
    apply H1. all: eauto.
    intros * [? | ?]; auto.
  - auto.
  - apply Hmon.
Qed.

(** [Gunlock] can also accumulate. *)
Lemma Gunlock_acc { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h X, X <3= Glock f (h \3/ X) -> X <3= Gunlock f h.
Proof.
  intros * Hmon * H1 * H2. simpl in *.
  apply Gunlock_lock; auto.
  eapply Glock_acc; eauto.
Qed.

(** Reformulation of [Glock_acc] *)
Lemma Glock_incr { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h h' x1 x2 x3,
      h' x1 x2 x3 ->
      (forall x1 x2 x3, h' x1 x2 x3 -> Glock f (h \3/ h') x1 x2 x3) ->
      Glock f h x1 x2 x3.
Proof.
  intros * Hmon h h' * H1 H2.
  eapply Glock_acc; eauto.
Qed.

(** Reformulation of [Gunlock_acc] *)
Lemma Gunlock_incr { T P }:
  forall (f : FUNC T P),
    monotone3 f ->
    forall h h' x1 x2 x3,
      h' x1 x2 x3 ->
      (forall x1 x2 x3, h' x1 x2 x3 -> Glock f (h \3/ h') x1 x2 x3) ->
      Gunlock f h x1 x2 x3.
Proof.
  intros * Hmon h h' * H1 H2.
  eapply Gunlock_acc; eauto.
Qed.

End G.