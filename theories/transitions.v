From Coq Require Import Streams.
From Paco Require Import paco.

(** * Facts about transition relations and transition systems *)

Section Transitions.

Context {state event : Type} (step : state -> option event -> state -> Prop).

(** ** Transition Relations *)

(** Reflexive transitive closure *)
Inductive rt (R : state -> state -> Prop) : state -> state -> Prop :=
  | rt_refl x : rt R x x
  | rt_step x y z : R x y -> rt R y z -> rt R x z.
Hint Constructors rt : core.

Lemma rt_trans (R : state -> state -> Prop):
  forall x y z, rt R x y -> rt R y z -> rt R x z.
Proof.
  induction 1; eauto.
Qed.

(** One step without io *)
Definition nio_step (s1 s2 : state) := step s1 None s2.

(** Multiple steps without io *)
Definition nio_steps := rt nio_step.

Definition steps (s1 : state) (e : event) (s3 : state) : Prop:=
  exists s2, nio_steps s1 s2 /\ step s2 (Some e) s3.

(** Determinitistic step without io *)
Definition det_step (s1 s2 : state) :=
  nio_step s1 s2 /\ (forall e s3, step s1 e s3 -> s3 = s2).

(** Multiple deterministic steps *)
Definition det_steps := rt det_step.

Lemma nio_steps_steps:
  forall s1 s2 e s3,
    nio_steps s1 s2 -> steps s2 e s3 -> steps s1 e s3.
Proof.
  intros * H1 (s2' & H2 & H3).
  eexists s2'. split; auto.
  eapply rt_trans; eauto.
Qed.

Lemma det_steps_nio_steps:
  forall s1 s2, det_steps s1 s2 -> nio_steps s1 s2.
Proof.
  intros * H. induction H.
  - apply rt_refl.
  - eapply rt_step; eauto.
    apply H.
Qed.

Lemma det_steps_steps:
  forall s1 s2 e s3,
    det_steps s1 s2 -> steps s2 e s3 -> steps s1 e s3.
Proof.
  intros * H1 H2.
  eapply nio_steps_steps; eauto.
  now apply det_steps_nio_steps.
Qed.

Definition action_determinist :=
  forall s1 s2 e s3, step s1 None s2 -> step s1 e s3 -> e = None.

(** Determinitistic step without io (and that cannot do any io!!!) *)
Definition nio_det_step (s1 s2 : state) :=
  nio_step s1 s2 /\ (forall e2 s2', step s1 e2 s2' -> s2' = s2 /\ e2 = None).

(** If the transition relation is action-determinisit, deterministic steps cannot do io *)
Lemma det_step_nio:
  action_determinist ->
  forall s1 s2, det_step s1 s2 -> nio_det_step s1 s2.
Proof.
  intros Hdet * [H1 H2]. split; auto.
  intros e2 s2' H. split.
  - eapply H2; eauto.
  - eapply Hdet; eauto.
Qed.

(** ** Runs and Traces *)

Definition run := Stream (state * event).
Definition trace := Stream event.

Inductive is_runF (is_run : state -> run -> Prop) : state -> run -> Prop :=
  | is_run_intro s1 e1 s2 r : steps s1 e1 s2 -> is_run s2 r -> is_runF is_run s1 (Cons (s1, e1) r).
Hint Constructors is_runF : core paco.

Lemma is_runF_mono:
  monotone2 is_runF.
Proof.
  pmonauto.
Qed.
Hint Resolve is_runF_mono : paco core.

Definition is_run := paco2 is_runF bot2.

Inductive is_traceF (is_trace : state -> trace -> Prop) : state -> trace -> Prop :=
  | is_trace_some s1 e1 s2 t : steps s1 e1 s2 -> is_trace s2 t -> is_traceF is_trace s1 (Cons e1 t).
Hint Constructors is_traceF : core paco.

Lemma is_traceF_mono:
  monotone2 is_traceF.
Proof.
  pmonauto.
Qed.
Hint Resolve is_traceF_mono : paco core.

Definition unfold_stream {A} (s : Stream A) : Stream A :=
  match s with
  | Cons x xs => Cons x xs
  end.

Lemma unfold_stream_eq {A}:
  forall (s : Stream A), s = unfold_stream s.
Proof.
  now destruct s.
Qed.

Definition is_trace := paco2 is_traceF bot2.

Lemma is_trace_inv:
  forall s t, is_trace s t -> exists e s', steps s e s' /\ is_trace s' (tl t).
Proof.
  intros s t H.
  pinversion H; subst; simpl.
  now exists e1, s2.
Qed.

Lemma is_run_is_trace:
  forall s r, is_run s r -> is_trace s (map snd r).
Proof.
  pcofix CH.
  intros s [s0 r0] Hr0. pstep.
  pinversion Hr0; subst.
  rewrite unfold_stream_eq. simpl.
  econstructor; eauto.
Qed.

Lemma is_run_step:
  forall s x r, is_run s (Cons x r) -> is_run (fst (hd r)) r.
Proof.
  intros.
  pinversion H; subst.
  pinversion H4; subst.
  simpl in *. pstep. econstructor; eauto.
Qed.

(** ** Simulation Relation *)

Inductive simF (R : state -> state -> Prop) : state -> state -> Prop :=
  | simF_intro s1 s2 :
    (forall e s1', steps s1 e s1' -> exists s2', steps s2 e s2' /\ R s1' s2') ->
    simF R s1 s2.
Hint Constructors simF : core paco.

Lemma simF_mono:
  monotone2 simF.
Proof.
  intros s1 s2 R1 R2 H1 H2.
  constructor; intros * H.
  inversion H1; subst.
  apply H0 in H as (s2' & Hsteps & HR).
  exists s2'. split; eauto.
Qed.
Hint Resolve simF_mono : paco core.

Definition sim := paco2 simF bot2.

Lemma sim_refl:
  forall s, sim s s.
Proof.
  pcofix CH with REC.
  intros s. pstep.
  constructor. eauto.
Qed.

Lemma sim_steps:
  forall s1 e s1' s2, 
    sim s1 s2 ->
    steps s1 e s1' ->
    exists s2', sim s1' s2' /\ steps s2 e s2'.
Proof.
  intros s1 e s1' s2 Hsim Hsteps.
  pinversion Hsim; subst.
  specialize (H _ _ Hsteps) as (s2' & Hsteps' & Hsim').
  pclearbot. now eexists s2'.
Qed.

End Transitions.

Hint Resolve is_runF_mono : paco core.
Hint Resolve is_traceF_mono : paco core.
Hint Constructors rt : core.
Hint Constructors simF : core paco.
Hint Resolve simF_mono : paco core.