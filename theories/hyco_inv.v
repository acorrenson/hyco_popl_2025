From Coq Require Import String ZArith List Streams Lia.
From Paco Require Import paco.
From hyco Require Import transitions tracerel G2.

(** * A version of Hyco for hyperliveness + relational invariants *)

(** IMPORTANT: The soundness proof of Hyco relies on Classical Choice *)
From Coq Require Import Logic.ClassicalChoice.

Section Hyco_def.

(**
  We assume that we are given an event labeled transition system defined by
  a relation [step]
*)
Context {state event : Type} (step : state -> option event -> state -> Prop).

(** ** Definition of Hyco *)

Inductive hycoF (phi : event -> event -> Prop) (hyco : state -> state -> Prop) : state -> state -> Prop :=
  | hycoF_intro s1 s2 :
    (forall e1 s1', steps step s1 e1 s1' -> exists e2 s2', steps step s2 e2 s2' /\ phi e1 e2 /\ hyco s1' s2')
    -> hycoF phi hyco s1 s2.
Hint Constructors hycoF : paco core.

(** [hycoF] is monotone *)
Lemma hycoF_mono (phi : event -> event -> Prop):
  monotone2 (hycoF phi).
Proof.
  intros s1 s2 R1 R2 H1 H2. constructor.
  intros e1 s1' H.
  inversion H1; subst.
  specialize (H0 e1 s1' H) as (e2 & s2' & H').
  exists e2, s2'. firstorder.
Qed.
Hint Resolve hycoF_mono : paco core.

(** Hyco is the following coinductive relation (Corresponds to [fei] in the paper) *)
Definition hyco (phi : event -> event -> Prop) :=
  Glock (hycoF phi).

Definition uhyco (phi : event -> event -> Prop) :=
  Gunlock (hycoF phi).

(** ** Soundness Proof *)

Record proof_state (phi : event -> event -> Prop) : Type := PROOF_STATE {
  get_s1  : state;
  get_r1  : run;
  get_s2  : state;
  Hrun    : is_run step get_s1 get_r1;
  Hhyco   : hyco phi bot2 get_s1 get_s2;
}.
Arguments get_s1 {_}.
Arguments get_s2 {_}.
Arguments get_r1 {_}.

Definition get_e1 {phi} (st : proof_state phi) : event :=
  snd (hd (get_r1 st)).

Definition get_s1' {phi} (st : proof_state phi) : state :=
  fst (hd (tl (get_r1 st))).

Record proof_state' (phi : event -> event -> Prop) : Type := PROOF_STATE' {
  get_next   :> proof_state phi;
  get_e2     : event;
}.
Arguments get_e2 {_}.

Definition is_proof_step {phi} (st1 : proof_state phi) (st2 : proof_state' phi) :=
  get_s1 st2 = get_s1' st1 /\
  get_r1 st2 = tl (get_r1 st1) /\
  steps step (get_s2 st1) (get_e2 st2) (get_s2 st2) /\
  phi (get_e1 st1) (get_e2 st2).

Lemma proof_step {phi}:
  forall (st1 : proof_state phi),
    exists (st2 : proof_state' phi), is_proof_step st1 st2.
Proof.
  intros [s1 r1 s2 Hrun Hyco].
  unfold is_proof_step. simpl.
  unfold get_e1, get_s1'. simpl.
  pinversion Hrun; subst. simpl.
  pinversion H0; subst.
  apply Glock_unfold in Hyco; auto.
  inversion Hyco; subst.
  specialize (H3 _ _ H) as (e2 & s2' & (H3 & H4 & H5)).
  eexists (PROOF_STATE' _ (PROOF_STATE _ _ _ _ _ _) e2). simpl.
  repeat split; eauto.
  Unshelve. simpl. pstep. econstructor; eauto.
  clear - H5. now pclearbot.
Qed.

(** Hyco can prove hyperliveness properties of the form
    "\forall\exists" followed by a relational invariant
*)
Lemma hyco_sound:
  forall Q s1 s2,
  hyco Q bot2 s1 s2 ->
  forall_exists step s1 s2 (always Q).
Proof.
  intros Q.
  pose proof (@choice _ _ _ (@proof_step Q)) as [f Hf].
  intros s1 s2 H r1 Hr1.
  pose (build_trace := cofix build_trace p :=
    Cons (get_e2 (f p)) (build_trace (f p))
  ).
  exists (build_trace (PROOF_STATE Q s1 r1 s2 Hr1 H)).
  split.
  - generalize s1 s2 r1 H Hr1. clear s1 s2 r1 H Hr1.
    pcofix CH.
    intros s1 s2 r1 H Hr1. pstep.
    rewrite unfold_stream_eq. cbn.
    specialize (Hf (PROOF_STATE Q s1 r1 s2 Hr1 H)) as (H1 & H2 & H3 & H4).
    destruct (f _) as [[s1' r1' s2' Hr1' Hyco' ] e2].
    simpl in *. unfold get_e1, get_e2, get_s1' in *. simpl in *.
    econstructor; eauto.
  - generalize s1 s2 r1 H Hr1. clear s1 s2 r1 H Hr1.
    pcofix CH.
    intros s1 s2 r1 H Hr1. pstep.
    rewrite (unfold_stream_eq (map snd r1)). cbn.
    rewrite (unfold_stream_eq (build_trace _)). cbn.
    specialize (Hf (PROOF_STATE Q s1 r1 s2 Hr1 H)) as (H1 & H2 & H3 & H4).
    destruct (f _) as [[s1' r1' s2' Hr1' Hyco' ] e2].
    simpl in *. unfold get_e1, get_e2, get_s1' in *. simpl in *.
    constructor; subst; cbn; auto.
Qed.

(** ** Proof Rules and Reasoning Principles *)

Notation "'HYCO' [ r ] s1 '|' s2 '⊨' P" := (hyco P r s1 s2) (at level 80).
Notation "'UHYCO' [ r ] s1 '|' s2 '⊨' P" := (uhyco P r s1 s2) (at level 80).

Lemma hyco_step:
  forall R s1 s2 Q,
    (forall e1 s1', steps step s1 e1 s1' -> exists e2 s2',
      steps step s2 e2 s2' /\ Q e1 e2 /\ UHYCO [R] s1' | s2' ⊨ Q) ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros.
  apply Glock_step; auto.
Qed.

Lemma hyco_cycle:
  forall R s1 s2 Q,
    R s1 s2 -> UHYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros. now apply Gunlock_cycle.
Qed.

Lemma uhyco_hyco:
  forall R s1 s2 Q,
    HYCO [R] s1 | s2 ⊨ Q -> UHYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros * H. now apply Gunlock_lock.
Qed.

Lemma hyco_step_l:
  forall R s1 s1' s2 Q,
    action_determinist step ->
    det_step step s1 s1' ->
    HYCO [R] s1' | s2 ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros * Hadet [Hnio_step Hdet] H.
  apply Glock_step; auto. constructor.
  intros e1 s1_2 (s1_1 & Hsteps & Hstep).
  inversion Hsteps; subst.
  - now eapply Hadet in Hstep; eauto.
  - apply Hdet in H0; subst.
    apply Glock_unfold in H; auto.
    inversion H; subst.
    apply H0.
    eapply nio_steps_steps; eauto.
    econstructor. split; eauto.
    apply rt_refl.
Qed.

Lemma hyco_steps_l:
  forall R s1 s1' s2 Q,
    action_determinist step ->
    det_steps step s1 s1' ->
    HYCO [R] s1' | s2 ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros * Hadet H1 H2.
  induction H1; subst; auto.
  apply IHrt in H2. clear IHrt.
  eapply hyco_step_l; eauto.
Qed.

Lemma hyco_steps_r:
  forall R s1 s2 s2' Q,
    nio_steps step s2 s2' ->
    HYCO [R] s1 | s2' ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros * H1 H2.
  apply Glock_step; auto. constructor.
  intros e1 s1'' Hsteps.
  apply Glock_unfold in H2; auto.
  inversion H2; subst. clear H2.
  specialize (H _ _ Hsteps) as (e2 & s2'' & (?H & ?H & ?H)).
  eexists _, _. split; eauto.
  eapply nio_steps_steps; eauto.
Qed.

Lemma hyco_inv:
  forall INV H s1 s2 phi,
    INV s1 s2 ->
    (forall s1 s2, INV s1 s2 -> HYCO [H \2/ INV] s1 | s2 ⊨ phi) ->
    HYCO [H] s1 | s2 ⊨ phi.
Proof.
  intros * H1 H2.
  eapply Glock_incr; eauto.
Qed.

Inductive sim_clo (R : rel2 state (fun _ => state)) : rel2 state (fun _ => state) :=
  | sim_clo_intro s1 s1' s2 s2' : sim step s1 s1' -> sim step s2' s2 -> R s1' s2' -> sim_clo R s1 s2.
Hint Constructors sim_clo : paco core.

Lemma sim_clo_mon:
  monotone2 sim_clo.
Proof.
  pmonauto.
Qed.
Hint Resolve sim_clo_mon : core paco.

Lemma hyco_sim_clo_compat:
  forall Q, compatible2 (hycoF Q) sim_clo.
Proof.
  intros Q. constructor; auto.
  intros R s1_ s2_ [s1 s1' s2 s2' Hsim1 Hsim2 H]. clear s1_ s2_.
  inversion_clear H as [ ? ? H'].
  constructor. eintros * (s2'' & Hsim' & (e2 & s2''' & Hsteps & Hphi & Hrec)%H')%sim_steps; eauto.
  eapply sim_steps in Hsim2 as (s3 & Hsim3 & Hsteps3); eauto.
  eexists e2, s3. split; auto. split; auto.
  econstructor; eauto.
Qed.
Hint Resolve hyco_sim_clo_compat : core.

Lemma internalize_sim:
  forall s1 s2, HYCO [bot2] s1 | s2 ⊨ eq -> sim step s1 s2.
Proof.
  pcofix CH with REC.
  intros s1 s2 H.
  pstep. constructor. intros * Hsteps.
  apply Glock_unfold in H; auto.
  inversion_clear H as [ ? ? H'].
  specialize (H' _ _ Hsteps) as (e2 & s2' & (H1 & -> & H3)).
  pclearbot. eexists _. split; eauto.
Qed.

Lemma hyco_sim_left:
  forall Q R s1 s1' s2,
    sim step s1 s1' ->
    HYCO [R] s1' | s2 ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros Q R s1 s1' s2 Hsim H.
  apply Glock_up_to with sim_clo; auto.
  econstructor; eauto using sim_refl.
Qed.

Lemma hyco_sim_left_internal:
  forall Q R s1 s1' s2,
    HYCO [bot2] s1 | s1' ⊨ eq ->
    HYCO [R] s1' | s2 ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros Q R s1 s1' s2 Hsim H.
  eapply hyco_sim_left; eauto using internalize_sim.
Qed.

Lemma hyco_sim_right:
  forall Q R s1 s2 s2',
    sim step s2' s2 ->
    HYCO [R] s1 | s2' ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros Q R s1 s1' s2 Hsim H.
  eapply Glock_up_to with sim_clo; auto.
  econstructor; eauto using sim_refl.
Qed.

Lemma hyco_sim_right_internal:
  forall Q R s1 s2 s2',
    HYCO [bot2] s2' | s2 ⊨ eq ->
    HYCO [R] s1 | s2' ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros Q R s1 s1' s2 Hsim H.
  eapply hyco_sim_right; eauto using internalize_sim.
Qed.

End Hyco_def.

#[export]
Hint Resolve hycoF_mono : paco core.