From Coq Require Import Logic.ClassicalChoice.
From Coq Require Import Classes.Morphisms.
From Coq Require Import String ZArith List Streams Lia.
From Paco Require Import paco.
From hyco Require Import transitions tracerel G3.

(** * A version of Hyco for hyperliveness + safety relations *)

Section Hyco_def.

(** ** Definition of Hyco *)

Context {state event : Type} (step : state -> option event -> state -> Prop).

Definition spec := @spec event.

Definition equiv (phi1 phi2 : spec) :=
  phi1 <2= phi2 /\ phi2 <2= phi1.
Infix "≡" := equiv (at level 80, no associativity).

Definition next (e1 e2 : event) (phi : spec) (R : state -> state -> spec -> Prop) :=
  fun s1 s2 => non_empty (deriv e1 e2 phi) /\ R s1 s2 (deriv e1 e2 phi).

Inductive hycoF (hyco : state -> state -> spec -> Prop) : state -> state -> spec -> Prop :=
  | hycoF_intro s1 s2 phi :
    (forall e1 s1',
      steps step s1 e1 s1' ->
      exists e2 s2', steps step s2 e2 s2' /\ non_empty (deriv e1 e2 phi) /\ hyco s1' s2' (deriv e1 e2 phi)
    ) -> hycoF hyco s1 s2 phi.
Hint Constructors hycoF : paco core.

Lemma hycoF_mono:
  monotone3 hycoF.
Proof.
  intros s1 s2 R R1 R2 H1 H2. constructor.
  intros e1 s1' H.
  inversion H1; subst.
  specialize (H0 e1 s1' H) as (e2 & s2' & H').
  exists e2, s2'. firstorder.
Qed.
Hint Resolve hycoF_mono : paco core.

(** The coinductive relation (Corresponds to [fe] in the paper) *)
Definition hyco :=
  Glock hycoF.

Definition uhyco :=
  Gunlock hycoF.

(** ** Soundness Proof *)

Record proof_state : Type := PROOF_STATE {
  get_R   : spec;
  get_s1  : state;
  get_r1  : run;
  get_s2  : state;
  Hrun    : is_run step get_s1 get_r1;
  Hhyco   : hyco bot3 get_s1 get_s2 get_R;
}.

Definition get_e1 (st : proof_state) : event :=
  snd (hd (get_r1 st)).

Definition get_s1' (st : proof_state) : state :=
  fst (hd (tl (get_r1 st))).

Record proof_state' : Type := PROOF_STATE' {
  get_next   :> proof_state;
  get_e2     : event;
}.

Definition is_proof_step (st1 : proof_state) (st2 : proof_state') :=
  get_R st2  = deriv (get_e1 st1) (get_e2 st2) (get_R st1) /\
  get_s1 st2 = get_s1' st1 /\
  get_r1 st2 = tl (get_r1 st1) /\
  steps step (get_s2 st1) (get_e2 st2) (get_s2 st2) /\
  non_empty (deriv (get_e1 st1) (get_e2 st2) (get_R st1)).

Lemma proof_step:
  forall (st1 : proof_state),
    exists (st2 : proof_state'), is_proof_step st1 st2.
Proof.
  intros [R s1 r1 s2 Hrun Hyco].
  unfold is_proof_step. simpl.
  unfold get_e1, get_s1'. simpl.
  pinversion Hrun; subst. simpl.
  pinversion H0; subst.
  apply Glock_unfold in Hyco; auto.
  inversion Hyco; subst.
  specialize (H3 _ _ H) as (e2 & s2' & (H3 & H4 & H5)).
  eexists (PROOF_STATE' (PROOF_STATE _ _ _ _ _ _) e2). simpl.
  repeat split; eauto.
  Unshelve. simpl. pstep. econstructor; eauto.
  clear - H5. now pclearbot.
Qed.

(** Hyco can prove hyperliveness properties of the form
    "\forall\exists" followed by a safety relation
*)
Lemma hyco_sound:
  forall s1 s2 (phi : spec), safety phi -> hyco bot3 s1 s2 phi -> forall_exists step s1 s2 phi.
Proof.
  pose proof (@choice _ _ _ proof_step) as [f Hf].
  intros s1 s2 phi Hsafe H r1 Hr1.
  pose (build_trace := cofix build_trace p :=
    Cons (get_e2 (f p)) (build_trace (f p))
  ).
  exists (build_trace (PROOF_STATE phi s1 r1 s2 Hr1 H)).
  split.
  - generalize s1 s2 r1 phi Hsafe H Hr1. clear s1 s2 r1 phi Hsafe H Hr1.
    pcofix CH.
    intros s1 s2 r1 phi Hsafe H Hr1. pstep.
    rewrite unfold_stream_eq. cbn.
    specialize (Hf (PROOF_STATE phi s1 r1 s2 Hr1 H)) as (H1 & H2 & H3 & H4 & H5).
    destruct (f _) as [[R' s1' r1' s2' Hr1' Hyco' ] e2].
    simpl in *. unfold get_e1, get_e2, get_s1' in *. simpl in *.
    subst. econstructor; eauto.
  - apply Hsafe. generalize s1 s2 r1 phi Hsafe H Hr1. clear s1 s2 r1 phi Hsafe H Hr1.
    pcofix CH.
    intros s1 s2 r1 phi Hsafe H Hr1. pstep.
    rewrite (unfold_stream_eq (build_trace _)).
    rewrite (unfold_stream_eq (map snd _)). cbn.
    specialize (Hf (PROOF_STATE phi s1 r1 s2 Hr1 H)) as (H1 & H2 & H3 & H4 & H5).
    destruct (f _) as [[R' s1' r1' s2' Hr1' Hyco' ] e2].
    simpl in *. unfold get_e1, get_e2, get_s1' in *. simpl in *.
    subst. econstructor; eauto.
Qed.

(** ** Proof Rules and Reasoning Principles *)

Notation "'HYCO' [ H ] s1 '|' s2 '⊨' phi" := (hyco H s1 s2 phi) (at level 80).
Notation "'HYCO' [ H ] e1 '▷' s1 '|' e2 '▷' s2 '⊨' phi" := (next e1 e2 phi (uhyco H) s1 s2) (at level 80).
Notation "'UHYCO' [ H ] s1 '|' s2 '⊨' phi" := (uhyco H s1 s2 phi) (at level 80).

Lemma hyco_step:
  forall R s1 s2 Q,
    (forall e1 s1', steps step s1 e1 s1' -> exists e2 s2',
      steps step s2 e2 s2' /\ HYCO [R] e1 ▷ s1' | e2 ▷ s2' ⊨ Q) ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros.
  apply Glock_step; auto.
Qed.

Lemma hyco_cycle:
  forall R s1 s2 Q,
    R s1 s2 Q -> UHYCO [R] s1 | s2 ⊨ Q.
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
  specialize (H _ _ Hsteps) as (e2 & s2'' & (? & ? & ?)).
  eexists _, _. split; eauto.
  eapply nio_steps_steps; eauto.
Qed.

Inductive str_clo (R : state -> state -> spec -> Prop) : state -> state -> spec -> Prop :=
  | str_clo_intro s1 s2 phi1 phi2 : phi1 <2= phi2 -> R s1 s2 phi1 -> str_clo R s1 s2 phi2.
Hint Constructors str_clo : paco.

Lemma str_clo_mon:
  monotone3 str_clo.
Proof.
  pmonauto.
Qed.
Hint Resolve str_clo_mon : paco core.

Lemma hyco_str_clo_compat:
  compatible3 hycoF str_clo.
Proof.
  constructor; auto.
  intros R s1 s2 phi Hclo. constructor.
  intros * Hsteps. inversion Hclo; subst.
  inversion H0; subst.
  specialize (H1 _ _ Hsteps) as (e2 & s2' & (H1 & H2 & H3)).
  eexists _, _. repeat split; eauto.
  econstructor; cycle 1; eauto.
Qed.
Hint Resolve hyco_str_clo_compat : paco core.

Lemma hyco_stronger_relation:
  forall (Q1 Q2 : spec),
    Q1 <2= Q2 ->
    forall R s1 s2, HYCO [R] s1 | s2 ⊨ Q1 -> HYCO [R] s1 | s2 ⊨ Q2.
Proof.
  intros * H1 * H2.
  apply Glock_up_to with (clo := str_clo); auto.
  econstructor; eauto.
Qed.

Inductive sim_clo (R : rel3 state (fun _ => state) (fun _ _ => spec)) : rel3 state (fun _ => state) (fun _ _ => spec) :=
  | sim_clo_intro phi s1 s1' s2 s2' : sim step s1 s1' -> sim step s2' s2 -> R s1' s2' phi -> sim_clo R s1 s2 phi.
Hint Constructors sim_clo : paco core.

Lemma sim_clo_mon:
  monotone3 sim_clo.
Proof.
  pmonauto.
Qed.
Hint Resolve sim_clo_mon : core paco.

Lemma hyco_sim_clo_compat:
  compatible3 hycoF sim_clo.
Proof.
  constructor; auto.
  intros R s1_ s2_ phi_ [phi s1 s1' s2 s2' Hsim1 Hsim2 H]. clear s1_ s2_ phi_.
  inversion_clear H as [ ? ? ? H'].
  constructor. eintros * (s2'' & Hsim' & (e2 & s2''' & Hsteps & Hphi & Hrec)%H')%sim_steps; eauto.
  eapply sim_steps in Hsim2 as (s3 & Hsim3 & Hsteps3); eauto.
  eexists e2, s3. split; auto. split; auto.
  econstructor; eauto.
Qed.
Hint Resolve hyco_sim_clo_compat : core.

Lemma internalize_sim:
  forall s1 s2, HYCO [bot3] s1 | s2 ⊨ eq -> sim step s1 s2.
Proof.
  pcofix CH with REC.
  intros s1 s2 H.
  pstep. constructor. intros * Hsteps.
  apply Glock_unfold in H; auto.
  inversion_clear H as [ ? ? ? H'].
  specialize (H'  _ _ Hsteps) as (e2 & s2' & (H1 & (t1 & t2 & [=->_]) & H3)).
  eexists _. split; eauto.
  right. apply CH.
  apply Glock_up_to with str_clo; auto.
  econstructor; cycle 1.
  apply H3. clear.
  now intros [e1 t1] [e2' t2] [=->->].
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
    HYCO [bot3] s1 | s1' ⊨ eq ->
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
    HYCO [bot3] s2' | s2 ⊨ eq ->
    HYCO [R] s1 | s2' ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros Q R s1 s1' s2 Hsim H.
  eapply hyco_sim_right; eauto using internalize_sim.
Qed.

Lemma hyco_always:
  forall phi e1 e2 R s1 s2,
    phi e1 e2 ->
    UHYCO [R] s1 | s2 ⊨ always phi ->
    HYCO [R] e1 ▷ s1 | e2 ▷ s2 ⊨ always phi.
Proof.
  intros * H1 H2. split.
  - exists (cofix t := Cons e1 t), (cofix t := Cons e2 t).
    red. pstep. constructor; auto. left.
    pcofix CH. pstep.
    rewrite (unfold_stream_eq (cofix t := Cons e1 _)).
    rewrite (unfold_stream_eq (cofix t := Cons e2 _)).
    cbn. constructor; auto.
  - apply Gunlock_up_to with str_clo; auto.
    econstructor; cycle 1.
    apply H2. auto using deriv_always.
Qed.

Lemma hyco_wuntil_now:
  forall phi1 phi2 e1 e2 R s1 s2,
    phi2 e1 e2 ->
    UHYCO [R] s1 | s2 ⊨ (fun _ _ => True) ->
    HYCO [R] e1 ▷ s1 | e2 ▷ s2 ⊨ wuntil (now phi1) (now phi2).
Proof.
  intros * H1 H2. split.
  - exists (cofix t := Cons e1 t), (cofix t := Cons e2 t).
    pstep. now left.
  - apply Gunlock_up_to with str_clo; auto.
    econstructor; cycle 1.
    apply H2. auto using deriv_wuntil.
Qed.

Lemma hyco_wuntil_later:
  forall phi1 phi2 e1 e2 R s1 s2,
    phi1 e1 e2 ->
    HYCO [R] s1 | s2 ⊨ wuntil (now phi1) (now phi2) ->
    HYCO [R] e1 ▷ s1 | e2 ▷ s2 ⊨ wuntil (now phi1) (now phi2).
Proof.
  intros * H1 H2. split.
  - exists (cofix t := Cons e1 t), (cofix t := Cons e2 t).
    pstep. right; simpl; auto.
    left. pcofix CH. pstep.
    rewrite (unfold_stream_eq (cofix t := Cons e1 _)).
    rewrite (unfold_stream_eq (cofix t := Cons e2 _)).
    cbn. right; auto.
  - apply Gunlock_up_to with str_clo; auto.
    econstructor; cycle 1.
    apply Gunlock_lock; auto.
    apply H2. auto using deriv_wuntil.
Qed.

End Hyco_def.

Hint Resolve hycoF_mono : paco core.