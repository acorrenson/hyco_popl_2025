From Coq Require Import ZArith String Lia.
From hyco Require Import hyco_inv imp_io transitions tracerel G2.
From Paco Require Import paco.

(** * An instance of Hyco for programs with IO *)

Notation "'HYCO' [ r ] s1 '|' s2 '⊨' P" := (hyco step P r s1 s2) (at level 80).
Notation "'UHYCO' [ r ] s1 '|' s2 '⊨' P" := (uhyco step P r s1 s2) (at level 80).

(** ** Asynchronous Rules *)

Lemma hyco_exec_l:
  forall R s1 s2 Q,
    HYCO [R] (exec_det_step s1) | s2 ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros.
  eapply hyco_steps_l; eauto using action_determinism.
  apply exec_det_step_sound.
Qed.

Lemma hyco_exec_r:
  forall R s1 s2 Q,
    HYCO [R] s1 | (exec_det_step s2) ⊨ Q ->
    HYCO [R] s1 | s2 ⊨ Q.
Proof.
  intros.
  eapply hyco_steps_r; eauto.
  apply det_steps_nio_steps.
  apply exec_det_step_sound.
Qed.

(** ** Handling IO *)

Lemma hyco_input_input:
  forall R m1 x1 k1 m2 x2 k2 Q,
    (forall v1, exists v2, Q (EINPUT x1 v1) (EINPUT x2 v2) /\ UHYCO [R] (resume (update m1 x1 v1) k1) | (resume (update m2 x2 v2) k2) ⊨ Q) ->
    HYCO [R] (m1, INPUT x1, k1) | (m2, INPUT x2, k2) ⊨ Q.
Proof.
  intros.
  apply hyco_step.
  intros e1 s1' (v1 & -> & ->)%steps_seq_input_inv.
  specialize (H v1) as (v2 & (H1 & H2)).
  eexists (EINPUT x2 v2), _.
  split; [ | split ]; eauto.
  repeat econstructor.
Qed.

Lemma hyco_output_output:
  forall R m1 e1 k1 m2 e2 k2 Q,
    Q (EOUTPUT (aeval m1 e1)) (EOUTPUT (aeval m2 e2)) ->
    UHYCO [R] (resume m1 k1) | (resume m2 k2) ⊨ Q ->
    HYCO [R] (m1, OUTPUT e1, k1) | (m2, OUTPUT e2, k2) ⊨ Q.
Proof.
  intros.
  apply hyco_step.
  intros e_1 s1' (-> & ->)%steps_seq_output_inv.
  eexists (EOUTPUT (aeval m2 e2)), _.
  split; [ | split ]; eauto.
  repeat econstructor.
Qed.

(** ** Handling Nondeterminism *)

Lemma hyco_havoc_r:
  forall v R s1 m x k Q,
    HYCO [R] s1 | (resume (update m x v) k) ⊨ Q ->
    HYCO [R] s1 | (m, HAVOC x, k) ⊨ Q.
Proof.
  intros.
  eapply hyco_steps_r; eauto.
  eapply rt_step; eauto.
  constructor.
Qed.

Lemma hyco_havoc_l:
  forall R m1 x1 k1 s2 Q,
    (forall v1, HYCO [R] (resume (update m1 x1 v1) k1) | s2 ⊨ Q) ->
    HYCO [R] (m1, HAVOC x1, k1) | s2 ⊨ Q.
Proof.
  intros.
  apply hyco_step.
  intros * (z & Hsteps & Hstep).
  inversion Hsteps; subst; try easy.
  inversion H0; subst; try easy.
  specialize (H v).
  apply Glock_unfold in H; auto.
  inversion H; subst.
  edestruct H2 as (e2 & s2' & H').
  econstructor. split; eauto.
  eexists _, _; eauto.
Qed.

Lemma hyco_havoc_havoc:
  forall R m1 x1 k1 m2 x2 k2 Q,
    (forall v1, exists v2, HYCO [R] (resume (update m1 x1 v1) k1) | (resume (update m2 x2 v2) k2) ⊨ Q) ->
    HYCO [R] (m1, HAVOC x1, k1) | (m2, HAVOC x2, k2) ⊨ Q.
Proof.
  intros.
  apply hyco_havoc_l.
  intros v1. specialize (H v1) as (v2 & H).
  now apply (hyco_havoc_r v2).
Qed.

(** ** Tactics to ease the use of Hyco *)

(** Execute both programs untill they reach an event-producing instructions *)
Ltac hyco_sync_ :=
  match goal with
  | [ |- UHYCO [_] _ | _ ⊨ _ ] =>
    apply uhyco_hyco; hyco_sync_
  | [ |- HYCO [_] (_, SEQ _ _, _) | (_, _, _) ⊨ _ ] =>
    apply hyco_exec_l; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, LOOP _, _) | (_, _, _) ⊨ _ ] =>
    apply hyco_exec_l; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, SKIP, _) | (_, _, _) ⊨ _ ] =>
    apply hyco_exec_l; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, _, _) | (_, SKIP, _) ⊨ _ ] =>
    apply hyco_exec_r; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, _, _) | (_, SEQ _ _, _) ⊨ _ ] =>
    apply hyco_exec_r; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, _, _) | (_, LOOP _, _) ⊨ _ ] =>
    apply hyco_exec_r; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, _, _) | (_, SKIP, _) ⊨ _ ] =>
    apply hyco_exec_r; simpl exec_det_step; try hyco_sync_
  | [ |- HYCO [_] (_, ?p1, _) | (_, ?p2, _) ⊨ _ ] =>
    unfold p1; unfold p2; try hyco_sync_
  end.

Ltac hyco_sync :=
  timeout 2 hyco_sync_.

(** Synchronized event-producing steps *)
Ltac hyco_step :=
  match goal with
  | [ |- HYCO [_] (_, INPUT _, _) | (_, INPUT _, _) ⊨ _ ] =>
    apply hyco_input_input; simpl resume
  | [ |- HYCO [_] (_, OUTPUT _, _) | (_, OUTPUT _, _) ⊨ _ ] =>
    apply hyco_output_output; simpl resume
  end.

(** Conclude a proof by creating a cycle *)
Ltac hyco_cycle :=
  match goal with
  | [ |- UHYCO [_] _ | _ ⊨ _ ] => gbase; try easy
  end.

Ltac hycofix invariant CH CH_fact :=
  gcofix CH_fact with CH;
  fold (Glock (hycoF step invariant) CH);
  fold (hyco step invariant).

Ltac hycofix' invariant CH CH_fact :=
  gcofix CH_fact;
  fold (Glock (hycoF step invariant) CH);
  fold (hyco step invariant).

Ltac hyco_init :=
  match goal with
  | [ |- forall m1 m2, HYCO [bot2] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix P ltac:(fresh "CH0") ltac:(fresh "defH0")
  | [ |- forall m1 m2, _ -> HYCO [bot2] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix P ltac:(fresh "CH0") ltac:(fresh "defH0")
  | [ |- HYCO [bot2] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix P ltac:(fresh "CH0") ltac:(fresh "defH0")
  | [ |- forall m1 m2, HYCO [?CH] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix' P CH ltac:(fresh "defH0")
  | [ |- forall m1 m2, _ -> HYCO [?CH] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix' P CH ltac:(fresh "defH0")
  | [ |- HYCO [?CH] ?s1 | ?s2 ⊨ ?P ] =>
    hycofix P CH ltac:(fresh "defH0")
  end.

Opaque Z.mul.

Example echo :=
  LOOP (SEQ (INPUT "x") (OUTPUT (VAR "x"))).

Example echo_skip :=
  LOOP (SEQ SKIP (SEQ (INPUT "x") (OUTPUT (VAR "x")))).
  
Example DOUBLE (e1 e2 : event) :=
  forall x, e1 = EOUTPUT x -> e2 = EOUTPUT (2 * x).

Goal
  forall m1 m2, HYCO [bot2] (m1, echo, Kstop) | (m2, echo, Kstop) ⊨ DOUBLE.
Proof.
  hyco_init. intros m1 m2.

  (* synchronize at inputs *)
  hyco_sync.

  (* match inputs *)
  hyco_step.
  intros v1. exists (2 * v1)%Z.
  split; try easy.

  apply uhyco_hyco.
  
  (* match outputs *)
  hyco_step.
  unfold update; simpl.
  now intros ? [=]; subst.

  fold echo.
  hyco_cycle.
Qed.

Definition echo_plus :=
  LOOP (SEQ (INPUT "x") (SEQ (HAVOC "r") (OUTPUT (ADD (VAR "r") (VAR "x"))))).

Goal
  forall m1 m2, HYCO [bot2] (m1, echo, Kstop) | (m2, echo_plus, Kstop) ⊨ DOUBLE.
Proof.
  hyco_init. intros m1 m2.
  hyco_sync.
  hyco_step.
  intros v1. exists (2 * v1)%Z.
  split; try easy.

  hyco_sync.
  apply (hyco_havoc_r 0). simpl.
  hyco_step.
  now intros v2 [=<-].
  fold echo. fold echo_plus.
  hyco_cycle.
Qed.

Definition add_cst c :=
  LOOP (SEQ (ASSIGN "x" (ADD (VAR "x") (CST c))) (OUTPUT (VAR "x"))).

Definition add c :=
  SEQ (ASSIGN "x" (CST 0)) (add_cst c).

Lemma alloc_inv:
  forall INV R m1 p1 k1 m2 p2 k2 Q,
    INV m1 m2 ->
    (forall m1 m2, INV m1 m2 -> HYCO [R] (m1, p1, k1) | (m2, p2, k2) ⊨ Q) ->
    HYCO [R] (m1, p1, k1) | (m2, p2, k2) ⊨ Q.
Proof.
  intros * HINV H.
  now apply H.
Qed.

Tactic Notation "hyco_left" integer(n) :=
  match goal with
  | [ |- HYCO [_] _ | _ ⊨ _ ] =>
    do n apply hyco_exec_l; simpl
  end.

Tactic Notation "hyco_right" integer(n) :=
  match goal with
  | [ |- HYCO [_] _ | _ ⊨ _ ] =>
    do n apply hyco_exec_r; simpl
  end.

Tactic Notation "hyco_left" := hyco_left 1.
Tactic Notation "hyco_right" := hyco_right 1.

Ltac hyco_invariant INV :=
  match goal with
  | [ |- HYCO [_] (?m1, _, _) | (?m2, _, _) ⊨ _ ] =>
    apply (alloc_inv INV); [ | hyco_init ]
  end.

Goal
  forall m1 m2, HYCO [bot2] (m1, add 1, Kstop) | (m2, add 2, Kstop) ⊨ DOUBLE.
Proof.
  (* start proof *)
  hyco_init. intros m1 m2.

  (* take two steps to initialize the memories left and right *)
  hyco_left 2.
  hyco_right 2.

  (* allocate the invariant [2 * x_1 = x_2] *)
  hyco_invariant (fun m1 m2 => 2 * m1 "x" = m2 "x")%string%Z.
  now unfold update. clear m1 m2.
  intros m1 m2 HINV. unfold add_cst.

  (* synchronize both programs *)
  hyco_sync.
  hyco_left 2.
  hyco_right 2.

  (* match outputs (YOU NEED THE INVARIANT!!!) *)
  hyco_step. cbn.
  intros v1 [=<-]. rewrite <- HINV.
  f_equal. lia.

  (* use the co-induction hypothesis to finish the proof *)
  hyco_cycle.
  apply defH1. cbn.
  rewrite <- HINV. lia.
Qed.