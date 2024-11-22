From Coq Require Import ZArith String Streams.
From hyco Require Import transitions.

(** * A small imperative language with non-determinism and IO *)

(** Arithmetic Expressions *)
Inductive aexpr :=
  | VAR (x : string)
  | CST (c : Z)
  | ADD (e1 e2 : aexpr)
  | MUL (e1 e2 : aexpr).

(** Boolean Expressions *)
Inductive bexpr :=
  | BOOL (b : bool)
  | NOT (e : bexpr)
  | EQ (e1 e2 : aexpr)
  | LT (e1 e2 : aexpr)
  | AND (e1 e2 : bexpr).

(** Programs *)
Inductive prog :=
  | LOOP (p : prog)
  | ITE (b : bexpr) (p1 p2 : prog)
  | FLIP (p1 p2 : prog)
  | SEQ (p1 p2 : prog)
  | SKIP
  | ASSIGN (x : string) (e : aexpr)
  (* havoc is a silent version of input (it is not observable) *)
  | HAVOC (x : string)
  (* input is observed, it appears on the trace *)
  | INPUT  (x : string)
  | OUTPUT (e : aexpr).

Definition memory : Type := string -> Z.

Definition update (mem : memory) (x : string) (vx : Z) : memory :=
  fun y => if (x =? y)%string then vx else mem y.

Fixpoint aeval (mem : memory) (e : aexpr) : Z :=
  match e with
  | VAR x => mem x
  | CST c => c
  | ADD e1 e2 => aeval mem e1 + aeval mem e2
  | MUL e1 e2 => aeval mem e1 * aeval mem e2
  end%Z.

Fixpoint beval (mem : memory) (e : bexpr) : bool :=
  match e with
  | BOOL b => b
  | NOT e => negb (beval mem e)
  | EQ e1 e2 => aeval mem e1 =? aeval mem e1 
  | LT e1 e2 => aeval mem e1 <? aeval mem e1 
  | AND e1 e2 => (beval mem e1 && beval mem e1)%bool
  end%Z.

Inductive event :=
  | EINPUT (x : string) (vx : Z)
  | EOUTPUT (x : Z).

Inductive cont : Type :=
  | Kstop
  | Kseq (p : prog) (k : cont)
  | Kloop (c : prog) (k : cont).

Definition state : Type := memory * prog * cont.

Definition resume (m : memory) (k : cont) : state :=
  match k with
  | Kseq c k => (m, c, k)
  | Kstop => (m, SKIP, Kstop)
  | Kloop c k => (m, LOOP c, k)
  end.

Inductive step : state -> option event -> state -> Prop :=

  | step_flip_left : forall m p1 p2 k,
    step (m, FLIP p1 p2, k) None (m, p1, k)
  
  | step_flip_right : forall m p1 p2 k,
    step (m, FLIP p1 p2, k) None (m, p2, k)

  | step_havoc : forall m x v k,
    step (m, HAVOC x, k) None (resume (update m x v) k)

  | step_input : forall m x v k,
    step (m, INPUT x, k) (Some (EINPUT x v)) (resume (update m x v) k)

  | step_output : forall m e k,
    step (m, OUTPUT e, k) (Some (EOUTPUT (aeval m e))) (resume m k)

  | step_assign : forall m x e k,
    step (m, ASSIGN x e, k) None (resume (update m x (aeval m e)) k)

  | step_seq : forall m c1 c2 k,
    step (m, SEQ c1 c2, k) None (m, c1, Kseq c2 k)

  | step_ite : forall m b c1 c2 k,
    step (m, ITE b c1 c2, k) None (m, (if beval m b then c1 else c2), k)

  | step_loop : forall m c k,
    step (m, LOOP c, k) None (m, c, Kloop c k)

  | step_skip_seq: forall m c k,
    step (m, SKIP, Kseq c k) None (m, c, k)

  | step_skip_loop: forall m c k,
    step (m, SKIP, Kloop c k) None (m, LOOP c, k).

Definition exec_det_step_aux (m : memory) (p : prog) (k : cont) :=
  match p with
  | ASSIGN x e => resume (update m x (aeval m e)) k
  | LOOP p => (m, p, Kloop p k)
  | SEQ  p1 p2 => (m, p1, Kseq p2 k)
  | SKIP =>
    match k with
    | Kseq c k => (m, c, k)
    | Kloop c k => (m, LOOP c, k)
    | k => (m, SKIP, k)
    end
  | _ => (m, p, k)
  end.

Definition exec_det_step '((m, p, k) : state) := exec_det_step_aux m p k.

Hint Constructors step : core.

Lemma exec_det_step_sound:
  forall s, det_steps step s (exec_det_step s).
Proof.
  intros [[m p] k]. destruct p; simpl.
  all: try apply rt_refl.
  - eapply rt_step; eauto.
    repeat econstructor. now inversion 1.
  - eapply rt_step; eauto.
    repeat econstructor. now inversion 1.
  - destruct k. all: try apply rt_refl.
    + eapply rt_step; eauto.
      repeat econstructor. now inversion 1.
    + eapply rt_step; eauto.
      repeat econstructor. now inversion 1.
  - eapply rt_step; eauto.
    repeat econstructor. now inversion 1.
Qed.

Lemma action_determinism:
  action_determinist step.
Proof.
  intros s1 s2 e2 s3 Hstep1 Hstep2.
  remember None as e1 eqn:Heq.
  induction Hstep1; auto.
  all: now inversion Hstep2.
Qed.

Lemma steps_seq_input_inv:
  forall m x k e s,
    steps step (m, INPUT x, k) e s ->
    exists v, e = EINPUT x v /\ s = resume (update m x v) k.
Proof.
  intros * (z & Hsteps & Hio).
  remember (m, (INPUT x), k) as s1 eqn:Heq.
  generalize m x k Heq. clear m x k Heq.
  induction Hsteps.
  - intros * ->. inversion Hio; subst.
    repeat econstructor.
  - intros * ->. inversion H; subst.
Qed.

Lemma steps_seq_output_inv:
  forall m k a e s,
    steps step (m, OUTPUT a, k) e s ->
    e = EOUTPUT (aeval m a) /\ s = resume m k.
Proof.
  intros * (z & Hsteps & Hio).
  remember (m, (OUTPUT a), k) as s1 eqn:Heq.
  generalize m a k Heq. clear m a k Heq.
  induction Hsteps.
  - intros * ->. inversion Hio; subst.
    inversion Hio; subst.
    repeat econstructor.
  - intros * ->. inversion H; subst.
Qed.