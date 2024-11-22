From Coq Require Import Logic.ClassicalChoice List Streams Lia.
From Coq Require Import String ZArith Classes.RelationClasses.
From hyco Require Import transitions.
From Paco Require Import paco.
Import ListNotations.

(** * Facts about (LTL defined) trace relations *)

Section Tracerel.

Context {state event : Type} (step : state -> option event -> state -> Prop).

Definition trace : Type := Stream event.
Definition spec := trace -> trace -> Prop.

(** ** Safety Relations *)

Fixpoint extend {A} (l : list A) (s : Stream A) : Stream A :=
  match l with
  | [] => s
  | x::xs => Cons x (extend xs s)
  end.

Definition is_prefix {A} (pr : list A) (s : Stream A) : Prop :=
  exists s', s = extend pr s'.

Inductive prefix2 {A} : list A -> list A -> Stream A -> Stream A -> Prop :=
  | prefix2_nil s1 s2 : prefix2 nil nil s1 s2
  | prefix2_cons x1 pr1 s1 x2 pr2 s2 : 
    prefix2 pr1 pr2 s1 s2 -> prefix2 (x1::pr1) (x2::pr2) (Cons x1 s1) (Cons x2 s2).

Definition classic_safety_closure (phi : spec) (t1 t2 : trace) : Prop :=
  forall pr1 pr2, prefix2 pr1 pr2 t1 t2 -> exists t1' t2', phi (extend pr1 t1') (extend pr2 t2').

(** Classical definition of safety via trace prefixes *)
Definition classic_safety phi :=
  classic_safety_closure phi <2= phi.

(** ** Safety via derivatives *)

(** Derivation operator *)
Definition deriv (e1 e2 : event) (phi : spec) : spec :=
  fun t1 t2 => phi (Cons e1 t1) (Cons e2 t2).

Lemma deriv_mon:
  forall (e1 e2 : event) phi1 phi2,
    phi1 <2= phi2 ->
    deriv e1 e2 phi1 <2= deriv e1 e2 phi2.
Proof.
  intros e1 e2 phi1 phi2 H1 t1 t2 H2.
  now apply H1.
Qed.
Hint Resolve deriv_mon : paco core.

Definition non_empty (phi : spec) :=
  exists t1 t2, phi t1 t2.

Lemma non_empty_mon:
  forall (phi1 phi2 : spec),
    phi1 <2= phi2 ->
    non_empty phi1 -> non_empty phi2.
Proof.
  intros * H1 (t1 & t2 & H2).
  exists t1, t2. now apply H1.
Qed.
Hint Resolve non_empty_mon : paco core.


Inductive safety_closureF (clo : spec -> trace -> trace -> Prop) : spec -> trace -> trace -> Prop :=
  | safety_intro phi e1 t1 e2 t2 :
    non_empty (deriv e1 e2 phi) ->
    clo (deriv e1 e2 phi) t1 t2 ->
    safety_closureF clo phi (Cons e1 t1) (Cons e2 t2).
Hint Constructors safety_closureF : paco core.

Lemma safety_closureF_mon :
  monotone3 safety_closureF.
Proof.
  pmonauto.
Qed.
Hint Resolve safety_closureF_mon : paco core.

(** Coinductive characterization of the safety closure *)
Definition safety_closure (phi : spec) : spec :=
  paco3 safety_closureF bot3 phi.

Lemma safety_closure_mon:
  monotone2 safety_closure.
Proof.
  pcofix CH with REC.
  intros [e1 t1] [e2 t2] phi1 phi2 H1 H2.
  pinversion H1; subst. clear H1.
  pstep. constructor; eauto.
Qed.

Lemma deriv_step:
  forall t1 t2 phi, phi t1 t2 <-> deriv (hd t1) (hd t2) phi (tl t1) (tl t2).
Proof.
  now intros [e1 t1] [e2 t2] R; simpl in *.
Qed.

(** Every trace property is included in its safety closure *)
Lemma safety_closure_weaker:
  forall phi, phi <2= safety_closure phi.
Proof.
  pcofix CH.
  intros phi [e1 t1] [e2 t2] H. pstep.
  constructor.
  - eexists _, _. apply H.
  - right. eapply CH, H.
Qed.

(** Safety properties are these that are equivalent to their safety closure! *)
Definition safety (phi : spec) :=
  safety_closure phi <2= phi.

Lemma safety_deriv:
  forall e1 e2 phi, safety phi -> safety (deriv e1 e2 phi).
Proof.
  intros * H1 t1 t2 H2. apply H1.
  pinversion H2; subst.
  pstep. constructor; eauto.
  destruct H as (t1 & t2 & H).
  eexists _, _. apply H.
Qed.
Hint Resolve safety_deriv : core.

Lemma helper_1:
  forall phi e1 t1 e2 t2,
    safety_closure phi (Cons e1 t1) (Cons e2 t2) ->
    safety_closure (deriv e1 e2 phi) t1 t2.
Proof.
  intros. now pinversion H; subst.
Qed.

Lemma helper_1':
  forall phi e1 t1 e2 t2,
    safety_closure (deriv e1 e2 phi) t1 t2 ->
    safety_closure phi (Cons e1 t1) (Cons e2 t2).
Proof.
  pcofix CH with REC.
  intros * H.
  pinversion H; subst. clear H.
  destruct H0 as (t1 & t2 & H).
  do 2 red in H.
  pstep. constructor.
  - eexists _, _. apply H.
  - right. now apply CH.
Qed.

Definition deriv_pre pr1 pr2 (phi : trace -> trace -> Prop) :=
  fun (t1 t2 : trace) => phi (extend pr1 t1) (extend pr2 t2).

Fixpoint chop (n : nat) (t : trace) :=
  match n with
  | 0 => t
  | S n =>
    match t with
    | Cons _ t => chop n t
    end
  end.

Lemma helper_2:
  forall phi pr1 t1 pr2 t2,
    prefix2 pr1 pr2 t1 t2 ->
    safety_closure phi t1 t2 ->
    safety_closure (deriv_pre pr1 pr2 phi) (chop (List.length pr1) t1) (chop (List.length pr2) t2).
Proof.
  intros * H1 H2.
  induction H1 in phi, H2 |-*; auto.
  apply helper_1 in H2.
  apply IHprefix2 in H2.
  simpl. eapply paco3_mon_gen; eauto.
Qed.

(** The classical prefix-based notion of safety closure is equivalent to the coinductive one *)
Lemma equivalence_of_safety_closures:
  forall phi,
    classic_safety_closure phi <2= safety_closure phi /\
    safety_closure phi <2= classic_safety_closure phi.
Proof.
  intros phi. split.
  - revert phi. pcofix CH with REC. intros phi [e1 t1] [e2 t2] H.
    pstep. constructor.
    + specialize (H [e1] [e2] ltac:(repeat econstructor)) as (t1' & t2' & H).
      repeat econstructor; eauto.
    + right. apply CH. intros pr1 pr2 Hpre.
      specialize (H (e1::pr1) (e2::pr2) ltac:(repeat econstructor; eauto)) as (t1' & t2' & H).
      repeat econstructor; eauto.
  - intros t1 t2 Hclo pr1 pr2 Hpre.
    pose proof (helper_2 phi _ _ _ _ Hpre Hclo) as H.
    induction Hpre in phi, H |-*; simpl in *.
    + pinversion H; subst.
      destruct H0 as (t1'' & t2'' & H0).
      eexists _, _. apply H0.
    + destruct (IHHpre (deriv x1 x2 phi)) as (t1' & t2' & H').
      eapply paco3_mon_gen; eauto.
      eexists _, _. apply H'.
Qed.

(** The classical prefix-based notion of safety relation is equivalent to the coinductive one *)
Lemma equivalence_of_safety:
  forall phi,
    safety phi <-> classic_safety phi.
Proof.
  intros phi. split.
  - intros H t1 t2 Hclo%equivalence_of_safety_closures.
    now apply H.
  - intros H t1 t2 Hclo%equivalence_of_safety_closures.
    now apply H.
Qed.

(** ** Temporal Operators *)

Inductive alwaysF (R : event -> event -> Prop) (sem_always : trace -> trace -> Prop) : trace -> trace -> Prop :=
  | always_intro e1 t1 e2 t2: R e1 e2 -> sem_always t1 t2 -> alwaysF R sem_always (Cons e1 t1) (Cons e2 t2).
Hint Constructors alwaysF : core paco.

Lemma alwaysF_mon:
  forall R, monotone2 (alwaysF R).
Proof.
  pmonauto.
Qed.
Hint Resolve alwaysF_mon : paco core.

Definition always (R : event -> event -> Prop) :=
  paco2 (alwaysF R) bot2.

Inductive globallyF (R : trace -> trace -> Prop) (globally : trace -> trace -> Prop) : trace -> trace -> Prop :=
  | globally_intro t1 t2 : R t1 t2 -> globally (tl t1) (tl t2) -> globallyF R globally t1 t2.
Hint Constructors globallyF : core paco.

Lemma globallyF_mon:
  forall R, monotone2 (globallyF R).
Proof.
  pmonauto.
Qed.
Hint Resolve globallyF_mon : paco core.

Lemma globallyF_mon_gen:
  forall phi1 phi2 R1 R2, phi1 <2= phi2 -> R1 <2= R2 -> globallyF phi1 R1 <2= globallyF phi2 R2.
Proof.
  intros. simpl in *.
  inversion PR; subst.
  constructor; eauto.
Qed.
Hint Resolve globallyF_mon_gen : paco core.

Definition globally (R : trace -> trace -> Prop) :=
  paco2 (globallyF R) bot2.

Lemma globally_mon:
  monotone2 globally.
Proof.
  intros t1 t2 R1 R2 H1 H2.
  eapply paco2_mon_gen; eauto.
Qed.

Inductive wuntilF (R1 R2 : trace -> trace -> Prop) (wuntil : trace -> trace -> Prop) : trace -> trace -> Prop :=
  | wuntil_r t1 t2 : R2 t1 t2 -> wuntilF R1 R2 wuntil t1 t2
  | wuntil_l t1 t2 : R1 t1 t2 -> wuntil (tl t1) (tl t2) -> wuntilF R1 R2 wuntil t1 t2.
Hint Constructors wuntilF : core paco.

Lemma wuntilF_mon:
forall R1 R2, monotone2 (wuntilF R1 R2).
Proof.
  pmonauto.
Qed.
Hint Resolve wuntilF_mon : paco core.

Definition wuntil (R1 R2 : trace -> trace -> Prop) :=
  paco2 (wuntilF R1 R2) bot2.

Definition impl (phi1 phi2 : trace -> trace -> Prop) : trace -> trace -> Prop :=
  fun t1 t2 => phi1 t1 t2 -> phi2 t1 t2.

Definition pure (phi : Prop) : trace -> trace -> Prop :=
  fun _ _ => phi.

Definition now (phi : event -> event -> Prop) : trace -> trace -> Prop :=
  fun t1 t2 => phi (hd t1) (hd t2).

Definition next (phi : trace -> trace -> Prop) : trace -> trace -> Prop :=
  fun '(Cons e1 t1) '(Cons e2 t2) => phi t1 t2.

(** ** Proof of safety of some temporal operators *)

Lemma and_safe:
  forall phi1 phi2, safety phi1 -> safety phi2 -> safety (phi1 /2\ phi2).
Proof.
  intros phi1 phi2 H1 H2.
  intros t1 t2 H.
  split.
  - apply H1.
    eapply safety_closure_mon; eauto.
    simpl. intuition.
  - apply H2.
    eapply safety_closure_mon; eauto.
    simpl. intuition.
Qed.

Lemma always_safe:
  forall phi, safety (always phi).
Proof.
  intros phi. pcofix CH with REC.
  intros [e1 t1] [e2 t2] H. pstep.
  pinversion H; subst.
  destruct H4 as (t1' & t2' & H').
  pinversion H'; subst.
  econstructor; eauto.
  right. apply CH.
  eapply safety_closure_mon; eauto.
  clear - H3. intros t1 t2 H.
  pinversion H; auto.
Qed.

Lemma globally_now:
  forall phi, globally phi <2= phi.
Proof.
  intros phi t1 t2 H; simpl in *.
  now pinversion H; subst.
Qed.

Lemma globally_safe:
  forall phi, safety phi -> safety (globally phi).
Proof.
  intros phi. pcofix CH with REC.
  intros Hsafe t1 t2 H. pstep.
  econstructor.
  - apply Hsafe.
    eapply safety_closure_mon; eauto.
    clear. intros t1 t2 H.
    now pinversion H.
  - right. apply CH; auto.
    pinversion H; subst.
    eapply safety_closure_mon; eauto.
    clear. intros t1 t2 H. red in H.
    pinversion H; subst. simpl in *.
    eapply globally_mon; eauto.
Qed.

Lemma safety_closure_wuntil_inv:
  forall phi1 phi2 e1 t1 e2 t2,
    safety_closure (wuntil (now phi1) (now phi2)) (Cons e1 t1) (Cons e2 t2)
    ->
    (phi2 e1 e2 \/ phi1 e1 e2 /\ safety_closure (wuntil (now phi1) (now phi2)) t1 t2).
Proof.
  intros * Hclo.
  destruct (classic (phi2 e1 e2)) as [H | H].
  - now left.
  - right. pinversion Hclo; subst.
    destruct H4 as (t1' & t2' & H').
    pinversion H'; subst; try easy.
    split; auto.
    clear - H H6.
    eapply safety_closure_mon; eauto.
    clear - H. intros t1 t2 H'.
    pinversion H'; subst; try easy.
Qed.

Lemma wuntil_safe:
  forall phi1 phi2, safety (wuntil (now phi1) (now phi2)).
Proof.
  intros *. pcofix CH with REC.
  intros [e1 t1] [e2 t2] [Hclo | [H Hclo]]%safety_closure_wuntil_inv.
  - pstep. now left.
  - pstep. right; auto.
Qed.

Lemma pure_impl_safe:
  forall phi1 phi2, safety phi2 -> safety (impl (pure phi1) phi2).
Proof.
  intros phi1 phi2 Hsafe.
  intros [e1 t1] [e2 t2] Hclo H.
  apply Hsafe. clear Hsafe.
  pinversion Hclo; subst. clear Hclo.
  destruct H4 as (? & ? & H4).
  pstep. constructor.
  eexists _, _. apply (H4 H).
  left. eapply safety_closure_mon; eauto.
  clear - H. intros t1' t2' H'.
  apply (H' H).
Qed.

Lemma now_impl_safe:
  forall phi1 phi2, safety phi2 -> safety (impl (now phi1) phi2).
Proof.
  intros phi1 phi2 Hsafe.
  intros [e1 t1] [e2 t2] Hclo H.
  apply Hsafe. clear Hsafe.
  pinversion Hclo; subst. clear Hclo.
  destruct H4 as (? & ? & H4).
  pstep. constructor.
  eexists _, _. apply (H4 H).
  left. eapply safety_closure_mon; eauto.
  clear - H. intros t1' t2' H'.
  apply (H' H).
Qed.

(** ** Unfoldings and derivation rules *)

Lemma wuntil_unfold:
  forall (phi1 phi2 : trace -> trace -> Prop),
    phi2 \2/ (phi1 /2\ next (wuntil phi1 phi2)) <2= wuntil phi1 phi2.
Proof.
  intros phi1 phi2 [e1 t1] [e2 t2] [H | [H1 H2]]; simpl in *.
  - pstep. left; eauto.
  - pstep. right; eauto.
Qed.

Lemma globally_unfold:
  forall (phi : trace -> trace -> Prop),
    phi /2\ next (globally phi) <2= globally phi.
Proof.
  intros phi [e1 t1] [e2 t2] [H1 H2]; simpl in *.
  pstep. constructor; auto.
Qed.

Lemma always_unfold:
  forall (phi : event -> event -> Prop),
    now phi /2\ next (always phi) <2= always phi.
Proof.
  intros phi [e1 t1] [e2 t2] [H1 H2]; simpl in *.
  pstep. constructor; auto.
Qed.

Lemma deriv_next:
  forall e1 e2 phi,
    phi <2= deriv e1 e2 (next phi).
Proof.
  eauto.
Qed.

Lemma deriv_and:
  forall e1 e2 phi1 phi2,
    deriv e1 e2 phi1 /2\ deriv e1 e2 phi2 <2= deriv e1 e2 (phi1 /2\ phi2).
Proof.
  eauto.
Qed.

Lemma deriv_or:
  forall e1 e2 phi1 phi2,
    deriv e1 e2 phi1 \2/ deriv e1 e2 phi2 <2= deriv e1 e2 (phi1 \2/ phi2).
Proof.
  eauto.
Qed.

Lemma deriv_or_left:
  forall e1 e2 phi1 phi2,
    deriv e1 e2 phi1 <2= deriv e1 e2 (phi1 \2/ phi2).
Proof.
  eauto.
Qed.

Lemma deriv_or_right:
  forall e1 e2 phi1 phi2,
    deriv e1 e2 phi2 <2= deriv e1 e2 (phi1 \2/ phi2).
Proof.
  eauto.
Qed.

Lemma deriv_globally:
  forall e1 e2 phi,
    deriv e1 e2 phi /2\ globally phi <2= deriv e1 e2 (globally phi).
Proof.
  intros * [H1 H2]; simpl in *.
  apply globally_unfold; eauto.
Qed.

Lemma deriv_always:
  forall e1 e2 phi,
    pure (phi e1 e2) /2\ always phi <2= deriv e1 e2 (always phi).
Proof.
  intros * [H1 H2]; simpl in *.
  apply always_unfold; eauto.
Qed.

Lemma deriv_wuntil:
  forall e1 e2 phi1 phi2,
    deriv e1 e2 phi2 \2/ (deriv e1 e2 phi1 /2\ wuntil phi1 phi2) <2= deriv e1 e2 (wuntil phi1 phi2).
Proof.
  intros * H. simpl in *.
  apply wuntil_unfold; eauto.
Qed.

Definition forall_exists (s1 s2 : state) (phi : trace -> trace -> Prop) :=
  forall r1, is_run step s1 r1 -> exists t2, is_trace step s2 t2 /\ phi (map snd r1) t2.

End Tracerel.

Hint Constructors alwaysF : core paco.
Hint Resolve alwaysF_mon : core paco.
Hint Resolve wuntilF_mon : core paco.
Hint Resolve safety_closureF_mon : paco core.
Hint Resolve safety_deriv : core.
Hint Resolve deriv_mon : paco core.
Hint Resolve non_empty_mon : paco core.