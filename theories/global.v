From Coq Require Import Arith Bool List Lia.
From Giskard Require Import lib structures local.

Import ListNotations.

Set Implicit Arguments.
 
(** * Global state operations, transitions and properties *)

(** Global state transitions are responsible for modeling network responsibilities:
message broadcasting and timekeeping. Global states can be viewed as a snapshot of
all local states, paired with a global message buffer which records all messages sent
by all participating nodes up to that point in the protocol's execution. *)

(** ** Global state definitions *)

(** A global state is defined as a pair containing:
- a mapping from node identifier to its local state, and
- a list of messages containing all broadcasted messages thus far.

It is equipped with a property that the mapping works as intended. *)
Definition GState : Type := (node -> NState) * list message.

(** The initial global state is defined as the collection of initial local
states, paired with an empty message buffer. *)
Definition GState_init : GState :=
  (fun (n : node) => NState_init n, []).

(** ** Global state transitions *)

(** In order to define protocol-following global state transitions,
we first define an operation which does two things:
- broadcasts outgoing messages from the transitioning node to the remaining nodes, and
- records outgoing messages in the global message buffer.

We adopt the convention that nodes do not send messages to themselves.
This design choice is orthogonal to safety proofs because we do not
reason about the number of participants required to reach a quorum. *)
Definition broadcast_messages (g : GState) (s1 s2 : NState) (lm : list message) : GState :=
  (fun (n : node) => if node_eqb n (node_id s1)
                  then s2 
                  else
                    (if is_member n participants
                     then add_plural (fst g n) lm
                     else (fst g n)),
                  lm ++ (snd g)). 

(** Protocol-following global state transitions are defined as a binary relation
on pre-state and post-state, in which one participating node makes a protocol-following
local state transition, and the network broadcasts and records its outgoing messages
to the other participating nodes. *)
Inductive GState_step : GState -> GState -> Prop :=
| GState_step_process :
   forall (n : node) (process : NState_transition_type)
     (msg : message) (lm : list message) (g g' : GState),
      In n participants ->
      get_transition process (fst g n) msg (fst g' n) lm ->
      g' = broadcast_messages g (fst g n) (fst g' n) lm ->
      GState_step g g'
| GState_step_timeout :
    forall (g g' : GState),
      g' = ((fun n => if is_member n participants
        then flip_timeout (fst g n) else fst g n), snd g) ->
      GState_step g g'.

(** More convenient representation of the global transition relation for reasoning. *)
Definition GState_transition (g g' : GState) : Prop :=
  (exists (n : node),
      In n participants /\ 
      exists (process : NState_transition_type)
        (msg : message)
        (lm : list message),
        (get_transition process) (fst g n) msg (fst g' n) lm /\
        g' = broadcast_messages g (fst g n) (fst g' n) lm) \/
  g' = ((fun n => if is_member n participants
              then flip_timeout (fst g n)
              else fst g n), snd g).

(** The two global transition relation definitions are equivalent. *)
Lemma GState_step_transition :
 forall g g', GState_step g g' <-> GState_transition g g'.
Proof.
intros; split.
- intro Htr.
  inversion Htr; subst.
  * left.
    exists n; split; [assumption|].
    exists process, msg, lm.
    split; assumption.
  * right; reflexivity.
- intro Htr.
  inversion Htr.
  * destruct H; destruct H; destruct H0.
    destruct H0; destruct H0; destruct H0.
    eapply GState_step_process; eauto.
  * apply GState_step_timeout.
    assumption.
Qed.

Definition GState_sane (g : GState) : Prop := forall n, node_id ((fst g) n) = n.

Lemma GState_init_sane : GState_sane GState_init.
Proof. intro. reflexivity. Qed.

Lemma GState_sane_transition : forall g, GState_sane g -> forall g', GState_transition g g' -> GState_sane g'.
Proof.
intros.
inversion H0; clear H0.
- intro n.
  destruct H1 as [n' [Hin [process [msg [lm [Hpr Hg']]]]]].
  rewrite Hg'; clear Hg'.
  simpl.
  case_eq (node_eqb n (node_id (fst g n'))).
  * rewrite node_eqb_correct; intro Heq.
    rewrite Heq.
    unfold get_transition in Hpr.
    unfold
      propose_block_init,
      discard_view_invalid,
      process_PrepareBlock_duplicate,
      process_PrepareVote_vote,
      process_PrepareVote_wait,
      process_PrepareQC_last_block_new_proposer,
      process_PrepareQC_last_block,
      process_PrepareQC_non_last_block,
      process_ViewChange_quorum_new_proposer,
      process_ViewChange_pre_quorum,
      process_ViewChangeQC_single,
      process_PrepareBlock_malicious_vote,
      process_PrepareBlock_pending_vote in Hpr.
      destruct process; decompose record Hpr; rewrite H0; simpl; reflexivity.
  * case (node_eq_dec n (node_id (fst g n'))); [intro Heq;apply node_eqb_correct in Heq; congruence|].
    intro Hneq.
    case (node_eq_dec n n'); [intro Heq; rewrite Heq in Hneq; rewrite H in Hneq; congruence|].
    intros Hneq' Hnq.
    case_eq (is_member n participants); intro; simpl; rewrite H; reflexivity.
- rewrite H1; clear H1.
  intro n; simpl.
  case_eq (is_member n participants); intro; simpl; rewrite H; reflexivity.
Qed.

(** A trace is a mapping from the natural numbers to global states. *) 
Definition GTrace : Type := nat -> GState.

(** ** Protocol state definitions *)

(** A protocol-following trace is one that starts at the initial state and makes
only protocol-following global state transitions from step i to step (i+1), for all i. *)
Definition protocol_trace (t : GTrace) : Prop :=
  t 0 = GState_init /\ forall n, GState_transition (t n) (t (S n)).

(** In turn, a valid Giskard protocol state is one that exists at the index of a protocol-following trace. *) 
Definition protocol_state (g : GState) (t : GTrace) : Prop :=
  exists n, protocol_trace t /\ (t n) = g.

(** ** Facts about protocol states and traces *)

Lemma protocol_trace_zero :
  forall tr, protocol_trace tr -> tr 0 = GState_init.
Proof.
  intros tr H_prot.
  destruct H_prot as [H_init H_prot].
  assumption.
Qed.

Lemma GState_init_protocol_state :
  forall (tr : GTrace),
    protocol_trace tr ->
    protocol_state GState_init tr. 
Proof. 
  exists 0. split. assumption.
  destruct H; easy. 
Qed.

Lemma protocol_trace_state_sane :
  forall tr, protocol_trace tr ->
  forall n, GState_sane (tr n).
Proof.
intros tr Htr n.
destruct Htr as [Hinit Htr].
revert n Htr.
induction n.
- intros.
  rewrite Hinit.
  apply GState_init_sane.
- intros.
  specialize (IHn Htr).
  specialize (Htr n).
  revert Htr.
  apply GState_sane_transition.
  assumption.
Qed.

Lemma view_state_morphism_inductive_step :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n : node),
      In n participants ->
      node_view (fst (tr i) n) = node_view (fst (tr (S i)) n) \/
      S (node_view (fst (tr i) n)) = node_view (fst (tr (S i)) n).
Proof.
  intros tr Htr i n H_part.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  spec H_prot i.
  destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  - (* In the normal transition case *)
    destruct (node_eq_dec n0 n) as [H_old | H_new].
    + subst.
      destruct p0;
        destruct H_step as [H_update _];
        rewrite H_update; simpl; tauto.
    + left; rewrite H_deliver; simpl.
      rewrite (protocol_trace_state_sane Htr').
      rewrite node_eqb_comm. 
      apply node_eqb_no in H_new.
      rewrite H_new.
      apply is_member_correct in H_part.
      rewrite H_part.
      reflexivity.
  - (* In the timeout case *)
    left; rewrite H_timeout; simpl.
    apply is_member_correct in H_part.
    rewrite H_part.
    reflexivity.
Qed.

Lemma view_state_morphism :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i1 i2 : nat) (n : node),
      In n participants ->
      i1 <= i2 -> 
      node_view (fst (tr i1) n) <= node_view (fst (tr i2) n).
Proof. 
  intros tr H_prot i1 i2 n H_part H_le.
  induction i2 as [|i2 IH_prot].
  - destruct H_prot as [H_init _];
      inversion H_le.
    rewrite H_init. reflexivity.
  - apply le_lt_or_eq in H_le.
    destruct H_le as [H_lt | H_eq].
    + spec IH_prot. lia.
      destruct (view_state_morphism_inductive_step H_prot i2 n H_part) as [H_eq | H_eq_S];
        lia. 
    + clear IH_prot.
      rewrite H_eq.
      reflexivity.
Qed.

Lemma counting_messages_change_tells_receiver :
  forall tr i p0 m msg0 lm0 n msg,
    protocol_trace tr ->
    get_transition p0 (fst (tr i) m) msg0 (fst (tr (S i)) m) lm0 ->
    tr (S i) = broadcast_messages (tr i) (fst (tr i) m) (fst (tr (S i)) m) lm0 ->
    In n participants -> 
    ~ In msg (counting_messages (fst (tr i) n)) ->
    In msg (counting_messages (fst (tr (S i)) n)) ->
    m = n. 
Proof.  
  intros tr i p0 m msg0 lm0 n msg Htr H_step H_deliver H_part H_not_in H_in.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  destruct (node_eq_dec m n) as [H_true | H_false].
  assumption.
  apply node_eqb_no in H_false.
  assert (H_same_counting : counting_messages (fst (tr (S i)) n) = counting_messages (fst (tr i) n)).
  { rewrite H_deliver.
    unfold broadcast_messages.
    assert (is_member n participants = true) by now apply is_member_correct.
    simpl.
    rewrite (protocol_trace_state_sane Htr').
    rewrite node_eqb_comm in H_false. 
    rewrite H_false. rewrite H. simpl.
    reflexivity. }
  rewrite H_same_counting in H_in.
  contradiction.
Qed.

Lemma out_messages_global_monotonic_step :
  forall (tr : GTrace),
    protocol_trace tr -> 
    forall (i: nat),
    forall (n : node) (msg : message),
      In n participants -> 
      In msg (out_messages (fst (tr i) n)) ->
      In msg (out_messages (fst (tr (S i)) n)).
Proof.
  intros tr Htr i n msg H_part H_in1.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  spec H_prot i.
  destruct H_prot as [[n0 [H_in [p [msg0 [lm0 [H_process H_deliver]]]]]] | H_timeout].
  destruct (node_eq_dec n0 n).
  rewrite e in *.
  destruct p; destruct H_process as [H_update _];
    rewrite H_update; simpl;
      try assumption;
      try (try rewrite in_app_iff; repeat right; assumption). 
  rewrite H_deliver. unfold broadcast_messages.
    assert (is_member n participants = true) by now apply is_member_correct. 
    rewrite (protocol_trace_state_sane Htr').
    apply node_eqb_no in n1. rewrite node_eqb_comm in n1. 
    simpl. rewrite n1. rewrite H. simpl.
    assumption.
    rewrite H_timeout.
    assert (is_member n participants = true) by now apply is_member_correct. 
    simpl; rewrite H. easy.
Qed.
  
Lemma out_messages_global_monotonic :
  forall (tr : GTrace),
    protocol_trace tr -> 
    forall (n1 n2 : nat),
      n1 < n2 ->
      forall (n : node) (msg : message),
        In n participants -> 
      In msg (out_messages (fst (tr n1) n)) ->
      In msg (out_messages (fst (tr n2) n)).
Proof.
  intros tr [H_init H_prot] n1 n2 H_lt n msg H_part H_in1.
  generalize dependent n2. induction n2.
  intros. inversion H_lt. intros.
  assert (n1 < n2 \/ n1 = n2) by lia.
  destruct H. spec IHn2 H.
  now apply out_messages_global_monotonic_step.
  subst.
  now apply out_messages_global_monotonic_step.
Qed.

Lemma out_messages_change_means_sent :
  forall (tr : GTrace),
   protocol_trace tr ->
    forall (i : nat) (n0 : node) (p0 : NState_transition_type)
    (msg0 : message) (lm0 : list message),
  In n0 participants ->
  tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 ->
  get_transition p0 (fst (tr i) n0) msg0 (fst (tr (S i)) n0) lm0 ->
  forall n : node,
  In n participants ->
  forall msg : message,
     In msg (out_messages (fst (tr (S i)) n)) -> 
     ~ In msg (out_messages (fst (tr i) n)) ->
     In msg lm0.
Proof.
  intros tr Htr i n0 p0 msg0 lm0 H_part0 H_deliver H_step n H_part msg H_in H_out.  
  destruct (node_eq_dec n0 n) as [H_eq | H_neq].
  - rewrite H_eq in *.
    destruct p0;
      assert (H_step_copy := H_step);
      destruct H_step as [H_update [H_broadcast H_rest]];
      rewrite H_update in H_in;
      rewrite H_broadcast;
      simpl in H_in;
      try rewrite in_app_iff in H_in; 
      repeat destruct H_in as [H_in | H_in];
      try contradiction;
      try assumption; 
      try (rewrite <- H_in; simpl; tauto);
      try (rewrite <- H_in; apply in_eq);
      try (right; assumption).
  - exfalso.
    rewrite H_deliver in H_in.
    simpl in H_in.
    rewrite (protocol_trace_state_sane Htr) in H_in.
    rewrite node_eqb_comm in H_in.
    apply node_eqb_no in H_neq.
    rewrite H_neq in H_in.
    apply is_member_correct in H_part.
    rewrite H_part in H_in. simpl in H_in.
    contradiction.
Qed.

Lemma global_messages_monotonic_step :
  forall tr : GTrace,
    protocol_trace tr ->
    forall (n : nat) (msg : message),
        In msg (snd (tr n)) ->
        In msg (snd (tr (S n))).
Proof.   
  intros tr H_prot n msg H_in.
  destruct H_prot as [H_init H_prot];
  spec H_prot n.
  destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  - (* In the transition case *)
    rewrite H_deliver.
    simpl. apply in_app_iff. now right.
  - (* In the timeout case *)
    rewrite H_timeout.
    simpl. assumption.
Qed.

Lemma global_messages_monotonic :
  forall tr : GTrace,
    protocol_trace tr ->
    forall n1 n2 : nat,
      n1 < n2 ->
      forall (msg : message),
        In msg (snd (tr n1)) ->
        In msg (snd (tr n2)).
Proof. 
  intros tr H_prot n1 n2 H_lt msg H_in.
  induction n2 as [|n2 IH_prot].
  - inversion H_lt.
  - assert (H : n1 < n2 \/ n1 = n2) by lia.
    destruct H as [H_still_lt | H_eq].
    + spec IH_prot H_still_lt.
      now apply global_messages_monotonic_step.
    + subst.
      now apply global_messages_monotonic_step.
Qed.

Lemma not_my_problem :
  forall tr, protocol_trace tr ->
    forall i n n0 lm0,
    In n participants -> 
    n0 <> n -> 
    tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 ->
    counting_messages (fst (tr (S i)) n) = counting_messages (fst (tr i) n). 
Proof.
  intros tr Htr; intros.
  rewrite H1.
  unfold broadcast_messages.
  rewrite (protocol_trace_state_sane Htr).
  apply node_eqb_no in H0.
  rewrite node_eqb_comm in H0.
  simpl. rewrite H0.
  assert (is_member n participants = true) by now apply is_member_correct.
  rewrite H2. simpl. reflexivity.
Qed.

Lemma counting_messages_monotonic :
  forall tr i n msg,
    protocol_trace tr ->
    In n participants -> 
    In msg (counting_messages (fst (tr i) n)) ->
    In msg (counting_messages (fst (tr (S i)) n)). 
Proof.  
  intros tr i n msg Htr H_part H_in.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  spec H_prot i.
  destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  - destruct (node_eq_dec n0 n) as [H_n | H_not_n].
    + rewrite H_n in *.
      destruct p0;
      destruct H_step as [H_update H_rest];
      rewrite H_update;
      simpl; 
      try assumption;
      try (right; assumption);
      try (right; right; assumption);
      try (rewrite H_update in H_view;
           simpl in H_view;
           lia).
    + assert (H_same_counting : counting_messages (fst (tr (S i)) n) =
       counting_messages (fst (tr i) n)) by apply (not_my_problem Htr' i H_part H_not_n H_deliver).
      now rewrite H_same_counting.
  - (* In the timeout case *)
    assert (H_same_counting : counting_messages (fst (tr (S i)) n) = counting_messages (fst (tr i) n)).
    { rewrite H_timeout.
      assert (is_member n participants = true) by now apply is_member_correct.
      simpl. rewrite H. simpl. reflexivity. }
    now rewrite H_same_counting.
Qed.

Lemma counting_message_different_tells_receiver :
  forall tr i n p0 m msg0 lm0,
    protocol_trace tr ->
    In n participants -> 
    counting_messages (fst (tr i) n) <> counting_messages (fst (tr (S i)) n) ->
    get_transition p0 (fst (tr i) m) msg0 (fst (tr (S i)) m) lm0 ->
    tr (S i) = broadcast_messages (tr i) (fst (tr i) m) (fst (tr (S i)) m) lm0 -> 
    m = n. 
Proof.                                       
  intros tr i n p0 m msg0 lm0 Htr H_part H_diff H_step H_deliver.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  destruct (node_eq_dec m n) as [H_true | H_false].
  assumption.
  apply node_eqb_no in H_false.
  assert (H_same_counting : counting_messages (fst (tr (S i)) n) = counting_messages (fst (tr i) n)).
  { rewrite H_deliver.
    unfold broadcast_messages.
    assert (is_member n participants = true) by now apply is_member_correct. simpl.
    rewrite (protocol_trace_state_sane Htr').
    rewrite node_eqb_comm in H_false. 
    rewrite H_false. rewrite H. simpl.
    reflexivity. }
  rewrite H_same_counting in H_diff.
  contradiction.
Qed.

Lemma view_different_tells_receiver :
  forall tr i n p0 m msg0 lm0,
    protocol_trace tr ->
    In n participants -> 
    node_view (fst (tr i) n) <> node_view (fst (tr (S i)) n) -> 
    get_transition p0 (fst (tr i) m) msg0 (fst (tr (S i)) m) lm0 ->
    tr (S i) = broadcast_messages (tr i) (fst (tr i) m) (fst (tr (S i)) m) lm0 -> 
    m = n. 
Proof.
  intros tr i n p0 m msg0 lm0 Htr H_part H_diff H_step H_deliver.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  destruct (node_eq_dec m n) as [H_true | H_false].
  assumption.
  apply node_eqb_no in H_false.
  assert (H_same_view : node_view (fst (tr (S i)) n) = node_view (fst (tr i) n)).
  { rewrite H_deliver.
    unfold broadcast_messages.
    assert (is_member n participants = true) by now apply is_member_correct.
    rewrite (protocol_trace_state_sane Htr').
    rewrite node_eqb_comm in H_false. 
    simpl. rewrite H_false. rewrite H. simpl.
    reflexivity. }
  rewrite H_same_view in H_diff.
  contradiction.
Qed.

Lemma counting_message_change_view_change :
  forall tr i n msg,
    protocol_trace tr ->
    In n participants ->
    In msg (counting_messages (fst (tr i) n)) ->
    ~ In msg (counting_messages (fst (tr (S i)) n)) ->
    node_view (fst (tr (S i)) n) = S (node_view (fst (tr i) n)). 
Proof.
  intros tr i n msg [H_init H_prot] H_part H_in H_not_in.
  assert (H_prot_copy := H_prot). 
  spec H_prot i.
  destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  assert (H_useful := counting_message_different_tells_receiver).
  spec H_useful tr i n p0 n0 msg0 lm0.
  spec H_useful. split; assumption.
  spec H_useful H_part. spec H_useful.
  destruct (list_eq_dec message_eq_dec (counting_messages (fst (tr i) n)) (counting_messages (fst (tr (S i)) n))).
  rewrite e in H_in. contradiction. assumption.
  spec H_useful H_step H_deliver. rewrite <- H_useful in *.
  destruct p0; destruct H_step as [H_update _];
    rewrite H_update; simpl; try reflexivity;
      try (rewrite H_update in H_not_in;
           simpl in H_not_in; try tauto).
  rewrite H_timeout in H_not_in.
  assert (H_member : is_member n participants = true) by now apply is_member_correct. 
  simpl in H_not_in. rewrite H_member in H_not_in.
  simpl in H_not_in. tauto.
Qed.

Lemma processed_means_past_received :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n : node) (msg : message),
      In n participants -> 
      In msg (counting_messages (fst (tr i) n)) ->
      exists (i_past : nat),
        i_past < i /\ 
        In msg (in_messages (fst (tr i_past) n)).
Proof.
  intros tr H_prot i n msg H_part H_in.
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - destruct (In_dec message_eq_dec msg (counting_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot H_old.
      destruct IH_prot as [i_past [H_lt H_goal]].
      exists i_past; split.
      lia. assumption.
    + clear IH_prot.
      assert (H_prot_copy := H_prot);
        destruct H_prot as [H_init H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * assert (H_subst := counting_messages_change_tells_receiver _ _ _ _ _ _ H_prot_copy H_step H_deliver H_part H_new H_in).
      rewrite H_subst in *.
      (* Now that we've established n made the transition *)
      assert (H_step_copy := H_step);
        destruct p0;
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_update in H_in;
        (* For cases that don't process messages *)
        try contradiction;
      (* 9 goals left *)
        try (exists i; split; try lia;
               simpl in H_in;
               destruct H_in as [H_piggyback | H_contra];
               [subst; tauto | contradiction]);
      (* 2 goals left! *)
      try (exists i; split; try lia;
             simpl in H_in;
        destruct H_in as [H_self | [H_piggyback | H_contra]];
        [rewrite H_self in *; tauto | subst; tauto | contradiction]).
      * rewrite H_timeout in H_in.
        simpl in H_in.
        apply is_member_correct in H_part.
        rewrite H_part in H_in.
        simpl in H_in.
        contradiction.
Qed.

Lemma delivered_means_sent_global :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n : node) (msg : message),
      In n participants -> 
      In msg (in_messages (fst (tr i) n)) ->
      In msg (snd (tr i)). 
Proof.
  intros tr H_prot i n msg H_part H_in.
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - destruct (In_dec message_eq_dec msg (in_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot H_old.
      now apply global_messages_monotonic_step.
    + clear IH_prot.
      assert (H_prot_copy := H_prot);
        destruct H_prot as [H_init H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the normal transition case *)
        rewrite H_deliver. 
        simpl.
        destruct (node_eq_dec n n0) as [H_eq | H_neq].
        ** (* If n made the transition *)
          rewrite <- H_eq in *.
          (* There cannot be a message that is added after n consumes a message by
             making a transition, so we find a contradiction between H_in and H_new *)
          destruct p0;
            destruct H_step as [H_update _];
            rewrite H_update in H_in;
            simpl in *;
            try contradiction;
            try (repeat apply remove_subset in H_in; contradiction).
        ** (* If n didn't make the transition *)
          rewrite H_deliver in H_in. 
          simpl in H_in.
          rewrite (protocol_trace_state_sane H_prot_copy) in H_in.
          apply is_member_correct in H_part.
          rewrite H_part in H_in.
          apply node_eqb_no in H_neq.
          rewrite H_neq in H_in.
          simpl in H_in.
          apply in_app_iff in H_in;
            destruct H_in as [H_goal | H_contra].
          apply in_app_iff; tauto.
          contradiction.
      * rewrite H_timeout in H_in.
        simpl in H_in. 
        apply is_member_correct in H_part.
        rewrite H_part in H_in.
        simpl in H_in.
        contradiction.
Qed.

Lemma processed_means_sent_global :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n : node) (msg : message),
      In n participants -> 
      In msg (counting_messages (fst (tr i) n)) ->
      In msg (snd (tr i)).
Proof.   
    intros tr H_prot i n msg H_part H_in.
    assert (H_useful := processed_means_past_received H_prot _ _ _ H_part H_in).
    destruct H_useful as [i_past [H_lt H_goal]].
    assert (H_useful2 := delivered_means_sent_global H_prot _ _ _ H_part H_goal).
    now apply (global_messages_monotonic H_prot H_lt _ H_useful2).
Qed.

Lemma delivered_means_sent_local :
  forall tr, protocol_trace tr ->
   forall i msg (n0 : node) (lm0 : list message),
   In msg lm0 ->
   In n0 participants ->
   forall (p0 : NState_transition_type) (msg0 : message),
   get_transition p0 (fst (tr i) n0) msg0 (fst (tr (S i)) n0) lm0 ->
   tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 ->
   In msg (out_messages (fst (tr (S i)) n0)).
Proof.   
  intros tr Htr i msg n0 lm0 H_fresh H_in0 p0 msg0 H_step H_deliver.
  rewrite H_deliver.
  simpl.
  rewrite (protocol_trace_state_sane Htr).
  rewrite node_eqb_refl. 
  destruct p0;
    assert (H_step_copy := H_step);
    destruct H_step as [H_update [H_out _]];
    rewrite H_update;
    rewrite H_out in H_fresh; simpl;
      try easy.
  unfold make_PrepareBlocks in H_fresh;
    simpl in H_fresh; tauto.
  simpl in H_fresh; destruct H_fresh. tauto.
  right. rewrite in_app_iff.  tauto.
  unfold make_PrepareBlocks in H_fresh; simpl in H_fresh; tauto. 
  apply in_app_iff; left; assumption.
  (* Vanquished bug here *)
  unfold make_PrepareBlocks in H_fresh; simpl in H_fresh; tauto. 
  apply in_app_iff; tauto.
Qed.

Lemma out_message_change_tells_sender :
  forall (tr : GTrace), protocol_trace tr ->
    forall (i : nat) (n0 : node)
    (p0 : NState_transition_type)
    (msg0 : message)
    (lm0 : list message),
    In n0 participants -> 
    (* g ~~> g' with fixed node and in/out messages *) 
    tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 -> 
    get_transition p0 (fst (tr i) n0) msg0 (fst (tr (S i)) n0) lm0 ->
    (* We know the node that processed the message, 
     although we don't necessarily know the message *) 
    forall (n : node),
      In n participants -> 
      (exists (msg : message), 
          In msg (out_messages (fst (tr (S i)) n)) /\
          ~ In msg (out_messages (fst (tr i) n))) ->
      n0 = n. 
Proof.
  intros tr Htr i n0 p0 msg0 lm0 H_in0 H_deliver H_step n H_in H_change.
  destruct (node_eq_dec n n0) as [H_eq | H_neq]. 
  - symmetry; assumption.
  - exfalso. 
    (* Proving a contradiction *)
    destruct H_change as [msg [H_new H_old]].
    (* For all non-n0 nodes, their out message nodes are exactly the same *)
    assert (H_eq_one : out_messages (fst (tr (S i)) n) = out_messages (fst (tr i) n)).
    { unfold broadcast_messages in H_deliver.
      rewrite (protocol_trace_state_sane Htr) in H_deliver.
      apply node_eqb_no in H_neq.
      rewrite H_deliver. 
      simpl. rewrite H_neq.
      assert (is_member n participants = true) by now apply
      is_member_correct. 
      rewrite H.
      unfold record_plural. 
      simpl. 
      reflexivity. }
    rewrite H_eq_one in H_new.
    contradiction.
Qed.

Lemma delivered_means_sender_made_transition :
  forall tr, protocol_trace tr ->
   forall i msg (n0 : node) (lm0 : list message),
    In msg lm0 ->
    In n0 participants ->
    forall (p0 : NState_transition_type) (msg0 : message),
     get_transition p0 (fst (tr i) n0) msg0 (fst (tr (S i)) n0) lm0 ->
    tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 ->
    get_sender msg = n0.
Proof.
  intros tr Htr i msg n0 lm0 H_fresh H_in0 p0 msg0 H_step H_deliver.
  destruct p0;
    assert (H_step_copy := H_step); 
    destruct H_step as [H_update [H_out H_rest]];
    rewrite H_out in H_fresh;
    simpl in H_fresh; 
    try (subst; reflexivity);
    try (destruct H_fresh;
         subst;
         unfold get_sender; simpl; reflexivity);
    repeat destruct H_fresh as [H_fresh | H_fresh];
    try contradiction;
    try rewrite <- H_fresh; simpl in *;
      try rewrite (protocol_trace_state_sane Htr);
      try reflexivity; 
      try tauto;
      try (apply pending_PrepareVote_correct in H_fresh;
           destruct H_fresh as [_ [H_fresh _]];
           rewrite H_fresh; simpl in *;
           rewrite (protocol_trace_state_sane Htr); reflexivity).
Qed.

Lemma global_local_out_if :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall i msg n,
      In n participants ->
      In msg (filter (fun msg => node_eqb (get_sender msg) n) (snd (tr i))) ->
      In msg (out_messages (fst (tr i) n)). 
Proof.
  intros tr Htr i msg n H_part H_in.
  pose proof Htr as Htr'.
  destruct Htr as [H_init H_prot].
  induction i. 
  - (* Base case *)
    rewrite H_init in H_in.
    inversion H_in.
  - (* IH says if it's in the global out messages in the previous state, then it's in the
       local out messages in the previous state. *)
    (* Either it's in the global out messages in the previous state, or it's not, 
       meaning it was newly sent *)
    (* Then it must be in the out messages by case analysis on the transitions *)
    destruct (In_dec message_eq_dec msg
      (filter (fun msg : message => node_eqb (get_sender msg) n) (snd (tr i)))) as [H_old | H_new].
    + spec IHi H_old.
      now apply out_messages_global_monotonic_step.
    + (* msg was not in n's part of the global out message buffer in state (tr i) *)
      (* But it is in n's part of the global out message buffer in state (tr (S i)) *)
      clear IHi. 
      apply filter_In in H_in. 
      destruct H_in as [H_in H_sender].
      (* First we establish that n is the sender *)
      assert (H_useful := filter_In (fun msg : message => node_eqb (get_sender msg) n) msg (snd (tr i))).
      assert (~ In msg (snd (tr i)) \/
              ~ (fun msg : message => node_eqb (get_sender msg) n) msg = true) by tauto; clear H_useful H_new. 
      destruct H.
      2 : contradiction. 
      (* Based on H and H_in, msg must have been newly added *)  
      (* Therefore, whatever transition happened, n must have made the transition *) 
      spec H_prot i.
      destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the transition case *)
        destruct (node_eq_dec n0 n) as [H_true | H_false].
        ** (* In the case that n made the transition *)
          rewrite H_true in *.
          rewrite H_deliver in H_in. 
          simpl in H_in. 
          rewrite in_app_iff in H_in.
          destruct H_in as [H_fresh | H_old].
          2 : contradiction.
          now apply (delivered_means_sent_local Htr' i msg n H_fresh H_part p0 msg0 H_step H_deliver).
        ** (* In the case that n didn't make the transition *)
          exfalso.
          rewrite H_deliver in H_in. 
          simpl in H_in.
          rewrite in_app_iff in H_in.
          destruct H_in as [H_fresh | H_old].
          2 : contradiction.
          assert (get_sender msg = n0) by
           apply (delivered_means_sender_made_transition Htr' i msg n0 H_fresh H_in0 p0 msg0 H_step H_deliver).
          apply node_eqb_correct in H_sender.
          subst; tauto.
      * (* In the timeout case *)
        assert (snd (tr i) = snd (tr (S i))). 
        { apply is_member_correct in H_part.
          rewrite H_timeout. 
          simpl. reflexivity. }
        rewrite H0 in H. contradiction.
Qed.

Lemma local_global_out_if :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall i msg n,
      In n participants ->
      In msg (out_messages (fst (tr i) n)) -> 
      In msg (snd (tr i)). 
Proof.
  intros tr H_prot i msg n H_part H_in.
  induction i as [|i IH_prot]. 
  - (* Base case *)
    destruct H_prot as [H_init _];
      rewrite H_init in H_in.
    inversion H_in.
  - destruct (In_dec message_eq_dec msg (out_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot H_old;
        now apply global_messages_monotonic_step.
    + clear IH_prot.
      assert (H_useful := out_messages_change_means_sent).
      pose proof H_prot as H_prot'.
      destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout]. 
      * assert (In msg lm0) by
         now apply (H_useful _ H_prot' _ _ _ msg0 lm0 H_in0 H_deliver H_step n H_part msg H_in H_new).
        rewrite H_deliver. 
        unfold broadcast_messages; simpl.
        rewrite in_app_iff; tauto.

      * rewrite H_timeout in H_in; simpl in H_in. 
        apply is_member_correct in H_part;
          rewrite H_part in H_in.
        contradiction.
Qed.

Lemma message_type_PrepareVote :
  forall tr i n msg1 b1,
    protocol_trace tr -> 
    In msg1 (processed_PrepareVote_in_view_about_block (fst (tr i) n) (node_view (fst (tr i) n)) b1) ->
    get_message_type msg1 = PrepareVote. 
Proof.
  intros. 
  apply filter_In in H0. destruct H0.
  repeat (apply andb_prop in H1; destruct H1).
  apply message_type_eqb_correct in H1. assumption.
Qed.

Lemma view_same_or_plus_one : 
  forall (tr : GTrace) (i : nat) (n : node),
    protocol_trace tr ->
    In n participants ->
    node_view (fst (tr i) n) = node_view (fst (tr (S i)) n) \/
    S (node_view (fst (tr i) n)) = node_view (fst (tr (S i)) n).
Proof. 
  intros tr i n H_prot H_part.
  pose proof H_prot as H_prot_copy.
  destruct H_prot as [_ H_prot]. 
  spec H_prot i.
  destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  - (* In the normal transition case *)
    destruct (node_eq_dec n0 n) as [H_same | H_diff].
    + rewrite H_same in *.
      destruct p0;
      destruct H_step as [H_update _];
      rewrite H_update; simpl; tauto.
    + left. rewrite H_deliver.
      simpl.
      rewrite (protocol_trace_state_sane H_prot_copy).
      rewrite node_eqb_comm.
      apply node_eqb_no in H_diff.
      rewrite H_diff.
      apply is_member_correct in H_part.
      rewrite H_part.
      reflexivity.
  - (* In the timeout case *)
    left. rewrite H_timeout.
    simpl. 
    apply is_member_correct in H_part.
    rewrite H_part.
    reflexivity.
Qed.

Lemma counting_messages_inclusion:
  forall (tr : GTrace) (i j : nat) (n : node) (msg : message),
    protocol_trace tr ->
    In n participants ->
    i <= j -> 
    In msg (counting_messages (fst (tr i) n)) ->
    In msg (counting_messages (fst (tr j) n)).
Proof. 
  intros tr i j n msg H_prot H_part H_view H_in.
  induction j as [|j IHj].
  - inversion H_view. subst. 
    destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - assert (i <= j \/ i = S j) by lia.
    destruct H as [H_le | H_eq].
    + spec IHj H_le.
      now apply counting_messages_monotonic.
    + subst. assumption. 
Qed. 

(** For any two states with views v and (S v), we can always find the exact two
intermediate states where that view change occurred. *) 
Lemma wedged_in_between :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i j : nat) (n : node),
      In n participants ->
      i < j ->
      S (node_view (fst (tr i) n)) = node_view (fst (tr j) n) ->
      exists (x : nat),
        i <= x <= j /\
        node_view (fst (tr x) n) = node_view (fst (tr i) n) /\
        node_view (fst (tr (S x)) n) = node_view (fst (tr j) n). 
Proof.
  intros tr H_prot i j n H_part H_past H_view.
  induction j as [|j IH_prot].
  - inversion H_past.
  - destruct (view_same_or_plus_one j n H_prot H_part) as [H_j_same | H_j_next].
    + assert (i < j \/ i = j) by lia.
      destruct H as [H_lt | H_eq].
      * spec IH_prot H_lt.
        spec IH_prot. lia.
        destruct IH_prot as [x [H_rel [H_view1 H_view2]]].
        exists x; repeat split; try lia.
      * subst; lia.  
    + clear IH_prot.
      exists j; repeat split; try lia.
Qed.

(** For any view smaller than the current view for any node, we can find
the state at which that view change occurred *) 
Lemma strongly_wedged_in_between :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n : node),
      In n participants ->
      forall (v_past : nat),
        v_past < node_view (fst (tr i) n) ->
        exists (i_past : nat),
        i_past < i /\
        node_view (fst (tr i_past) n) = v_past /\
        node_view (fst (tr (S i_past)) n) = S v_past. 
Proof.
  intros tr H_prot i n H_part v_past H_past.
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _];
      rewrite H_init in H_past;
      inversion H_past.
  - destruct (view_same_or_plus_one i n H_prot H_part) as [H_i_same | H_i_next].
    + spec IH_prot. lia.
      destruct IH_prot as [x [H_rel [H_view1 H_view2]]].
        exists x; repeat split; try lia.
    + rewrite <- H_i_next in H_past.
      assert (v_past = node_view (fst (tr i) n) \/ v_past < node_view (fst (tr i) n)) by lia. 
      destruct H as [H_eq | H_lt].
      * subst. clear IH_prot.
        exists i; repeat split; try lia.
      * spec IH_prot. lia.
        destruct IH_prot as [x [H_rel [H_view1 H_view2]]].
        exists x; repeat split; try lia. 
Qed.


Lemma state_view_morphism:
  forall tr : GTrace,
  protocol_trace tr ->
  forall (i1 i2 : nat) (n : node),
    In n participants ->
    node_view (fst (tr i1) n) < node_view (fst (tr i2) n) -> 
    i1 < i2. 
Proof.
  intros tr H_prot i1 i2 n H_part H_lt. 
  induction i2 as [|i2 IH_prot].
  - destruct H_prot as [H_init _].
    rewrite H_init in H_lt.
    inversion H_lt. 
  - destruct (view_same_or_plus_one i2 n H_prot H_part) as [H_same | H_incr].
    + rewrite <- H_same in H_lt.
      spec IH_prot H_lt.
      lia.
    + rewrite <- H_incr in H_lt.
      assert (node_view (fst (tr i1) n) = node_view (fst (tr i2) n) \/
              node_view (fst (tr i1) n) < node_view (fst (tr i2) n)) by lia; clear H_lt. 
      destruct H as [H_eq | H_lt].
      * clear IH_prot.
        (* View change occurred from i2 to S i2 *)
        (* i1 is in the same view as i2 *)
        rewrite <- H_eq in H_incr. 
        assert (node_view (fst (tr i1) n) < node_view (fst (tr (S i2)) n)) by lia.
        assert (H_useful := view_state_morphism).
        spec H_useful tr H_prot (S i2) i1 n H_part.
        apply modus_tollens in H_useful. lia.
        lia.
      * spec IH_prot H_lt; lia.
Qed.

Lemma participation_rights_global :
    forall (tr : GTrace),
      protocol_trace tr ->
      forall (i : nat) (msg : message),
        In msg (snd (tr i)) ->
        In (get_sender msg) participants.
Proof. 
  intros tr H_prot i. 
  induction i as [|i IH_prot]; intros msg H_in. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - destruct (In_dec message_eq_dec msg (snd (tr i))) as [H_old | H_new].
    + now apply IH_prot.
    + assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      rewrite H_deliver in H_in.
      simpl in H_in.
      apply in_app_iff in H_in;
        destruct H_in as [H_in | H_in];
        try contradiction.
      assert (get_sender msg = n0) by now apply delivered_means_sender_made_transition with tr i lm0 p0 msg0.
      rewrite H.
      assumption.
      rewrite H_timeout in H_in. simpl in H_in. contradiction.
Qed.

Lemma participation_rights :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat) (msg : message),
      In n participants ->
      In msg (counting_messages (fst (tr i) n)) ->
      In (get_sender msg) participants. 
Proof.
  intros tr H_prot n i msg H_part H_in.
  apply processed_means_sent_global in H_in;
    try assumption. 
  now apply participation_rights_global with tr i.
Qed. 

(** Any message property that holds for processed messages holds for sent messages *) 
Lemma lift_sent_to_received :
  forall (P : message -> Prop), 
    (forall (tr : GTrace),
        protocol_trace tr ->
        forall (n : node) (i : nat),
          In n participants ->
          forall (msg : message),
            In msg (out_messages (fst (tr i) n)) ->
            P msg) ->
    (forall (tr : GTrace),
        protocol_trace tr ->
        forall (n : node) (i : nat),
          In n participants ->
          forall (msg : message),
            In msg (counting_messages (fst (tr i) n)) ->
            P msg).
Proof.
  intros P H_helper tr H_prot n i H_part msg H_in.
  (* n processed msg -> n received msg *) 
  assert (H_useful := processed_means_past_received H_prot i n msg H_part H_in). 
  destruct H_useful as [i_past [H_past H_received]]. 
  (* n received msg -> msg in global sent buffer *)
  assert (H_useful2 := delivered_means_sent_global H_prot i_past n msg H_part H_received).
  assert (H_part_sender : In (get_sender msg) participants) by now apply (participation_rights H_prot n i msg H_part H_in).
  (* msg in global sent buffer -> msg in local sent buffer *)  
  assert (H_useful3 := @global_local_out_if tr H_prot i_past msg (get_sender msg) H_part_sender).
  spec H_useful3. apply filter_In; split; try easy.
  now rewrite node_eqb_refl.
  (* Now apply assumption *) 
  now apply H_helper with tr (get_sender msg) i_past.
Qed.

Lemma sent_PrepareVote_means_received_PrepareBlock :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat) (msg : message),
      In n participants ->
      In msg (out_messages (fst (tr i) n)) ->
      get_message_type msg = PrepareVote -> 
      exists (msg' : message),
        In msg' (counting_messages (fst (tr i) n)) /\
        get_message_type msg' = PrepareBlock /\
        get_block msg'= get_block msg /\
        get_view msg' = get_view msg. 
Proof.         
  intros tr H_prot n i msg H_part H_sent H_type.
  generalize dependent msg. 
  induction i as [|i IH_prot]; intros. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_sent;
      inversion H_sent.
  - destruct (In_dec message_eq_dec msg (out_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot msg H_old H_type.
      destruct IH_prot as [msg' IH_prot].
      exists msg'; repeat split; try tauto.
      now apply counting_messages_monotonic. 
    + clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot].
      spec H_prot i.
      destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      (* Establishing that n must be in lm0 *) 
      assert (In msg lm0). 
      apply (out_messages_change_means_sent H_prot_copy _ _ _ _ H_in0 H_deliver H_step _ H_part); try assumption.
      assert (n0 = n). 
      apply (out_message_change_tells_sender H_prot_copy _ _ _ _ H_in0 H_deliver H_step n H_part).
      exists msg; tauto. rewrite H0 in *.
      (* Case analysis on transition made from i ~~> S i *)
      destruct p0;
        assert (H_step_copy := H_step);
        destruct H_step as [H_update [H_broadcast H_rest]];
        rewrite H_broadcast in H;
        try apply in_inv in H;
        (* For cases that do not send messages *)
        try tauto;
        try (apply make_PrepareBlocks_message_type in H; 
             rewrite H_type in H; discriminate); 
        repeat destruct H as [H | H]; 
        try (subst; rewrite H_type in H_rest;
             assert (PrepareVote = PrepareQC) by tauto;
             discriminate);
        try (rewrite <- H in H_type; discriminate);
        try inversion H. 
      (* In the three cases where voting actually occurs,
       the existential witness is in H *)  
      
      apply in_map_iff in H;
      destruct H as [msg' [H_eq' H_about_msg']];
      exists msg'; rewrite <- H_eq';
      apply filter_In in H_about_msg';
      destruct H_about_msg' as [H_in' H_about_msg'];
      apply andb_prop in H_about_msg'.
      destruct H_about_msg' as [H_view' H_type'].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      rewrite message_type_eqb_correct in H_type'.
      repeat split; try tauto.
      now apply counting_messages_monotonic.
      unfold view_valid in H_rest.
      rewrite Nat.eqb_eq in H_view'.
      rewrite H_view'. symmetry; easy.

      apply in_map_iff in H;
      destruct H as [msg' [H_eq' H_about_msg']];
      exists msg'; rewrite <- H_eq';
      apply filter_In in H_about_msg';
      destruct H_about_msg' as [H_in' H_about_msg'];
      apply andb_prop in H_about_msg'.
      destruct H_about_msg' as [H_view' H_type'].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      rewrite message_type_eqb_correct in H_type'.
      repeat split; try tauto.
      now apply counting_messages_monotonic.
      unfold view_valid in H_rest.
      rewrite Nat.eqb_eq in H_view'.
      rewrite H_view'. symmetry; easy.

      apply in_map_iff in H;
      destruct H as [msg' [H_eq' H_about_msg']];
      exists msg'; rewrite <- H_eq';
      apply filter_In in H_about_msg';
      destruct H_about_msg' as [H_in' H_about_msg'];
      apply andb_prop in H_about_msg'.
      destruct H_about_msg' as [H_view' H_type'].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      apply andb_prop in H_view'.
      destruct H_view' as [H_view' _].
      rewrite message_type_eqb_correct in H_type'.
      repeat split; try tauto.
      now apply counting_messages_monotonic.
      unfold view_valid in H_rest.
      rewrite Nat.eqb_eq in H_view'.
      rewrite H_view'. symmetry; easy.
      
      (* In the timeout case *)
      rewrite H_timeout in H_sent. 
      apply is_member_correct in H_part;
        simpl in H_sent;
        rewrite H_part in H_sent;
        tauto.
Qed.

Lemma vote_quorum_current_view_persistent :
  forall (tr : GTrace), protocol_trace tr ->
  forall (n : node) (i : nat), In n participants ->
  forall (b : block), vote_quorum_in_view (fst (tr i) n) (node_view (fst (tr i) n)) b ->
  forall (j : nat), i <= j ->
  vote_quorum_in_view (fst (tr j) n) (node_view (fst (tr i) n)) b.
Proof.
  intros tr H_prot n i H_part b H_vote j H_le.
  unfold vote_quorum_in_view, processed_PrepareVote_in_view_about_block,
   processed_PrepareVote_in_view_about_block in *.
  assert (H_useful := @quorum_subset 
             (filter
                (fun msg : message =>
                 message_type_eqb (get_message_type msg)
                   PrepareVote && block_eqb (get_block msg) b &&
                 (get_view msg =? node_view (fst (tr i) n)))
                (counting_messages (fst (tr i) n)))
             (filter
                (fun msg : message =>
                 message_type_eqb (get_message_type msg)
                   PrepareVote && block_eqb (get_block msg) b &&
                 (get_view msg =? node_view (fst (tr i) n)))
                (counting_messages (fst (tr j) n)))
          H_vote).  
  spec H_useful.
  intros msg H_in.
  apply filter_In in H_in.
  destruct H_in as [H_in H_rest].
  apply filter_In.  
  split; try tauto.
  now apply counting_messages_inclusion with i.
  assumption.
Qed.

Definition PrepareVote_about_block_in_view_global (tr : GTrace) i b p :=
  filter
    (fun msg =>
       message_type_eqb (get_message_type msg) PrepareVote &&
       block_eqb (get_block msg) b &&
       Nat.eqb (get_view msg) p)
    (snd (tr i)). 

Definition PrepareVote_about_block_global (tr : GTrace) i b :=
  filter
    (fun msg =>
       message_type_eqb (get_message_type msg) PrepareVote &&
       block_eqb (get_block msg) b)
    (snd (tr i)).

Definition vote_quorum_in_view_global tr i b p :=
  quorum (PrepareVote_about_block_in_view_global tr i b p).

Lemma vote_quorum_in_view_persistent :
  forall (tr : GTrace), protocol_trace tr ->
  forall (n : node) (i : nat), In n participants ->
  forall (b : block) (p : nat), vote_quorum_in_view (fst (tr i) n) p b ->
  forall (j : nat), i <= j ->
  vote_quorum_in_view (fst (tr j) n) p b.
Proof.
  intros tr H_prot n i H_part b p H_vote j H_le.
  unfold vote_quorum_in_view, processed_PrepareVote_in_view_about_block in *.
  assert (H_useful := @quorum_subset
                        (filter
                           (fun msg : message =>
                              message_type_eqb
                                (get_message_type msg) PrepareVote &&
                              block_eqb (get_block msg) b &&
                              (get_view msg =? p))
                           (counting_messages (fst (tr i) n)))
                        (filter
                           (fun msg : message =>
                              message_type_eqb
                                (get_message_type msg) PrepareVote &&
                              block_eqb (get_block msg) b &&
                              (get_view msg =? p))
                           (counting_messages (fst (tr j) n)))
                        H_vote). 
  spec H_useful.
  intros msg H_in.
  apply filter_In in H_in.
  destruct H_in as [H_in H_rest].
  apply filter_In.  
  split; try tauto.
  now apply counting_messages_inclusion with i.
  assumption.
Qed.

Lemma vote_quorum_in_view_global_step :
  forall tr i b p,
    protocol_trace tr ->
    vote_quorum_in_view_global tr i b p ->
    vote_quorum_in_view_global tr (S i) b p. 
Proof.
  intros tr i b p H_prot H_vote. 
  unfold vote_quorum_in_view_global, PrepareVote_about_block_in_view_global in *.
  assert (H_useful := @quorum_subset
                        (filter
                           (fun msg : message =>
                              message_type_eqb (get_message_type msg) PrepareVote &&
                              block_eqb (get_block msg) b && (get_view msg =? p)) 
                           (snd (tr i)))
                        (filter
                           (fun msg : message =>
                              message_type_eqb (get_message_type msg) PrepareVote &&
                              block_eqb (get_block msg) b && (get_view msg =? p)) 
                           (snd (tr (S i))))
                        H_vote). 
  spec H_useful.
  intros msg H_in.
  apply filter_In in H_in.
  destruct H_in as [H_in H_rest].
  apply filter_In.  
  split; try tauto.
  now apply global_messages_monotonic_step.   
  assumption.
Qed. 

Lemma make_PrepareBlocks_message_type :
  forall s msg0 msg, 
  In msg (make_PrepareBlocks s msg0) ->
  get_message_type msg = PrepareBlock. 
Proof.         
  intros. unfold make_PrepareBlocks in H.
  simpl in H;
    destruct H as [H | [H | [H | H]]];
    subst; try easy.
Qed.

Lemma ViewChange_quorum_global :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (msg : message),
      In msg (snd (tr i)) ->
      get_message_type msg = ViewChange ->
      vote_quorum_in_view_global tr i (get_block msg) (get_view msg). 
Proof.
  intros tr H_prot i; 
    induction i as [|i IH_prot];
    intros msg H_in H_type.
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in. 
  -  destruct (In_dec message_eq_dec msg (snd (tr i))) as [H_old | H_new].
     + apply vote_quorum_in_view_global_step;
         try assumption.
       now apply IH_prot. 
     + assert (H_prot_copy := H_prot); 
         destruct H_prot as [_ H_prot];
         spec H_prot i;
         destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
       assert (H_in_copy := H_in); 
         rewrite H_deliver in H_in; 
         simpl in H_in;
         rewrite in_app_iff in H_in;
         destruct H_in as [H_in | H_in];
         try contradiction.
       assert (H_step_copy := H_step);
         destruct p0;
         destruct H_step as [H_update [H_out H_rest]];
         rewrite H_out in H_in; 
         (* For all cases that do not send messages *) 
         try (simpl in H_in;
              contradiction);
         try (apply make_PrepareBlocks_message_type in H_in;
              rewrite H_type in H_in; discriminate);
         try destruct H_in as [H_in | H_in]; 
         try (rewrite <- H_in in H_type;
              simpl in H_type;
              discriminate); 
         try (apply pending_PrepareVote_correct in H_in;
              rewrite H_type in H_in; easy).
       destruct H_in as [H_in | H_in]. 
       rewrite <- H_in in H_type;
         simpl in H_type; discriminate.
       (apply make_PrepareBlocks_message_type in H_in;
        rewrite H_type in H_in; discriminate).
       rewrite H_timeout in H_in;
         simpl in H_in.
       contradiction.
Qed.

Lemma vote_quorum_local_means_vote_quorum_global :
  forall tr,
    protocol_trace tr ->
    forall (i : nat) (n : node) (b1 : block) (p : nat),
      In n participants ->
      vote_quorum_in_view (fst (tr i) n) p b1 ->
      vote_quorum_in_view_global tr i b1 p. 
Proof.
  intros tr H_prot i n b1 p H_part H_local.
  red in H_local.
  apply quorum_subset with (processed_PrepareVote_in_view_about_block (fst (tr i) n) p b1); try assumption.
  intros msg H_in.
  apply filter_In; 
  apply filter_In in H_in. destruct H_in as [H_in H_typeblockview].
  split. apply processed_means_sent_global with n; try assumption.
  assumption.
Qed.

Lemma vote_quorum_in_view_step_global :
  forall tr i b p,
    protocol_trace tr ->
    vote_quorum_in_view_global tr i b p -> 
    vote_quorum_in_view_global tr (S i) b p. 
Proof.
  intros tr i b p H_prot H_prepare.
  red. 
  apply quorum_subset with (PrepareVote_about_block_in_view_global tr i b p).
  assumption. intros.
  apply filter_In in H. apply filter_In.
  split. destruct H. now apply global_messages_monotonic_step.
  tauto.
Qed.

Lemma qc_current_view_persistent :
 forall (tr : GTrace), protocol_trace tr ->
 forall (n : node) (i : nat), In n participants ->
 forall (b : block),
  (exists msg : message,
           In msg (counting_messages (fst (tr i) n)) /\
           get_view msg = node_view (fst (tr i) n) /\
           get_block msg = b /\ get_message_type msg = PrepareQC) ->
 forall (j : nat), i <= j ->
  exists msg : message,
    In msg (counting_messages (fst (tr j) n)) /\
    get_view msg = node_view (fst (tr i) n) /\
    get_block msg = b /\ get_message_type msg = PrepareQC.
Proof.                                                  
  intros tr H_prot n i H_part b H_QC j H_le.
  destruct H_QC as [msg [H_in [H_view [H_block H_type]]]].
  exists msg; repeat split; try assumption.
  now apply counting_messages_inclusion with i.
Qed.

Lemma qc_in_view_persistent :
 forall (tr : GTrace), protocol_trace tr ->
 forall (n : node) (i : nat), In n participants ->
 forall (b : block) (p : nat),
  (exists msg : message,
           In msg (counting_messages (fst (tr i) n)) /\
           get_view msg = p /\
           get_block msg = b /\ get_message_type msg = PrepareQC) ->
 forall (j : nat), i <= j ->
  exists msg : message,
    In msg (counting_messages (fst (tr j) n)) /\
    get_view msg = p /\
    get_block msg = b /\ get_message_type msg = PrepareQC.
Proof.                                                  
  intros tr H_prot n i H_part b p H_QC j H_le.
  destruct H_QC as [msg [H_in [H_view [H_block H_type]]]].
  exists msg; repeat split; try assumption.
  now apply counting_messages_inclusion with i.
Qed.

Lemma prepare_in_view_persistent :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      forall (b : block) (p : nat),
        prepare_stage_in_view (fst (tr i) n) p b ->
        forall (j : nat),
          i <= j ->
          prepare_stage_in_view (fst (tr j) n) p b.
Proof. 
  intros tr H_prot n i H_part b p H_prepare j H_le. 
  destruct H_prepare as [H_vote | H_QC]. 
  - left.
    now apply vote_quorum_in_view_persistent with i.
  - right.
    now apply qc_in_view_persistent with i.
Qed.

(** No blocks can be at prepare stage in [GState_init]. *)
Lemma no_prepare_blocks_GState_init :
  forall (n : node),
    In n participants ->
    forall (b : block),
      prepare_stage (fst GState_init n) b ->
      False.
Proof. 
  intros n H_in b H_stage.
  unfold GState_init in H_stage.
  destruct H_stage as [v_past [H_past H_prepare]]. 
  simpl in H_past. assert (v_past = 0) by lia.
  subst.
  destruct H_prepare as [H_vote | H_qc].
  - inversion H_vote.
    apply empty_has_no_two_thirds in H0. 
    contradiction.
  - inversion H_qc. simpl in H.
    tauto. 
Qed.
