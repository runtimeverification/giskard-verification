From Coq Require Import Arith Bool List.
From Giskard Require Import lib structures local global.

Import ListNotations.

Set Implicit Arguments.

(** * Safety property one: Prepare stage height injectivity *)

(** ** Prepare stage height injectivity definition *)

(** Recall that a block is in prepare stage in some local state iff it has
received quorum PrepareVote messages or a PrepareQC message in the current
view or some previous view. *) 

(** The first safety property states that no two same height blocks can be
at prepare stage in the same view, i.e., prepare stage block height is injective
in the same view. The first safety property differs from the following two in that
it contains an additional premise restricting the view during which the two blocks
reached prepare stage. This is important because it is possible for multiple blocks
at the same height to reach prepare stage across different views in the case of
abnormal view changes. *)

(** In any global state i in a valid protocol trace tr that begins with the initial
state and respects the protocol transition rules, if there are two participating
nodes n and m, and two blocks b1 b2, such that b1 and b2 have the same height,
and both reach prepare stage for n and m's local state respectively in some view p,
but are not equal, then we can prove a contradiction. *)

Definition prepare_stage_same_view_height_injective_statement :=
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node) (b1 b2 : block) (p : nat),
      In n participants ->
      In m participants ->
      b1 <> b2 ->
      prepare_stage_in_view (fst (tr i) n) p b1 -> 
      prepare_stage_in_view (fst (tr i) m) p b2 ->      
      b_height b1 = b_height b2 ->
      False.

(** ** Reducing the proof *)

(** Intuitively, the proof of this property follows directly from the definition of
non-Byzantine/honest voting behavior: honest nodes cannot vote for two conflicting
blocks during the same view. If two conflicting blocks reach prepare stage in the
same view, then two quorums of at least 2/3 validators voted for each block.
By the pigeonhole principle, there must exist a set of at least 1/3 validators who
voted for both conflicting blocks and are therefore Byzantine/dishonest. By assumption,
there are no more than 1/3 Byzantine/dishonest blocks. Therefore, we reach a contradiction. *)

(** The formal proof proceeds by identifying a series of conditions that can both prove
that there exist more than 1/3 dishonest nodes (bottom-up) and be proven from the
node-local premises (top-down), and leverages the global broadcast message buffer,
which can be viewed as a ghost variable. Starting with the bottom-up direciton, we
first identify the most obvious sufficient condition for a node to be dishonest:
a node n is dishonest if there exist two equivocating messages in its own local
out-message buffer. *)

(** Local evidence of malice. **) 
Definition equivocating_in_state (s : NState) : Prop :=
  exists (msg1 msg2 : message),
    In msg1 (out_messages s) /\
    In msg2 (out_messages s) /\
    get_view msg1 = get_view msg2 /\
    get_message_type msg1 = PrepareVote /\
    get_message_type msg2 = PrepareVote /\
    get_block msg1 <> get_block msg2 /\
    b_height (get_block msg1) = b_height (get_block msg2).

(** However, it turns out that this obvious definition of local evidence of malice is
not the weakest precondition for a node being dishonest: there is a sufficient condition
yet for local evidence of malice. Giskard's transition rules forbid nodes from processing
PrepareBlock messages for conflicting blocks. This in turn prevents nodes from sending
PrepareVote messages for conflicting blocks at the get-go: nodes can only send a PrepareVote
message for a block if they have received the corresponding PrepareBlock message for that
block. Therefore, a malicious node can be detected by the presence of two conflicting
PrepareBlock messages in its processed message buffer. *)

(** If a node has sent a PrepareVote message for some block, then it must have
processed a PrepareBlock message for that block in the same view. *)
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
      apply (out_messages_change_means_sent H_prot_copy _ _ _ _ H_in0 H_deliver H_step _ H_part);
        try assumption.
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

(** Thus, the following condition is sufficient to show local evidence of malice:
we say that a node is "pre-equivocating" if it has processed two PrepareBlock
messages for two different blocks of the same height in the same view. *)
Definition pre_equivocating_in_state (s : NState) : Prop :=
  exists (msg1 msg2 : message),
    In msg1 (counting_messages s) /\
    In msg2 (counting_messages s) /\
    get_view msg1 = get_view msg2 /\
    get_message_type msg1 = PrepareBlock /\
    get_message_type msg2 = PrepareBlock /\
    get_block msg1 <> get_block msg2 /\
    b_height (get_block msg1) = b_height (get_block msg2).

(** "Pre-equivocation" is a weaker notion than "equivocation". *) 
Lemma pre_local_means_local_evidence_of_equivocation :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      equivocating_in_state (fst (tr i) n) ->
      pre_equivocating_in_state (fst (tr i) n). 
Proof.
  intros tr H_prot n i H_part [msg1 [msg2 [H_sent1
   [H_sent2 [H_view [H_type1 [H_type2 [H_neq H_height_eq]]]]]]]].
  assert (H_received1 := @sent_PrepareVote_means_received_PrepareBlock
   tr H_prot n i msg1 H_part H_sent1 H_type1). 
  assert (H_received2 := @sent_PrepareVote_means_received_PrepareBlock
   tr H_prot n i msg2 H_part H_sent2 H_type2).   
  destruct H_received1 as [msg1' [H_processed1'
   [H_type1' [H_block1' H_view1']]]].
  destruct H_received2 as [msg2' [H_processed2'
   [H_type2' [H_block2' H_view2']]]].
  exists msg1', msg2'; repeat split; try tauto. 
  now rewrite H_view1', H_view2'. 
  now rewrite H_block1', H_block2'.
  now rewrite H_block1', H_block2'.
Qed.

(** Therefore, if we can prove dishonesty from pre-equivocation, then we can
prove dishonesty from equivocation. In other words, we must show the following: *)
Definition pre_local_evidence_of_equivocation_statement := 
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      pre_equivocating_in_state (fst (tr i) n) ->
      ~ honest_node n.

(** The proof of the above proceeds by induction, which requires the following two cases: *) 
Lemma pre_local_evidence_of_equivocation_middle_case :
 forall (tr : GTrace), protocol_trace tr ->
 forall (n : node) (i : nat), In n participants ->
 forall (msg1 msg2 : message),
  In msg1 (counting_messages (fst (tr (S i)) n)) ->
  In msg2 (counting_messages (fst (tr (S i)) n)) ->
  get_view msg1 = get_view msg2 ->
  get_message_type msg1 = PrepareBlock ->
  get_message_type msg2 = PrepareBlock ->
  get_block msg1 <> get_block msg2 ->
  b_height (get_block msg1) = b_height (get_block msg2) ->
  honest_node n ->
  In msg2 (counting_messages (fst (tr i) n)) ->
  ~ In msg1 (counting_messages (fst (tr i) n)) ->
  False. 
Proof.
  intros tr H_prot n i H_part msg1 msg2 H_sent1 H_sent2
    H_view H_type1 H_type2 H_neq H_height_eq H_false H_old2 H_new1.
  assert (H_prot_copy := H_prot); 
    destruct H_prot as [_ H_prot];
    spec H_prot i;
    destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  assert (n0 = n). 
  apply counting_message_different_tells_receiver with tr i p0 msg0 lm0; try assumption. 
  intros H_contra.
  rewrite H_contra in H_new1. contradiction.
  subst.
  assert (H_step_copy := H_step);
  destruct p0;
  destruct H_step as [H_update H_rest];
  rewrite H_update in H_sent1;
  (* In cases that do not process messages *) 
  try contradiction;
  (* In cases where n is not honest *) 
  try (rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
       tauto);
  try (simpl in H_sent1;
       destruct H_sent1 as [H_sent1 | H_sent1]);
  try contradiction;
  subst; 
  try (rewrite H_type1 in H_rest;
       easy). 
  (assert (H_contra : ~ exists_same_height_PrepareBlock (fst (tr i) n) (get_block msg1)) by tauto;
       apply H_contra;
       exists msg2; split; try tauto). 
  (assert (H_contra : ~ exists_same_height_PrepareBlock (fst (tr i) n) (get_block msg1)) by tauto;
       apply H_contra;
       exists msg2; split; try tauto).
  simpl in H_type1. discriminate.
  destruct H_sent1 as [H_sent1 | H_sent1].
  subst.
  rewrite H_type1 in H_rest. easy.
  contradiction.
  destruct H_sent1 as [H_sent1 | H_sent1].
  subst.
  simpl in H_type1. discriminate.
  contradiction.
  rewrite H_timeout in H_sent1; simpl in H_sent1.
  apply is_member_correct in H_part.
  rewrite H_part in H_sent1; contradiction.
Qed.

Lemma pre_local_evidence_of_equivocation_last_case :
 forall (tr : GTrace), protocol_trace tr ->
 forall (n : node) (i : nat), In n participants ->
 forall (msg1 msg2 : message),
  In msg1 (counting_messages (fst (tr (S i)) n)) ->
  In msg2 (counting_messages (fst (tr (S i)) n)) ->
  get_view msg1 = get_view msg2 ->
  get_message_type msg1 = PrepareBlock ->
  get_message_type msg2 = PrepareBlock ->
  get_block msg1 <> get_block msg2 ->
  b_height (get_block msg1) = b_height (get_block msg2) ->
  honest_node n ->
  ~ In msg2 (counting_messages (fst (tr i) n)) ->
  ~ In msg1 (counting_messages (fst (tr i) n)) ->
  False.
Proof.
  intros tr H_prot n i H_part msg1 msg2 H_sent1 H_sent2 H_view
   H_type1 H_type2 H_neq H_height_eq H_false H_new2 H_new1.
  assert (H_prot_copy := H_prot); 
    destruct H_prot as [_ H_prot];
    spec H_prot i;
    destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  assert (n0 = n). 
  apply counting_message_different_tells_receiver with tr i p0 msg0 lm0; try assumption. 
  intros H_contra.
  rewrite H_contra in H_new1. contradiction.
  subst.
  assert (H_step_copy := H_step);
    destruct p0;
    destruct H_step as [H_update H_rest];
    rewrite H_update in H_sent1;
    rewrite H_update in H_sent2; 
    (* In cases that do not process messages *) 
    try contradiction;
    (* In cases where n is not honest *) 
    try (rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
         tauto);
    simpl in H_sent1, H_sent2; 
      destruct H_sent1 as [H_sent1 | H_sent1];
      destruct H_sent2 as [H_sent2 | H_sent2];
      try contradiction; 
      try (rewrite <- H_sent1, <- H_sent2 in H_neq; easy);
  try (rewrite <- H_sent1 in H_type1; simpl in H_type1; discriminate);
  try (rewrite <- H_sent2 in H_type2; simpl in H_type2; discriminate).
    simpl in H_sent1, H_sent2; 
      destruct H_sent1 as [H_sent1 | H_sent1];
      destruct H_sent2 as [H_sent2 | H_sent2].
      try (rewrite <- H_sent1, <- H_sent2 in H_neq; easy). 
      contradiction. contradiction. contradiction.
      destruct H_sent2 as [H_sent2 | H_sent2].
      rewrite <- H_sent2 in H_type2; simpl in H_type2; discriminate. 
      contradiction.
      destruct H_sent1 as [H_sent1 | H_sent1].
      (rewrite <- H_sent1 in H_type1; simpl in H_type1; discriminate). 
      contradiction.
      destruct H_sent2 as [H_sent2 | H_sent2].
      try (rewrite <- H_sent2 in H_type2; simpl in H_type2; discriminate).
      contradiction.
          rewrite H_timeout in H_sent1; simpl in H_sent1.
          apply is_member_correct in H_part.
          rewrite H_part in H_sent1; contradiction.
Qed.

(** Finally, we can show that evidence of "pre-equivocation" is sufficient
to show that a node is dishonest: *) 
Lemma pre_local_evidence_of_equivocation :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      pre_equivocating_in_state (fst (tr i) n) ->
      ~ honest_node n.
Proof. 
  intros tr H_prot n i H_part [msg1 [msg2 [H_sent1 [H_sent2
   [H_view [H_type1 [H_type2 [H_neq H_height_eq]]]]]]]] H_false.
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _].
    rewrite H_init in H_sent1. 
    inversion H_sent1. 
  - destruct (In_dec message_eq_dec msg2 (counting_messages (fst (tr i) n))) as [H_old2 | H_new2].
    + destruct (In_dec message_eq_dec msg1 (counting_messages (fst (tr i) n))) as [H_old1 | H_new1].
      * now apply IH_prot. 
      * clear IH_prot.
        now apply pre_local_evidence_of_equivocation_middle_case with tr n i msg1 msg2.  
    + destruct (In_dec message_eq_dec msg1 (counting_messages (fst (tr i) n))) as [H_old1 | H_new1].
      * apply pre_local_evidence_of_equivocation_middle_case with tr n i msg2 msg1; try assumption; try easy.
        intro H_eq. symmetry in H_eq. contradiction.
      * clear IH_prot.
        now apply pre_local_evidence_of_equivocation_last_case with tr n i msg1 msg2. 
Qed.

(** And therefore, we can prove dishonesty from equivocation by weakning the premise: *) 
Lemma local_evidence_of_equivocation :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
    In n participants ->
    equivocating_in_state (fst (tr i) n) ->
    ~ honest_node n.
Proof.
  intros tr H_prot n i H_part H_equiv.
  apply pre_local_means_local_evidence_of_equivocation in H_equiv; try assumption.
  now apply pre_local_evidence_of_equivocation with tr i.
Qed.

(** Continuing to identify conditions from the bottom up, we have established that
in order to show that more than 1/3 participating nodes are dishonest, we must show
that more than 1/3 participating nodes show local evidence of malice. In order to
show local evidence of malice, it suffices to show global evidence of malice. *)

(** Global evidence of malice. **) 
Definition equivocating_in_global_state (s : GState) (n : node) := 
  exists msg1 msg2 : message,
    In msg1 (snd s) /\
    In msg2 (snd s) /\
    get_sender msg1 = n /\
    get_sender msg2 = n /\ 
    get_view msg1 = get_view msg2 /\
    get_message_type msg1 = PrepareVote /\
    get_message_type msg2 = PrepareVote /\
    get_block msg1 <> get_block msg2 /\
    b_height (get_block msg1) = b_height (get_block msg2).

(** Proving that global evidence of malice is indeed a sufficient condition
for local evidence of malice: *)
Lemma global_equivocating_local :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      equivocating_in_global_state (tr i) n ->
      equivocating_in_state (fst (tr i) n). 
Proof.   
  intros tr H_prot n i H_part H_global.
  destruct H_global as [msg1 [msg2 H_global]].
  exists msg1, msg2; repeat split; try tauto;
    try 
      (apply global_local_out_if; try assumption;
       apply filter_In; split; try tauto;
       apply node_eqb_correct; tauto).
Qed.

(** We identify yet another sufficient condition for global evidence of malice:
there exist two vote quorums for b1 and b2 in the global broadcast message buffer.
We show that this is indeed a sufficient condition by completing the following
chain of reasoning:
- we have two global vote quorums, which implies
- more than one third global evidence of malice, which implies
- more than one third local evidence of malice, which implies
- more than one third of nodes are dishonest. *)
Lemma vote_quorum_same_view_global_injective :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (b1 b2 : block) (p : nat),
      b1 <> b2 ->
      vote_quorum_in_view_global tr i b1 p -> 
      vote_quorum_in_view_global tr i b2 p ->      
      b_height b1 = b_height b2 ->
      False.
Proof. 
  intros tr H_prot i b1 b2 p H_neq H_prepare1 H_prepare2 H_height.
  red in H_prepare1, H_prepare2.  
  assert (H_useful := intersection_property). 
  unfold quorum in H_prepare1, H_prepare2.
  spec H_useful (map get_sender (PrepareVote_about_block_in_view_global tr i b1 p))
    (map get_sender (PrepareVote_about_block_in_view_global tr i b2 p)) H_prepare1 H_prepare2. 
  destruct H_useful as [l_inter [H_inter H_subset]].
  (* All overlapping nodes are participants *) 
  assert (H_part : forall n, In n l_inter -> In n participants).
  { intros n H_in.
    spec H_subset n H_in. 
    destruct H_subset as [H _].
    apply in_map_iff in H.
    destruct H as [msg [H_sender H_global]].
    apply filter_In in H_global.
    rewrite <- H_sender.
    apply participation_rights_global with tr i; try tauto. }
  (* All overlapping nodes are equivocating in global state *) 
  assert (H_step1 : forall n, In n l_inter -> equivocating_in_global_state (tr i) n). 
  { intros n H_in. spec H_subset n H_in. 
    destruct H_subset as [H_in1 H_in2].
    apply in_map_iff in H_in1.
    destruct H_in1 as [msg1 [H_sender1  H_sent1]].
    apply in_map_iff in H_in2.
    destruct H_in2 as [msg2 [H_sender2 H_sent2]].
    apply filter_In in H_sent1;  
      apply filter_In in H_sent2.
    destruct H_sent1 as [H_sent1 H_rest1]. 
    apply andb_prop in H_rest1.
    destruct H_rest1 as [H_type1 H_view1].
    apply andb_prop in H_type1.
    destruct H_type1 as [H_type1 H_block1].
    destruct H_sent2 as [H_sent2 H_rest2]. 
    apply andb_prop in H_rest2.
    destruct H_rest2 as [H_type2 H_view2].
    apply andb_prop in H_type2.
    destruct H_type2 as [H_type2 H_block2]. 
    apply beq_nat_true in H_view1.
    apply beq_nat_true in H_view2.
    apply message_type_eqb_correct in H_type1.
    apply message_type_eqb_correct in H_type2.
    apply block_eqb_correct in H_block1.
    apply block_eqb_correct in H_block2.
    exists msg1, msg2; repeat split; try tauto; try (subst; easy). }
  (* All overlapping nodes are equivocating in their local state *) 
  assert (H_step2 : forall n, In n l_inter -> equivocating_in_state (fst (tr i) n)). 
  { intros n H_in.
    spec H_step1 n H_in.
    apply global_equivocating_local; try assumption.
    spec H_subset n H_in. 
    destruct H_subset as [H _].
    apply in_map_iff in H.
    destruct H as [msg [H_sender H_global]].
    apply filter_In in H_global.
    rewrite <- H_sender.
    apply participation_rights_global with tr i; try tauto. }
  (* All nodes equivocating in their local state are malicious *) 
  assert (H_step3 : forall n, In n l_inter -> ~ honest_node n).
  { intros n H_in.
    spec H_part n H_in. 
    spec H_step2 n H_in.
    now apply local_evidence_of_equivocation with tr i. }
  apply evil_participants.
  apply minority_subset with l_inter; try assumption.
  intros n H_in.
  apply filter_In. split.
  now apply H_part.
  apply negb_true_iff.
  apply H_step3 in H_in.
  case_eq (honest_nodeb n); auto.
  intro.
  apply honest_nodeb_correct in H; congruence.
Qed.

(** Finally, we close the gap from the top down direction by showing that from
our node-local <<prepare_stage_in_view>> assumption, we can prove the existence
of vote quorum in the global broadcast message buffer. There are two cases 
of <<prepare_stage_in_view>>, either a vote quorum in the local processed
message buffer, or a PrepareQC message in the local processed message buffer.
We show the first case: *)
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
  apply quorum_subset with
      (processed_PrepareVote_in_view_about_block (fst (tr i) n) p b1);
    try assumption.
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

Lemma witnessed_quorum_global :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (msg : message),
      In msg (snd (tr i)) ->
      get_message_type msg = PrepareQC ->
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
       * (* In the normal transition case *)
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
           (* For all cases that send messages of the wrong type *) 
           try (apply make_PrepareBlocks_message_type in H_in;
                rewrite H_in in H_type; discriminate);
           simpl in H_in;
           repeat destruct H_in as [H_in | H_in];
           try contradiction;
           try (apply pending_PrepareVote_correct in H_in;
                rewrite H_type in H_in;
                easy);
           try (rewrite <- H_in in H_type;
                simpl in H_type;
                discriminate).
         (* In the three cases that actually do send PrepareQC messages *) 
         **  (* In the PrepareVote vote case *) 
           assert (H_if : vote_quorum_in_view (fst (tr (S i)) n0) (get_view msg0) (get_block msg0)).
           assert (H_extract : vote_quorum_in_view (process (fst (tr i) n0) msg0)
             (get_view msg0) (get_block msg0)) by tauto.
           rewrite H_update.
           red in H_extract. apply quorum_subset with
            (processed_PrepareVote_in_view_about_block (process (fst (tr i) n0) msg0)
            (get_view msg0) (get_block msg0)).
           assumption. intros. apply filter_In in H.
           destruct H as [H_in' H_rest'].
           simpl in H_in'. destruct H_in' as [H_in' | H_in'].
           subst. apply filter_In. simpl. split. left; reflexivity.
           tauto. apply filter_In. simpl. split. right. tauto.
           tauto. 
           apply vote_quorum_local_means_vote_quorum_global in H_if; try assumption.
           rewrite <- H_in. simpl.
           assert (H_view_eq : view_valid (fst (tr i) n0) msg0) by tauto.
           unfold view_valid in H_view_eq. rewrite H_view_eq. assumption.
         ** (* In the ViewChange case *)
           (* We want to show that the block contained in the highest ViewChange message
              has reached vote_quorum globally *)
           spec IH_prot {|
            get_message_type := PrepareQC;
            get_view := get_view msg0;
            get_sender := get_sender msg0;
            get_block := get_block (highest_ViewChange_message (process (fst (tr i) n0) msg0));
            get_piggyback_block := GenesisBlock |}.
           spec IH_prot.
           apply delivered_means_sent_global with n0; try assumption.
           tauto. spec IH_prot. reflexivity.
           apply vote_quorum_in_view_global_step; try assumption.
           simpl in IH_prot.
           rewrite <- H_in. simpl.
           assert (H_view_eq : view_valid (fst (tr i) n0) msg0) by tauto.
           rewrite H_view_eq. assumption.
       * rewrite H_timeout in H_in; simpl in H_in; contradiction.
Qed.

(** And the second case, with some help from the two lemmas above: *) 
Lemma PrepareQC_local_means_vote_quorum_global :
  forall tr, protocol_trace tr ->
    forall (i : nat) (n : node) (b1 : block) (p : nat),
      In n participants ->
      PrepareQC_in_view (fst (tr i) n) p b1 -> 
      vote_quorum_in_view_global tr i b1 p. 
Proof.
  intros tr H_prot i n b1 p H_part H_local.
  assert (H_useful := witnessed_quorum_global). 
  destruct H_local as [msg [H_processed [H_view [H_block H_type]]]].
  spec H_useful tr H_prot i msg. 
  spec H_useful.
  apply processed_means_sent_global with n; try assumption.
  spec H_useful H_type.
  rewrite <- H_block. rewrite <- H_view.
  assumption.
Qed.

(** ** Proof of prepare stage height injectivity *)

(** Finally, we are ready to string everything together to prove the statement
of the first safety theorem: *)
Theorem prepare_stage_same_view_height_injective :
  prepare_stage_same_view_height_injective_statement.
Proof. 
  intros tr H_prot i n m b1 b2 p H_part1 H_part2 H_neq H_prepare1 H_prepare2 H_height.
  unfold prepare_stage in H_prepare1, H_prepare2.
  destruct H_prepare1 as [H_vote1 | H_QC1];
    destruct H_prepare2 as [H_vote2 | H_QC2]. 
  - apply vote_quorum_local_means_vote_quorum_global in H_vote1; try assumption.
    apply vote_quorum_local_means_vote_quorum_global in H_vote2; try assumption.
    now apply vote_quorum_same_view_global_injective with tr i b1 b2 p.
  - apply vote_quorum_local_means_vote_quorum_global in H_vote1; try assumption.
    apply PrepareQC_local_means_vote_quorum_global in H_QC2; try assumption.
    now apply vote_quorum_same_view_global_injective with tr i b1 b2 p.
  - apply vote_quorum_local_means_vote_quorum_global in H_vote2; try assumption.
    apply PrepareQC_local_means_vote_quorum_global in H_QC1; try assumption.
    now apply vote_quorum_same_view_global_injective with tr i b1 b2 p.
  - apply PrepareQC_local_means_vote_quorum_global in H_QC1; try assumption.
    apply PrepareQC_local_means_vote_quorum_global in H_QC2; try assumption.
    now apply vote_quorum_same_view_global_injective with tr i b1 b2 p.
Qed.
