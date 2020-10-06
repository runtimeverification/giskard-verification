From Coq Require Import Arith Bool List Lia Classical.
From Giskard Require Import lib structures local global prepare.
 
Import ListNotations.

Set Implicit Arguments.
 
(** * Safety property two: Precommit stage height injectivity *)

(** ** Precommit stage definition *)

(** We say that a block is in precommit stage in some local state iff it is in
prepare stage, and its child block is in prepare stage, i.e., it has received
quorum PrepareVote messages or a PrepareQC message in the current view or
some previous view. *)
Definition precommit_stage (tr : GTrace) (i : nat) (n : node) (b : block) :=
  exists b_child,
    parent_of b_child = b /\ 
    prepare_stage (fst (tr i) n) b /\  
    prepare_stage (fst (tr i) n) b_child.

(** Before we formally state the second safety property, we first motivate
the definition of precommit stage and establish some facts about the relationship
between prepare stage and precommit stage. *)

(** In particular, for a block to be in precommit stage we require that it is
in prepare stage in that local state. In other words, the definition must satisfy
that local precommit stage implies local prepare stage: *)
Lemma precommit_means_prepare :
  forall tr i b n,
    protocol_trace tr ->
    In n participants -> 
    precommit_stage tr i n b ->
    prepare_stage (fst (tr i) n) b. 
Proof.
  intros tr i b n H_prot H_part H_precommit.
  destruct H_precommit as [b_child [H_parent [H_prepare_parent H_prepare_child]]].
  destruct H_prepare_child as [v [H_past H_prepare_child]]. 
  assumption. 
Qed.

(** We motivate this requirement below. Consider the following statement: *)
Definition prepare_stage_parent_prepare_stage :=
  forall tr i n b,
    protocol_trace tr ->
    In n participants -> 
    prepare_stage (fst (tr i) n) b ->
    prepare_stage (fst (tr i) n) (parent_of b). 

(** While seemingly innocuous, this statement is false. This is evidenced by the following
counterexample:
- A, B, C and D are participating in the protocol, and blocks b1, b2 and b3 have been proposed.
- A, B and C receive PrepareBlock messages for b1, and broadcast PrepareVote messages for b1.
- A, B and C receive one another's PrepareVote(_, b1) messages, and respectively witness quorums
  for b1, broadcasting PrepareQC(_, b1) and PrepareVote(_, b2).
- A receives PrepareVote(B, b2) and PrepareVote(C, b2) first, and alongside its own PrepareVote(A, b2),
  it witnesses a quorum for b2 and broadcasts PrepareQC (A, b2).

At this point, node D's input message buffer contains PrepareVote messages for b1 and b2, PrepareQC
messages for b1, and PrepareQC(A, b1). In the case that D processes PrepareQC(A, b2) first, block
b2 reaches prepare stage in D's local state, but b2's parent block, b1, has not reached prepare
stage in D's local state, nor has D himself voted for either b1 or b2. *)

(** This counterexample further illustrates that the prepare stage status of a block in a local
view is *independent of* whether the node has personally cast a vote for the block - if there
are enough nodes in the protocol to form a quorum, a laggy node (e.g. node D in the example above)
can simply sit idle and receive votes from others to enter blocks into prepare stage locally. *)

(** The converse, however, holds: if an honest node has personally cast a vote for some block,
then the parent block must be at prepare stage locally: *)
Lemma sent_PrepareVote_means_parent_block_prepare_local :
  forall tr i n b p,
    protocol_trace tr ->
    In n participants ->
    honest_node n ->
    (* Node n has sent a PrepareVote for block b in view p *)
    In (mkMessage PrepareVote p n b GenesisBlock) (out_messages (fst (tr i) n)) ->
    (* The parent of block b must be in prepare stage, i.e. have received enough
       votes in the current or some past view. *)
    prepare_stage (fst (tr i) n) (parent_of b). 
Proof.
  intros tr i n b p H_prot H_part H_honest H_in.  
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - assert (H_view := view_same_or_plus_one i n H_prot H_part).
    destruct (In_dec message_eq_dec (mkMessage PrepareVote p n b GenesisBlock)
     (out_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot H_old.
      destruct IH_prot as [p' [H_past H_prepare]]. 
      exists p'; split; try tauto.
      lia.
      apply prepare_in_view_persistent with i;
        try assumption;
        try lia. 
    + clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the normal transition case *)
        assert (H_sender : n0 = n).
        { apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption.
          exists (mkMessage PrepareVote p n b GenesisBlock);
            tauto. } 
        rewrite H_sender in *.
        destruct p0;
          assert (H_step_copy := H_step);
          destruct H_step as [H_update H_rest];
          rewrite H_update in H_in;
          simpl in H_in;
          try rewrite in_app_iff in H_in;
          repeat destruct H_in as [H_in | H_in];
          try contradiction;
          try discriminate.
        (* In the case of PrepareVote vote *)
        (* There must be a PrepareBlock *)
        unfold pending_PrepareVote in H_in. 
        apply in_map_iff in H_in.
        destruct H_in as [pb_msg [H_eq H_in]]. 
        apply filter_In in H_in.
        destruct H_in as [H_in H_about].
        apply andb_prop in H_about.
        destruct H_about as [H_about H_type]. 
        apply andb_prop in H_about.
        destruct H_about as [H_about H_parent].
        apply parent_ofb_correct in H_parent.
        assert (parent_of b = get_block msg0).
        assert (get_block (make_PrepareVote (fst (tr i) n) msg0 pb_msg) =
         get_block (mkMessage PrepareVote p n b GenesisBlock)).
        { apply f_equal. easy. }
        unfold get_block in H. simpl in H.
        rewrite <- H. assumption. 
        rewrite H. 
        rewrite H_update. 
        assert (H_prepare : vote_quorum_in_view (process (fst (tr i) n) msg0)
         (get_view msg0) (get_block msg0)) by tauto. 
        exists (get_view msg0).        split.
        simpl. unfold view_valid in H_rest. lia.
        left. assumption.

        (* In the case of PrepareQC *) 
        unfold pending_PrepareVote in H_in. 
        apply in_map_iff in H_in.
        destruct H_in as [pb_msg [H_eq H_in]]. 
        apply filter_In in H_in.
        destruct H_in as [H_in H_about].
        apply andb_prop in H_about.
        destruct H_about as [H_about H_type]. 
        apply andb_prop in H_about.
        destruct H_about as [H_about H_parent].
        apply parent_ofb_correct in H_parent.
        assert (parent_of b = get_block msg0).
        assert (get_block (make_PrepareVote (fst (tr i) n) msg0 pb_msg) =
         get_block (mkMessage PrepareVote p n b GenesisBlock)).
        { apply f_equal. easy. }
        unfold get_block in H. simpl in H.
        rewrite <- H. assumption. 
        rewrite H. 

        exists (node_view (fst (tr (S i)) n)). split. lia.
        rewrite H_update. 
        right. exists msg0. repeat split.
        simpl; tauto.
        unfold view_valid in H_rest.  simpl.
        symmetry; tauto. tauto.
        (* In the case of PrepareBlock malicious *)
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest.
        tauto.
        
      * (* In the timeout case *)
        rewrite H_timeout in H_in; simpl in H_in.
        apply is_member_correct in H_part;
          rewrite H_part in H_in; contradiction.
Qed.

(** However, the prepare stage status of blocks and the prepare stage status of
their parent blocks are not unrelated - Giskard's criterion for voting states that
nodes can only vote for blocks whose parent block has reached prepare stage.
In other words, the criterion for voting in Giskard concerns what messages have
been received, i.e., sent globally, but not what messages have been sent locally. *)

(** We can show that if a block is in prepare stage in some local state, then its
parent block is in prepare stage in the global state, meaning that a quorum of
votes must have been cast by all participating nodes, if not by itself. In the
example above, when D processes PrepareQC(A, b2), it is certainly true that the
global state has witnessed a quorum of PrepareVote messages for b1, even though
D's local state has not. We formalize this notion of global prepare stage as follows. *)

(** Similar to [prepare_stage_in_view], we first define a version of the global
prepare stage definition which takes a particular view as a parameter. While
local prepare stage definitions reason about local counting_message buffers,
e.g., <<counting_messages (fst (tr i) n)>>, global prepare stage definitions
reason about the global message buffer <<snd (tr i)>>: *)
Definition PrepareVote_about_block_in_view_global (tr : GTrace) i b p :=
  filter
    (fun msg =>
       message_type_eqb (get_message_type msg) PrepareVote &&
       block_eqb (get_block msg) b &&
       Nat.eqb (get_view msg) p)
    (snd (tr i)).

Definition vote_quorum_in_view_global tr i b p :=
  quorum (PrepareVote_about_block_in_view_global tr i b p). 

Definition PrepareQC_in_view_global (tr : GTrace) i b p :=
  exists msg : message,
    In msg (snd (tr i)) /\
    get_view msg = p /\
    get_block msg = b /\
    get_message_type msg = PrepareQC.

(** Similar to local prepare stage [prepare_stage_in_view], we define global
prepare stage in some view as the disjunction of the two cases: in that
view, either the block has received a quorum of PrepareVote messages,
or it has received a PrepareQC message: *)
Definition prepare_stage_in_view_global tr i b p :=
  vote_quorum_in_view_global tr i b p \/
  PrepareQC_in_view_global tr i b p.

(** The property of being in local prepare stage is persistent: once a block
reaches prepare stage in some local state, it remains in prepare stage for
all future states of that node: *)
Lemma prepare_stage_persistent :
  forall tr : GTrace,
    protocol_trace tr ->
    forall (n : node) (i : nat),
      In n participants ->
      forall (b : block),
        prepare_stage (fst (tr i) n) b ->
        forall j : nat, i <= j ->
          prepare_stage (fst (tr j) n) b. 
Proof.
  intros tr H_prot n i H_part b H_prepare j H_past.
  destruct H_prepare as [v' [H_past' H_prepare]].
  exists v'. split.
  assert (H_useful := view_state_morphism).
  spec H_useful tr H_prot i j n H_part H_past. lia.
  now apply prepare_in_view_persistent with i.
Qed.

(** We can prove a similar fact for [prepare_stage_in_view_global]. *)
Lemma prepare_stage_in_view_step_global :
  forall tr i b p,
    protocol_trace tr ->
    prepare_stage_in_view_global tr i b p -> 
    prepare_stage_in_view_global tr (S i) b p. 
Proof.
  intros tr i b p H_prot H_prepare.
  destruct H_prepare as [H_vote | H_qc].
  left.
  unfold vote_quorum_in_view_global in H_vote.
  red. 
  apply quorum_subset with (PrepareVote_about_block_in_view_global tr i b p).
  assumption. intros.
  apply filter_In in H. apply filter_In.
  split. destruct H. now apply global_messages_monotonic_step.
  tauto.
  right. destruct H_qc as [msg [H1 [H2 H3]]].
  exists msg; repeat split; try tauto.
  now apply global_messages_monotonic_step.
Qed.

Lemma prepare_stage_in_view_persistent_global :
  forall tr i j b p,
    protocol_trace tr ->
    i < j -> 
    prepare_stage_in_view_global tr i b p -> 
    prepare_stage_in_view_global tr j b p. 
Proof.
  intros tr i j b p H_prot H_past H_prepare.
  destruct H_prepare as [H_vote | H_qc].
  left.
  unfold vote_quorum_in_view_global in H_vote.
  red. 
  apply quorum_subset with (PrepareVote_about_block_in_view_global tr i b p).
  assumption. intros.
  apply filter_In in H. apply filter_In.
  split. destruct H. now apply global_messages_monotonic with i.
  tauto.
  right. destruct H_qc as [msg [H1 [H2 H3]]].
  exists msg; repeat split; try tauto.
  now apply global_messages_monotonic with i.
Qed.

(** The following fact follows directly from the definition
of [prepare_stage_in_view_global]: *)
Lemma prepare_in_view_means_PrepareVote_PrepareQC_exists_global : 
  forall tr i,
    protocol_trace tr ->
    forall (b : block) (x : nat),
      prepare_stage_in_view_global tr i b x ->
      exists (msg1 : message),
        In msg1 (snd (tr i)) /\
        get_view msg1 = x /\
        get_block msg1 = b /\ 
        (get_message_type msg1 = PrepareVote \/
         get_message_type msg1 = PrepareQC). 
Proof.
  intros tr i H_prot b x H_prepare.
  destruct H_prepare as [H_quorum | H_qc]. 
  - apply empty_has_no_two_thirds' in H_quorum.
    destruct H_quorum as [n H_in].
    apply in_map_iff in H_in.
    destruct H_in as [msg [H_sender H_in]].
    apply filter_In in H_in. 
    destruct H_in as [H_in H_typeblockview].
    apply andb_true_iff in H_typeblockview.
    destruct H_typeblockview as [H_typeblock H_view].
    apply andb_prop in H_typeblock. 
    destruct H_typeblock as [H_type H_block].
    apply message_type_eqb_correct in H_type.
    apply Nat.eqb_eq in H_view.
    apply block_eqb_correct in H_block.
    exists msg; repeat split; try tauto.
  - destruct H_qc as [msg H_qc].
    exists msg; repeat split; try tauto.
Qed.

(** We can then define [prepare_stage_global] using [prepare_stage_in_view_global],
similar to how we defined [prepare_stage] using [prepare_stage_in_view]: *)
Definition prepare_stage_global tr i b :=
  exists p, prepare_stage_in_view_global tr i b p. 

(** We can easily establish the relationship between local and global prepare
stages through the relationship between local <<out_messages>> buffers and the
global message buffer. One is strictly stronger: we can prove global from local,
but not vice versa: *)
Lemma prepare_stage_in_view_means_prepare_stage_in_view_global :
  forall tr i n b p,
    protocol_trace tr ->
    In n participants -> 
    prepare_stage_in_view (fst (tr i) n) p b ->
    prepare_stage_in_view_global tr i b p.
Proof.
  intros tr i n b p H_prot H_part H_local.
  destruct H_local as [H_vote | H_qc]. 
  - left.
    unfold vote_quorum_in_view in H_vote.
    red.
    unfold quorum in *.
    apply quorum_subset with (processed_PrepareVote_in_view_about_block
                   (fst (tr i) n) p b).
    assumption. 
    intros msg0 H_in0.
    apply filter_In in H_in0.
    destruct H_in0 as [H_in0 H_rest0].
    apply filter_In. split.
    apply processed_means_sent_global with n; try assumption.
    tauto. 
  - right.
    destruct H_qc as [msg [H_in H_rest]].
    exists msg; split.
    apply processed_means_sent_global with n; try assumption.
    tauto.
Qed.

Lemma prepare_stage_means_prepare_stage_global :
  forall tr i n b,
    protocol_trace tr ->
    In n participants -> 
    prepare_stage (fst (tr i) n) b ->
    prepare_stage_global tr i b.
Proof.
  intros tr i n b H_prot H_part H_local.
  destruct H_local as [v' [H_past [H_vote | H_qc]]];
  exists v'.
  - left.
    unfold vote_quorum_in_view in H_vote.
    red.
    unfold quorum in *.
    apply quorum_subset with (processed_PrepareVote_in_view_about_block
                   (fst (tr i) n) v' b).
    assumption. 
    intros msg0 H_in0.
    apply filter_In in H_in0.
    destruct H_in0 as [H_in0 H_rest0].
    apply filter_In. split.
    apply processed_means_sent_global with n; try assumption.
    tauto. 
  - right.
    destruct H_qc as [msg [H_in H_rest]].
    exists msg; split.
    apply processed_means_sent_global with n; try assumption.
    tauto.
Qed.

(** ** Precommit stage height injectivity statement *)

(** We are now ready to state the second safety property. *)

(** The second safety property states that no two same height blocks can be at
precommit stage, i.e., precommit stage block height is injective. The second safety
property does not require that the two blocks reach precommit stage in the same view. *)

(** More formally, in any global state i in a valid protocol trace tr that begins
with the initial state and respects the protocol transition rules, if there are
two participating nodes n and m, and two blocks b1 b2, such that b1 and b2 have
the same height, and are both in precommit stage in n and m's local state respectively,
but are not equal, then we can prove a contradiction. *)

Definition precommit_stage_height_injective_statement :=
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node) (b1 b2 : block),
      In n participants ->
      In m participants ->
      b1 <> b2 -> 
      precommit_stage tr i n b1 ->
      precommit_stage tr i m b2 -> 
      b_height b1 = b_height b2 ->
      False.

(** In order to gain a better understanding of the case analysis required of
this proof, we show the following fact: *)
Lemma precommit_stage_means_prepare_stage_global :
  forall tr i n b,
    protocol_trace tr ->
    In n participants -> 
    precommit_stage tr i n b ->
    exists b_child,
      parent_of b_child = b /\
      exists v v',
        prepare_stage_in_view_global tr i b v /\
        prepare_stage_in_view_global tr i b_child v'. 
Proof.
  intros tr i n b H_prot H_part H_precommit.
  destruct H_precommit as [b_child [H_parent [H_prepare H_prepare_child]]].
  exists b_child. split. assumption.
  destruct H_prepare as [v [H_past H_prepare]].
  destruct H_prepare_child as [v' [H_past_child H_prepare_child]].
  exists v, v'. split.
  now apply prepare_stage_in_view_means_prepare_stage_in_view_global with n.
  now apply prepare_stage_in_view_means_prepare_stage_in_view_global with n.
Qed.

(** From the lemma above, we know that we have at least four views:
let v1, v1' be the views during which b1 and b1's child reach global prepare stage,
and let v2, v2' be the views during which b2 and b2's child reach global prepare stage.
The first layer of case analysis proceeds on v1 and v2: 
- In the case that v1 = v2, we have already proven this in the process of 
  proving <<prepare_stage_same_view_height_injective_statement>>.
- In the case that v1 <> v2, we have two symmetric cases. Without loss of generality,
  suppose v1 < v2. Globally, a child block must reach prepare stage after its parent
  block, i.e. v1 <= v1'. By further case analysis on v1' and v2':
  - In the case that v1 = v1', either
    - v2 = v2', or
    - v2 < v2'.
  - In the case that v1 < v1', either
    - v1 < v2 <= v2' < v1', or
    - v1 < v1' < v2 <= v2', or
    - v1 < v2 < v1' < v2'. *)

(** It comes as no surprise that some of these cases are vacuous according to
the protocol. It should also be evidence that the complexity of this second
safety proof towers over that of the first safety proof, by virtue of the
number of cases we must analyze based on four views. *)

(** We break down this proof into more manageable chunks by first considering
the special case in which the block and its child reach prepare stage in the
same view that is also the current view. *)
Definition precommit_stage_now (tr : GTrace) (i : nat) (n : node) (b : block) :=
  exists b_child,
    parent_of b_child = b /\
    prepare_stage_in_view (fst (tr i) n) (node_view (fst (tr i) n)) b /\
    prepare_stage_in_view (fst (tr i) n) (node_view (fst (tr i) n)) b_child.

(** We can reorganize our cases into those for which v1 = v1' and v2= v2' and
v1 < v2, and those for which this is not the case. The statement of the safety
property for the former cases is as follows, whereby v1 = v (fst (tr i) n) and
v2 = v (fst (tr i) m): *)
Definition precommit_stage_now_height_injective_statement :=
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node) (b1 b2 : block),
      In n participants ->
      In m participants ->
      node_view (fst (tr i) n) < node_view (fst (tr i) m) -> 
      b1 <> b2 -> 
      precommit_stage_now tr i n b1 ->
      precommit_stage_now tr i m b2 -> 
      b_height b1 = b_height b2 ->
      False.

(** ** Reducing the proof *)

(** We first provide intuition on the key properties of Giskard that this statement
relies on. In order to do so, we first require the following definitions of maximum
and minimum height prepare stage blocks in a given view: *)

(** Instead of defining "the highest block to reach prepare stage globally in any
view for any node" computationally, we define it propositionally and then prove
its existence: *)
Definition is_max_prepare_height_global (tr : GTrace) (i : nat) (h : nat) :=
  (exists b p, prepare_stage_in_view_global tr i b p /\ b_height b = h) /\ 
  (forall b p, prepare_stage_in_view_global tr i b p -> b_height b <= h).

Definition is_max_prepare_height_in_view_global (tr : GTrace) (i : nat) (h : nat) (p : nat) :=
  (exists b, prepare_stage_in_view_global tr i b p /\ b_height b = h) /\ 
  (forall b, prepare_stage_in_view_global tr i b p -> b_height b <= h).

Definition is_max_prepare_height_in_view (tr : GTrace) (i : nat) (n : node) (h : nat) (p : nat) :=
  In n participants /\ 
  node_view (fst (tr i) n) = p /\
  (exists b, prepare_stage_in_view (fst (tr i) n) p b /\ b_height b = h) /\
  (forall b', prepare_stage_in_view (fst (tr i) n) p b' -> b_height b' <= h).

Definition exists_max_prepare_height_in_view_global :=
  forall tr i p, protocol_trace tr ->
    (exists b, prepare_stage_in_view_global tr i b p) ->
    exists h, is_max_prepare_height_in_view_global tr i h p.
  
Lemma local_leq_global :
  forall tr i h p,
    protocol_trace tr -> 
    is_max_prepare_height_in_view_global tr i h p ->
    forall n h_local,
      is_max_prepare_height_in_view tr i n h_local p ->
      h_local <= h. 
Proof. 
  intros tr i h p H_prot H_global n h_local H_local.
  destruct (le_dec h_local h) as [H_goal | H_false].
  - assumption.
  - (* Now we prove a contradiction *)
    exfalso.
    assert (h_local > h) by lia.
    clear H_false.
    destruct H_global as [H_gprepare H_ghighest].
    destruct H_local as [H_part [H_lview [H_lprepare H_lhighest]]].
    destruct H_lprepare as [b [H_lprepare H_lheight]].
    spec H_ghighest b. spec H_ghighest.
    destruct H_lprepare as [H_left | H_right].
    left. red. red in H_left.
    apply quorum_subset with
      (processed_PrepareVote_in_view_about_block (fst (tr i) n) p b).
    assumption. intros msg H_in.
    apply filter_In in H_in.
    destruct H_in as [H_in H_typeblock].
    apply andb_prop in H_typeblock.
    destruct H_typeblock as [H_typeblock H_view].
    apply andb_prop in H_typeblock.
    destruct H_typeblock as [H_type H_block].
    apply filter_In. 
    split.
    now apply processed_means_sent_global with n. 
    repeat (apply andb_true_iff; split); assumption. 
    right.
    destruct H_right as [msg [H_in [H_view [H_block H_type]]]].
    exists msg; repeat split; try assumption. 
    now apply processed_means_sent_global with n.
    spec H_lhighest b H_lprepare. 
    lia.
Qed.

Definition is_min_prepare_height_global (tr : GTrace) (i : nat) (h : nat) :=
  (exists b p, prepare_stage_in_view_global tr i b p /\ b_height b = h) /\ 
  (forall b p, prepare_stage_in_view_global tr i b p -> b_height b >= h).

Definition is_min_prepare_height_in_view_global (tr : GTrace) (i : nat) (h : nat) (p : nat) :=
  (exists b, prepare_stage_in_view_global tr i b p /\ b_height b = h) /\ 
  (forall b, prepare_stage_in_view_global tr i b p -> b_height b >= h).

Definition is_min_prepare_height_in_view (tr : GTrace) (i : nat) (n : node) (h : nat) (p : nat) :=
  In n participants /\ 
  node_view (fst (tr i) n) = p /\
  (exists b, prepare_stage_in_view (fst (tr i) n) p b /\ b_height b = h) /\
  (forall b', prepare_stage_in_view (fst (tr i) n) p b' -> b_height b' >= h).

(** The first key property states that for every lowest prepare stage block in a view,
its parent block must be either the highest or second-highest prepare stage block of
a past view. Intuitively, this is because there are three cases of view change:
- normal view change, last and highest block reaches prepare stage, and
- abnormal view change, highest prepare block is contained in ViewChangeQC message, and
- abnormal view change, second highest prepare block is contained in ViewChangeQC message. *)

Definition prepare_stage_first_parent_highest_or_second_global :=
  forall tr i, protocol_trace tr ->
    forall b1 v1, is_min_prepare_height_in_view_global tr i (b_height b1) v1 ->
     exists v', v' <= v1 /\
      (is_max_prepare_height_in_view_global tr i (b_height (parent_of b1)) v' \/
       is_max_prepare_height_in_view_global tr i (b_height (parent_of b1) + 1) v').

(** The second key property states that prepare stage block height increases as view
increments. Intuitively, this is because new blocks are proposed on top of a block
carried over from the previous round, either through normal or abnormal view change. *)
Definition prepare_stage_height_view_morphism_global :=
  forall tr i, protocol_trace tr ->
    forall b1 b2 v1 v2,
      prepare_stage_in_view_global tr i b1 v1 ->
      prepare_stage_in_view_global tr i b2 v2 ->
      v1 <= v2 ->
      b_height b1 <= b_height b2. 

(** The third key property specializes the lemma above and states that non-last prepare
stage block height strictly increases as view increments. *)
Definition prepare_stage_height_view_morphism_global_non_last :=
  forall tr i, protocol_trace tr ->
    forall b1 b2 v1 v2,
      prepare_stage_in_view_global tr i b1 v1 ->
      prepare_stage_in_view_global tr i b2 v2 ->
      ~ last_block b1 -> 
      v1 <= v2 ->
      b_height b1 < b_height b2. 

(** Finally, a block that has a child block in prepare stage in the same view cannot
be the last block of the view. Intuitively, this is true by construction. *)
Definition prepare_stage_child_non_last :=
  forall tr i n v b, protocol_trace tr ->
    In n participants -> 
    prepare_stage_in_view (fst (tr i) n) v b ->
    (exists b_child,
      parent_of b_child = b /\
      prepare_stage_in_view (fst (tr i) n) v b_child) ->
    ~ last_block b.

(** We now show how we can use the four key properties above to prove our
desired safety result: *)
Lemma precommit_height_injective_symmetric :
  prepare_stage_first_parent_highest_or_second_global -> 
  prepare_stage_height_view_morphism_global -> 
  prepare_stage_height_view_morphism_global_non_last ->
  prepare_stage_child_non_last -> 
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node),
      In n participants ->
      In m participants ->
      forall (b1 b2 : block),
        b1 <> b2 -> 
        precommit_stage_now tr i n b1 ->
        precommit_stage_now tr i m b2 -> 
        b_height b1 = b_height b2 ->
        False.
Proof.                          
  intros H_useful1 H_useful2 H_useful3 H_useful4 tr H_prot i n m.
  intros H_part_n H_part_m b1 b2 H_neq H_precommit1 H_precommit2 H_height.
  destruct H_precommit1 as [b_child1 [H_height1 [H_prepare1 H_prepare_child1]]]. 
  destruct H_precommit2 as [b_child2 [H_height2 [H_prepare2 H_prepare_child2]]].

  remember (node_view (fst (tr i) n)) as v1;
    remember (node_view (fst (tr i) m)) as v2. 
  assert (v1 < v2 \/ v1 = v2 \/ v2 < v1) by lia. 
  destruct H as [H_lt | [H_eq | H_gt]].

  - assert (~ last_block b1).
    { spec H_useful4 tr i n v1 b1 H_prot H_part_n.
      spec H_useful4 H_prepare1.
      spec H_useful4. exists b_child1; repeat split; tauto. assumption. } 
    apply prepare_stage_in_view_means_prepare_stage_in_view_global in H_prepare1; try assumption. 
    apply prepare_stage_in_view_means_prepare_stage_in_view_global in H_prepare2; try assumption. 
    spec H_useful3 tr i H_prot b1 b2 v1 v2.
    spec H_useful3 H_prepare1 H_prepare2 H. 
    spec H_useful3. lia.
    lia.
  - subst.
    apply prepare_stage_same_view_height_injective with
     tr i n m (parent_of b_child1) (parent_of b_child2) (node_view (fst (tr i) m)); try assumption.
    rewrite H_eq in H_prepare1.  assumption.
  - assert (~ last_block b2).
    { spec H_useful4 tr i m v2 b2 H_prot H_part_m.
      spec H_useful4 H_prepare2.
      spec H_useful4. exists b_child2; repeat split; tauto. assumption. }  
    apply prepare_stage_in_view_means_prepare_stage_in_view_global in H_prepare1; try assumption. 
    apply prepare_stage_in_view_means_prepare_stage_in_view_global in H_prepare2; try assumption. 
    spec H_useful3 tr i H_prot b2 b1 v2 v1.
    spec H_useful3 H_prepare2 H_prepare1 H. 
    spec H_useful3. lia.
    lia.
Qed.

(** Now that we have walked through one possible and relatively intuitive proof by
identifying and assuming certain key lemmas, we proceed to break down the proof
piecewise. We start by proving facts about view changes - a feature that is absent
from the first safety proof, which only deals with behaviors within the same view. *)

(** Based on Giskard's view change process, we know that a view change is triggered either
normally or abnormally. In the normal case, the last block of the previous view must have
reached prepare stage, as evidenced by the existence of a PrepareQC message for it in
the global message buffer. *)
Definition normal_trigger_message_global (tr : GTrace) (i : nat) (p : nat) (msg : message) :=
  (* In the normal view change case *) 
  (get_message_type msg = PrepareQC /\
   get_view msg = p /\
   b_last (get_block msg) = true /\
   In msg (snd (tr i))).

(** In the abnormal case, there must be a ViewChangeQC message in the global message buffer. *) 
Definition timeout_trigger_message_global (tr : GTrace) (i : nat) (p : nat) (msg : message) :=
  (* In the timeout view change case *)
  (get_message_type msg = ViewChangeQC /\
   get_view msg = p /\
   In msg (snd (tr i))).

Definition timeout_trigger_message_global_dec : forall (tr : GTrace) (i : nat) (p : nat) (msg : message),
  { timeout_trigger_message_global tr i p msg} + { ~ timeout_trigger_message_global tr i p msg }.
Proof.
intros.
case (message_type_eq_dec (get_message_type msg) ViewChangeQC); intros.
- case (Nat.eq_dec (get_view msg) p); intros.
  * case (In_dec message_eq_dec msg (snd (tr i))); intros.
    + left.
      split; [assumption|].
      split; [assumption|].
      assumption.
    + right.
      intro.
      destruct H.
      destruct H0.
      auto.
  * right.
    intro.
    destruct H.
    destruct H0.
    congruence.
- right.
  intro.
  destruct H.
  congruence.
Defined.

Definition trigger_message_global (tr : GTrace) (i : nat) (p : nat) (msg : message) :=
  normal_trigger_message_global tr i p msg \/
  timeout_trigger_message_global tr i p msg. 

(** If a view change occurs locally from <<i ~> S i>> for node <<n>>, there must exist
a trigger message signed with <<i>>'s view in global state <<(S i)>>'s message buffer. *)
Lemma view_increment_exists_trigger_message_global :
  forall (tr : GTrace), protocol_trace tr ->
  forall (n : node) (i : nat), In n participants ->
   S (node_view (fst (tr i) n)) = node_view (fst (tr (S i)) n) ->
  exists msg : message,
    trigger_message_global tr (S i) (node_view (fst (tr i) n)) msg.
Proof. 
  intros tr H_prot n i H_part H_incr.
  assert (H_prot_copy := H_prot); 
    destruct H_prot as [_ H_prot];
    spec H_prot i;
    destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
  - (* In the transition case *) 
    (* Establishing that n0 = n *) 
    assert (H_useful := @view_different_tells_receiver tr i n p0 n0 msg0 lm0 H_prot_copy H_part).
    spec H_useful. 
    lia.
    spec H_useful H_step H_deliver. 
    subst. 
    destruct p0;
      assert (H_step_copy := H_step);
      destruct H_step as [H_update [H_out H_rest]];
      unfold view_valid in H_rest;
      try (rewrite H_update in H_incr;
           simpl in H_incr;
           lia);
      (* In the cases of PrepareQC last block *) 
      try (exists msg0; left; repeat split;
             try tauto; try (symmetry; tauto);
             apply global_messages_monotonic_step;
             try assumption; try tauto;
             now apply delivered_means_sent_global with n);
    (* In the case of ViewChange quorum received by the new proposer *) 
    try (exists (make_ViewChangeQC (fst (tr i) n)
     (highest_ViewChange_message (process (fst (tr i) n) msg0))); right;
     repeat split; try tauto; try (symmetry; tauto);
    rewrite H_deliver, H_out;
    simpl; tauto); 
    (* In the case of ViewChangeQC received by validators *) 
    try (exists msg0; right; repeat split;
           try tauto; try (symmetry; tauto);
           apply global_messages_monotonic_step;
           try assumption; try tauto;
           now apply delivered_means_sent_global with n). 
  - rewrite H_timeout in H_incr;
      simpl in H_incr;
      apply is_member_correct in H_part;
      rewrite H_part in H_incr;
      inversion H_incr;
      lia.
Qed.

(** Any global broadcast message buffer must contain trigger messages for all its past views,
from the view of a particular participant. *)
Lemma past_view_exists_trigger_message_global :
  forall tr,
    protocol_trace tr ->
    forall n i,
      In n participants ->
      forall v_past,
        v_past < node_view (fst (tr i) n) ->
        exists msg,
          trigger_message_global tr i v_past msg. 
Proof.   
  intros tr H_prot n i H_part v_past H_past.
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_past;
      inversion H_past.
  - assert (H_view := @view_same_or_plus_one tr i n H_prot H_part).
    destruct H_view as [H_same | H_incr].
    + (* In the case that no view change occurred from i ~> S i *)
      spec IH_prot. lia. 
      destruct IH_prot as [msg H_trigger].
      exists msg.
      destruct H_trigger as [H_normal | H_abnormal].
      left; red in H_normal; repeat split; try tauto.
      now apply global_messages_monotonic_step.
      right; red in H_abnormal; repeat split; try tauto.
      destruct H_abnormal as [_ [_ H_out]].
      now apply global_messages_monotonic_step.
    + (* In the case that a view change occurred from i ~> S i *)
      assert (v_past < node_view (fst (tr (S i)) n) - 1 \/
              v_past = node_view (fst (tr (S i)) n) - 1) by lia. 
      destruct H as [H_lt | H_eq].
      * spec IH_prot.
        lia.
        destruct IH_prot as [msg H_trigger].
        exists msg.
        destruct H_trigger as [H_normal | H_abnormal].
        left; red in H_normal; repeat split; try tauto.
        now apply global_messages_monotonic_step.
        right; red in H_abnormal; repeat split; try tauto.
        now apply global_messages_monotonic_step.
      * (* This is the tricky case *)
        assert (H_view : v_past = node_view (fst (tr i) n)) by lia. 
        clear IH_prot H_eq H_past.
        subst.
        now apply view_increment_exists_trigger_message_global. 
Qed.

(** Trigger messages that exist in global state (S i) exist in global state i as long as
the sender of the message did not make the transition from i ~> S i: *) 
Lemma trigger_message_global_backwards_persistent_verbose :
  forall (tr : GTrace), protocol_trace tr ->
  forall (i p : nat) (n : node), In n participants ->
  forall (msg : message), trigger_message_global tr (S i) p msg ->
  forall (n0 : node) (p0 : NState_transition_type) (msg0 : message) (lm0 : list message),
   In n0 participants ->
   get_transition p0 (fst (tr i) n0) msg0 (fst (tr (S i)) n0) lm0 ->
   tr (S i) = broadcast_messages (tr i) (fst (tr i) n0) (fst (tr (S i)) n0) lm0 ->
   n0 <> get_sender msg ->
   trigger_message_global tr i p msg.
Proof.  
  intros tr H_prot_copy i p n H_part msg H_trigger n0 p0 msg0 lm0 H_in0 H_step H_deliver H_neq.
  destruct H_trigger as [H_normal | H_timeout].
  - left; red in H_normal; repeat split; try tauto.
    destruct H_normal as [_ [_ [_ H_in]]].
    rewrite H_deliver in H_in.
    simpl in H_in.
    rewrite in_app_iff in H_in;
    destruct H_in as [H_false | H_goal]; try assumption.
    assert (H_useful := delivered_means_sender_made_transition). 
    spec H_useful tr H_prot_copy i msg n0 lm0 H_false H_in0.
    spec H_useful p0 msg0 H_step H_deliver.
    symmetry in H_useful. contradiction.
  - right; red in H_timeout; repeat split; try tauto. 
    destruct H_timeout as [_ [_ H_in]].
    rewrite H_deliver in H_in.
    simpl in H_in.
    rewrite in_app_iff in H_in;
    destruct H_in as [H_false | H_goal]; try assumption.
    assert (H_useful := delivered_means_sender_made_transition). 
    spec H_useful tr H_prot_copy i msg n0 lm0 H_false H_in0.
    spec H_useful p0 msg0 H_step H_deliver.
    symmetry in H_useful. contradiction.
Qed.

(** Finally, an important property of trigger messages is that their blocks are in
global prepare stage in the current view. In the normal trigger message case, this
is direct by definition: PrepareQC suffices to enter a block into prepare stage.
In the abnormal trigger message case, we require a few supplementary facts: *)

(** The block contained in ViewChange messages is at global prepare stage: *)
Lemma ViewChange_message_block_prepare_stage_global :
  forall (tr : GTrace) (i p : nat) (msg : message),
    protocol_trace tr ->
    get_message_type msg = ViewChange /\ get_view msg = p /\ In msg (snd (tr i)) ->
    prepare_stage_in_view_global tr i (get_block msg) p.
Proof.
  intros tr i p msg H_prot H_abnormal.
  destruct H_abnormal as [H_type [H_view H_in]]. 
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      easy.
  - destruct (In_dec message_eq_dec msg (snd (tr i))) as [H_old | H_new].
    + apply prepare_stage_in_view_step_global; tauto.
    + clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * rewrite H_deliver in H_in;
          simpl in H_in;
          destruct p0;
          destruct H_step as [H_update [H_out H_rest]];
          rewrite H_out in H_in;
          simpl in H_in;
          try rewrite in_app_iff in H_in;
          repeat destruct H_in as [H_in | H_in];
          try contradiction;
          try (rewrite <- H_in in H_type;
               simpl in H_type;
               discriminate);
          try (apply pending_PrepareVote_correct in H_in;
               rewrite H_type in H_in;
               easy);
          try (subst; rewrite H_type in H_rest; easy). 
      * rewrite H_timeout in H_in. 
        simpl in H_in.
        contradiction.
Qed.
  
(** The block contained in timeout trigger messages is at global prepare stage: *) 
Lemma timeout_trigger_message_block_prepare_stage_global :
  forall (tr : GTrace) (i p : nat) (msg : message),
  protocol_trace tr ->
  get_message_type msg = ViewChangeQC /\ get_view msg = p /\ In msg (snd (tr i)) ->
  prepare_stage_in_view_global tr i (get_block msg) p.
Proof. 
  intros tr i p msg H_prot H_abnormal.
  destruct H_abnormal as [H_type [H_view H_in]]. 
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      easy.
  - destruct (In_dec message_eq_dec msg (snd (tr i))) as [H_old | H_new].
    + apply prepare_stage_in_view_step_global; tauto.
    + clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * rewrite H_deliver in H_in;
          simpl in H_in;
          destruct p0;
          assert (H_step_copy := H_step); 
          destruct H_step as [H_update [H_out H_rest]];
          rewrite H_out in H_in;
          simpl in H_in;
          try rewrite in_app_iff in H_in;
          repeat destruct H_in as [H_in | H_in];
          try contradiction;
          try (rewrite <- H_in in H_type;
               simpl in H_type;
               discriminate);
          try (apply pending_PrepareVote_correct in H_in;
               rewrite H_type in H_in;
               easy);
          try (subst; rewrite H_type in H_rest; easy).
        (* In the ViewChange quorum case *)
        assert (H_useful := ViewChange_message_block_prepare_stage_global).
        spec H_useful tr (S i) p (highest_ViewChange_message (process (fst (tr i) n0) msg0)) H_prot_copy.
        spec H_useful; repeat split.
        (* Discharging the message type obligation *)
        apply highest_ViewChange_message_type_eq_ViewChange. 
        (* Discharging the view obligation *)
        assert (H_goal := get_view_highest_ViewChange_message_node_view).
        spec H_goal (process (fst (tr i) n0) msg0).
        spec H_goal msg0. spec H_goal.
        tauto. spec H_goal. simpl.
        unfold view_valid in H_rest.
        lia.
        spec H_goal. simpl. tauto.
        rewrite H_goal.
        rewrite <- H_view.
        rewrite <- H_in.
        simpl. reflexivity.
        (* Discharging the membership obligation *)
        assert (H_goal := get_view_highest_ViewChange_message_in_counting_messages). 
        spec H_goal (process (fst (tr i) n0) msg0) msg0.
        spec H_goal. tauto.
        spec H_goal. simpl.
        unfold view_valid in H_rest.
        lia.
        spec H_goal. simpl. tauto.
        apply processed_means_sent_global with n0; try assumption.
        rewrite H_update. simpl.
        right. simpl in H_goal.
        assumption.
        rewrite <- H_in.
        simpl. assumption. 
      * rewrite H_timeout in H_in; contradiction.
Qed.

(** The block contained in trigger messages is at global prepare stage: *) 
Lemma trigger_message_block_prepare_stage_global : 
  forall tr i p msg,
    protocol_trace tr ->
    trigger_message_global tr i p msg ->
    prepare_stage_in_view_global tr i (get_block msg) p. 
Proof.
  intros tr i p msg H_prot H_trigger.
  destruct H_trigger as [H_normal | H_abnormal].
  right; red in H_normal.  
  exists msg; repeat split; try tauto.
  now apply timeout_trigger_message_block_prepare_stage_global. 
Qed.

(** These global trigger messages are significant because the blocks contained in serve as:
- strict lower bounds for prepare stage blocks in the next view, and
- non-strict upper bounds for prepare stage blocks in the current view.
*)

(** We establish these two useful qualities about global trigger message blocks in turn. *) 

(** ** Global trigger message blocks as lower bounds *)

(** First, we show that the height of the block contained in the trigger message
for a view is the lowest height of all blocks that reach prepare stage in the next view. *)

(** More formally, we wish to establish the following: *)
Definition past_view_trigger_message_lowest_block_global_statement :=
  forall tr i n p msg,
    protocol_trace tr ->
    In n participants ->
    trigger_message_global tr i p msg ->
    forall b,
      prepare_stage_in_view_global tr i b (S p) ->
      b_height b > b_height (get_block msg). 

(** We prove this by showing that the trigger message for a view carries the piggyback
block for all PrepareBlock messages sent in the next view. Because the height of
piggyback block in any PrepareBlock message is lower than the height of the proposed
block, and all prepare stage blocks must have a PrepareBlock message, the trigger message
block must be lower than the proposed block/prepare stage block. The proof of the statement
above therefore requires the following ingredients:
- all blocks that reach prepare stage in some view must have a PrepareBlock message
  in the global message buffer in that view, and
- the piggyback block of PrepareBlock messages in some view is equal to the trigger
  message block from the previous view, and
- all PrepareBlock messages have a lower piggyback block than proposed block. *)

(** *** Ingredient one: All blocks that reach prepare stage in some view must have a PrepareBlock message in the global message buffer in that view. *)

(** We prove the first ingredient by case analysis on blocks being in prepare stage in some
view: we must prove the existence of a global PrepareBlock message from the existence of a
global PrepareVote and PrepareQC message respectively. *)
Lemma prepare_means_PrepareVote_PrepareQC_exists_global : 
  forall tr i, protocol_trace tr ->
    forall (b : block) (x : nat), prepare_stage_in_view_global tr i b x ->
      exists (msg1 : message),
        In msg1 (snd (tr i)) /\
        get_view msg1 = x /\
        get_block msg1 = b /\ 
        (get_message_type msg1 = PrepareVote \/
         get_message_type msg1 = PrepareQC).
Proof.
  intros tr i H_prot b x H_prepare.
  destruct H_prepare as [H_quorum | H_qc]. 
  - apply empty_has_no_two_thirds' in H_quorum.
    destruct H_quorum as [n H_in].
    apply in_map_iff in H_in.
    destruct H_in as [msg [H_sender H_in]].
    apply filter_In in H_in. 
    destruct H_in as [H_in H_typeblockview].
    apply andb_true_iff in H_typeblockview.
    destruct H_typeblockview as [H_typeblock H_view].
    apply andb_prop in H_typeblock. 
    destruct H_typeblock as [H_type H_block].
    apply message_type_eqb_correct in H_type.
    apply Nat.eqb_eq in H_view.
    apply block_eqb_correct in H_block.
    exists msg; repeat split; try tauto.
  - destruct H_qc as [msg H_qc].
    exists msg; repeat split; try tauto.
Qed.

(** We use the above fact to break down the proof that all prepare stage blocks must have a
PrepareBlock message. Taking the left disjunct of [prepare_stage_in_view_global], we first
show that if a PrepareVote message for a block exists in the global message buffer, then a
PrepareBlock message must exist for that block in the same view. This lemma belongs to
a class of lemmas that we prove using the same proof pattern: by first showing the local
version using induction on protocol traces, and then strengthening and weakening the
premise and conclusion respectively to obtain the global version. *)
Lemma PrepareVote_sent_means_PrepareBlock_processed_local : 
  forall tr i n msg1, protocol_trace tr ->
    In n participants -> 
    In msg1 (out_messages (fst (tr i) n)) ->
    get_message_type msg1 = PrepareVote -> 
    exists (msg2 : message), 
      get_message_type msg2 = PrepareBlock /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\ 
      In msg2 (counting_messages (fst (tr i) n)).  
Proof.
  intros tr i n msg1 H_prot H_part H_sent1 H_type1.
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_sent1;
      inversion H_sent1. 
  - destruct (In_dec message_eq_dec msg1 (out_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot.
      assumption.
      destruct IH_prot as [msg2 IH_prot];
        exists msg2; repeat split; try tauto.
      now apply counting_messages_monotonic.
    + clear IH_prot. 
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the normal transition case *)
        assert (n0 = n).
        apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption.
        exists msg1; tauto. 
        subst.
        destruct p0;
          destruct H_step as [H_update [H_out H_rest]];
          rewrite H_update in H_sent1;
        try easy;
        try (apply make_PrepareBlocks_message_type in H_sent1;
         rewrite H_sent1 in H_type1;
         try destruct H_type1 as [H_type1 | H_type1]; discriminate);
        simpl in H_sent1;
        repeat destruct H_sent1 as [H_sent1 | H_sent1];
        try (rewrite <- H_sent1 in H_type1; easy);
        try (subst; rewrite H_type1 in H_rest; easy);
        try contradiction;
        (* In the three remaining cases that send PrepareVote messages, *) 
        apply in_app_iff in H_sent1;
          destruct H_sent1 as [H_sent1 | H_sent1];
          try contradiction.
        
        assert (H_sent1_copy := H_sent1). 
        apply pending_PrepareVote_correct in H_sent1_copy.
        apply in_map_iff in H_sent1.
        destruct H_sent1 as [msg' [H_eq' H_in']]. 
        apply filter_In in H_in'.
        destruct H_in' as [H_received' H_rest'].
        exists msg'; repeat split. 
        apply message_type_eqb_correct. apply andb_prop in H_rest'. tauto.
        unfold view_valid in H_rest.
        symmetry. rewrite <- H_eq'; simpl.
        replace (node_view (fst (tr i) n)) with (get_view msg0).
        apply Nat.eqb_eq. apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        tauto. symmetry; tauto.
        rewrite <- H_eq'. simpl. reflexivity.
        apply counting_messages_monotonic; try tauto.
        
        assert (H_sent1_copy := H_sent1). 
        apply pending_PrepareVote_correct in H_sent1_copy.
        apply in_map_iff in H_sent1.
        destruct H_sent1 as [msg' [H_eq' H_in']]. 
        apply filter_In in H_in'.
        destruct H_in' as [H_received' H_rest'].
        exists msg'; repeat split. 
        apply message_type_eqb_correct. apply andb_prop in H_rest'. tauto.
        unfold view_valid in H_rest.
        symmetry. rewrite <- H_eq'; simpl.
        replace (node_view (fst (tr i) n)) with (get_view msg0).
        apply Nat.eqb_eq. apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        tauto. symmetry; tauto.
        rewrite <- H_eq'. simpl. reflexivity.
        apply counting_messages_monotonic; try tauto.

        assert (H_sent1_copy := H_sent1). 
        apply pending_PrepareVote_correct in H_sent1_copy.
        apply in_map_iff in H_sent1.
        destruct H_sent1 as [msg' [H_eq' H_in']]. 
        apply filter_In in H_in'.
        destruct H_in' as [H_received' H_rest'].
        exists msg'; repeat split. 
        apply message_type_eqb_correct. apply andb_prop in H_rest'. tauto.
        unfold view_valid in H_rest.
        symmetry. rewrite <- H_eq'; simpl.
        replace (node_view (fst (tr i) n)) with (get_view msg0).
        apply Nat.eqb_eq. apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' _].
        apply andb_prop in H_rest'.
        tauto. symmetry; tauto.
        rewrite <- H_eq'. simpl. reflexivity.
        apply counting_messages_monotonic; try tauto.
        * (* In the timeout case *) 
          rewrite H_timeout in H_sent1. 
          simpl in H_sent1.
          apply is_member_correct in H_part.
          rewrite H_part in H_sent1.
          contradiction.
Qed.

Lemma PrepareVote_sent_means_PrepareBlock_sent_global : 
  forall tr i msg1, protocol_trace tr ->
    In msg1 (snd (tr i)) ->
    get_message_type msg1 = PrepareVote -> 
    exists (msg2 : message), 
      get_message_type msg2 = PrepareBlock /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\ 
      In msg2 (snd (tr i)).  
Proof.
  intros tr i msg1 H_prot H_sent1 H_type1.
  assert (H_useful := PrepareVote_sent_means_PrepareBlock_processed_local).
  spec H_useful tr i (get_sender msg1) msg1 H_prot.
  spec H_useful.
  apply participation_rights_global with tr i; try assumption.
  spec H_useful. 
  apply global_local_out_if; try assumption.
  apply participation_rights_global with tr i; try assumption.
  apply filter_In. split. assumption. apply node_eqb_correct.
  reflexivity.
  spec H_useful H_type1.
  destruct H_useful as [msg2 H_rest].
  exists msg2; repeat split; try tauto.
  apply processed_means_sent_global with (get_sender msg1); try tauto.
  apply participation_rights_global with tr i; try assumption.
Qed.

(** The right disjunct states that if a PrepareQC message for a block exists in the
global message buffer, then a PrepareBlock message must exist for that block in
the same view. *)

(** However, the proof structure here differs due to the following
statement being untrue. *)
Definition PrepareQC_sent_means_exists_PrepareBlock_processed_local :=
  forall tr i n msg1, protocol_trace tr ->
    In n participants ->
    In msg1 (out_messages (fst (tr i) n)) -> 
    get_message_type msg1 = PrepareQC -> 
    exists (msg2 : message), 
      get_message_type msg2 = PrepareBlock /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\
      In msg2 (counting_messages (fst (tr i) n)).  

(** The reason why this is untrue is in the case of sending PrepareQC messages
alongside ViewChangeQC messages - it is then no longer the case that the sender
of the PrepareQC message has personally seen a PrepareBlock for that block,
because it could have reached quorum votes independently of its participation. *)

(** Instead, we prove this by reverting back to global reasoning. *)

Lemma PrepareQC_sent_means_exists_PrepareVote_processed_local : 
  forall tr i n msg1, protocol_trace tr ->
    In n participants ->
    In msg1 (out_messages (fst (tr i) n)) -> 
    get_message_type msg1 = PrepareQC -> 
    exists (n' : node) (msg2 : message),
      In n' participants /\ 
      get_message_type msg2 = PrepareVote /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\
      In msg2 (counting_messages (fst (tr i) n')).  
Proof.
  intros tr i n msg1 H_prot H_part H_sent1 H_type1.
  generalize dependent n.
  generalize dependent msg1. 
  induction i as [|i IH_prot]; intros. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_sent1;
      inversion H_sent1. 
  - destruct (In_dec message_eq_dec msg1 (out_messages (fst (tr i) n))) as [H_old | H_new].
    + spec IH_prot msg1 H_type1 n H_part H_old. 
      destruct IH_prot as [n' [msg2 IH_prot]];
        exists n', msg2; repeat split; try tauto.
      now apply counting_messages_monotonic.
    + assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the normal transition case *)
        assert (n0 = n).
        apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption.
        exists msg1; tauto. 
        subst. 
        destruct p0;
          destruct H_step as [H_update [H_out H_rest]];
          rewrite H_update in H_sent1;
        try easy;
        try (apply make_PrepareBlocks_message_type in H_sent1;
         rewrite H_sent1 in H_type1; try destruct H_type1 as [H_type1 | H_type1];
         discriminate);
        try apply in_app_iff in H_sent1; 
        repeat destruct H_sent1 as [H_sent1 | H_sent1];
        try (rewrite <- H_sent1 in H_type1; easy);
        try (subst; rewrite H_type1 in H_rest; easy);
        try contradiction;
        try (apply pending_PrepareVote_correct in H_sent1;
             rewrite H_type1 in H_sent1; easy).

        (* In the case that PrepareQC is sent by the node itself *)
        assert (H_quorum : vote_quorum_in_view (process (fst (tr i) n) msg0)
             (get_view msg0) (get_block msg0)) by tauto. 
        red in H_quorum. unfold quorum in H_quorum.
        apply empty_has_no_two_thirds' in H_quorum.
        destruct H_quorum as [n' H_sender'].
        apply in_map_iff in H_sender'. destruct H_sender' as [msg' [H_sender' H_sent']].
        exists n, msg'. apply filter_In in H_sent'.
        destruct H_sent' as [H_sent' H_rest'].
        apply andb_prop in H_rest'.
        destruct H_rest' as [H_rest' H_view'].
        apply andb_prop in H_rest'.
        destruct H_rest' as [H_type' H_block'].
        repeat split.
        assumption.
        apply message_type_eqb_correct. assumption.
        symmetry. 
        rewrite <- H_sent1; simpl.
        unfold view_valid in H_rest.
        replace (node_view (fst (tr i) n)) with (get_view msg0) by easy.
        apply Nat.eqb_eq. assumption.
        symmetry. 
        rewrite <- H_sent1; simpl.
        apply block_eqb_correct. assumption.
        rewrite H_update. simpl. easy.

        (* In the case that the PrepareQC is aggregated and from some other node *)        
        destruct (node_eq_dec (get_sender msg0) n). 
        ** subst.
           spec IH_prot {|
            get_message_type := PrepareQC;
            get_view := get_view msg0;
            get_sender := get_sender msg0;
            get_block := get_block (highest_ViewChange_message
              (process (fst (tr i) (get_sender msg0)) msg0));
            get_piggyback_block := GenesisBlock |}.
        spec IH_prot. simpl. reflexivity.
        spec IH_prot (get_sender msg0).
        spec IH_prot. assumption.
        spec IH_prot.
        apply global_local_out_if; try assumption.
        apply filter_In. split.
        apply delivered_means_sent_global with (get_sender msg0); try assumption;
          try tauto. apply node_eqb_correct. reflexivity.
        destruct IH_prot as [n' [msg' [H_part' [H_type' [H_view' [H_block' H_processed]]]]]].
        exists n', msg'; repeat split; try tauto.
        simpl. rewrite <- H_view'. simpl.
        unfold view_valid in H_rest. tauto.
        apply counting_messages_monotonic; try assumption.
        ** spec IH_prot {|
             get_message_type := PrepareQC;
             get_view := get_view msg0;
             get_sender := get_sender msg0;
             get_block := get_block (highest_ViewChange_message (process (fst (tr i) n) msg0));
             get_piggyback_block := GenesisBlock |}. 
        spec IH_prot. simpl. reflexivity.
        spec IH_prot (get_sender msg0).
        spec IH_prot.
        (* Participation rights *)
        apply participation_rights with tr n (S i);
          try assumption.
        rewrite H_update. simpl. tauto. 
        spec IH_prot.
        apply global_local_out_if; try assumption.
        (* Participation rights *)
        apply participation_rights with tr n (S i);
          try assumption.
        rewrite H_update. simpl. tauto.  
        apply filter_In. split.
        apply delivered_means_sent_global with n; try assumption; try tauto.
        apply node_eqb_correct. simpl. reflexivity.
        destruct IH_prot as [n' [msg' [H_part' [H_type' [H_view' [H_block' H_processed]]]]]].
        exists n', msg'; repeat split; try tauto.
        rewrite <- H_view'. simpl.
        rewrite <- H_sent1. simpl.
        unfold view_valid in H_rest. tauto.
        simpl in H_block'.
        rewrite <- H_sent1. simpl.
        assumption. apply counting_messages_monotonic; try assumption.
      * rewrite H_timeout in H_sent1.
        simpl in H_sent1.
        apply is_member_correct in H_part.
        rewrite H_part in H_sent1.
        contradiction.
Qed. 

Lemma PrepareQC_sent_means_PrepareVote_sent_global : 
  forall tr i msg1,
    protocol_trace tr ->
    In msg1 (snd (tr i)) -> 
    get_message_type msg1 = PrepareQC -> 
    exists (msg2 : message), 
      get_message_type msg2 = PrepareVote /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\
      In msg2 (snd (tr i)).  
Proof.
  intros tr i msg1 H_prot H_sent1 H_type1.
  assert (H_useful := PrepareQC_sent_means_exists_PrepareVote_processed_local).
  spec H_useful tr i (get_sender msg1) msg1 H_prot.
  spec H_useful.
  apply participation_rights_global with tr i; try assumption.
  spec H_useful. 
  apply global_local_out_if; try assumption.
  apply participation_rights_global with tr i; try assumption.
  apply filter_In. split. assumption. apply node_eqb_correct.
  reflexivity.
  spec H_useful H_type1.
  destruct H_useful as [n' [msg2 H_rest]].
  exists msg2; repeat split; try tauto.
  apply processed_means_sent_global with n'; try tauto.
Qed.   
  
Lemma PrepareQC_sent_means_PrepareBlock_sent_global : 
  forall tr i msg1,
    protocol_trace tr ->
    In msg1 (snd (tr i)) -> 
    get_message_type msg1 = PrepareQC -> 
    exists (msg2 : message), 
      get_message_type msg2 = PrepareBlock /\
      get_view msg1 = get_view msg2 /\
      get_block msg1 = get_block msg2 /\
      In msg2 (snd (tr i)).  
Proof.
  intros tr i msg1 H_prot H_sent1 H_type1.
  assert (H_useful := PrepareQC_sent_means_exists_PrepareVote_processed_local).
  spec H_useful tr i (get_sender msg1) msg1 H_prot.
  spec H_useful.
  apply participation_rights_global with tr i; try assumption.
  spec H_useful. 
  apply global_local_out_if; try assumption.
  apply participation_rights_global with tr i; try assumption.
  apply filter_In. split. assumption. apply node_eqb_correct.
  reflexivity.
  spec H_useful H_type1.
  destruct H_useful as [n' [msg2 H_rest]].
  (* Now we have established that n' has sent a PrepareVote *) 
  assert (H_useful2 := PrepareVote_sent_means_PrepareBlock_sent_global).
  spec H_useful2 tr i msg2 H_prot.
  spec H_useful2.
  apply processed_means_sent_global with n'; try tauto.
  spec H_useful2. tauto.
  destruct H_useful2 as [msg0 H_about0].
  exists msg0; repeat split; try tauto.
  replace (get_view msg0) with (get_view msg2) by easy.
  tauto.
  replace (get_block msg0) with (get_block msg2) by easy.
  tauto.
Qed. 

(** We combine the four proofs above in the following global fact which concludes
our proof of the first ingredient: we have shown that any block in global prepare
stage in some view must have a PrepareBlock message in the global message buffer
in that view. *)
Lemma prepare_stage_in_view_means_PrepareBlock_sent_global : 
  forall tr i b p,
    protocol_trace tr ->
    prepare_stage_in_view_global tr i b p -> 
    exists (msg : message), 
      get_message_type msg = PrepareBlock /\
      p = get_view msg /\
      b = get_block msg /\ 
      In msg (snd (tr i)).
Proof.
  intros tr i b p H_prot H_prepare.
  apply prepare_means_PrepareVote_PrepareQC_exists_global in H_prepare; try assumption.
  destruct H_prepare as [msg1 [H_sent [H_view [H_block [H_type1 | H_type1]]]]];
  rewrite <- H_view; rewrite <- H_block.
  now apply PrepareVote_sent_means_PrepareBlock_sent_global.
  now apply PrepareQC_sent_means_PrepareBlock_sent_global.
Qed.

(** *** Ingredient two: The piggyback block of PrepareBlock messages in some view is equal to the trigger message block from the previous view. *)

(** We formalize the second ingredient as follows: *)
Definition trigger_message_next_view_PrepareBlock_same_block_global :=
  forall (tr : GTrace)
    (H_prot : protocol_trace tr)
    (i : nat)
    (msg : message)
    (v : nat),
    trigger_message_global tr i v msg ->
    forall (pb_msg : message),
      get_message_type pb_msg = PrepareBlock ->
      get_view pb_msg = S v ->
      In pb_msg (snd (tr i)) ->
      get_piggyback_block pb_msg = get_block msg. 

(** *** Ingredient three: All PrepareBlock messages have a lower piggyback block than proposed block *)

(** We show this height relation between piggyback and proposed blocks in
PrepareBlock messages directly using induction on protocol traces - it
is true by construction of PrepareBlock messages. *)
Lemma PrepareBlock_block_height_geq :
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (msg : message),
      In msg (snd (tr i)) ->
      get_message_type msg = PrepareBlock -> 
      b_height (get_piggyback_block msg) <
      b_height (get_block msg). 
Proof.
  intros tr H_prot i msg H_in H_type.
  pose proof H_prot as H_prot_copy.
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in. 
  - destruct (In_dec message_eq_dec msg (snd (tr i))) as [H_old | H_new].
    + spec IH_prot H_old. assumption.
    + clear IH_prot.
      destruct H_prot as [_ H_prot];
        spec H_prot i; 
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      destruct (node_eq_dec n0 (get_sender msg)) as [H_true | H_false].
      * subst.
        destruct p0;
          destruct H_step as [H_update [H_out H_rest]];
          rewrite H_out in H_deliver;
          rewrite H_deliver in H_in;
          simpl in H_in;
          try rewrite in_app_iff in H_in;
          repeat destruct H_in as [H_in | H_in]; 
          try contradiction;
          try (rewrite <- H_in in H_type;
               simpl in H_type;
               discriminate); 
          try (rewrite <- H_in;
               unfold get_piggyback_block, get_block;
               simpl;
               repeat rewrite about_generate_new_block;
               try rewrite GenesisBlock_height; 
               try rewrite about_generate_last_block; lia);
          try (apply pending_PrepareVote_correct in H_in;
               rewrite H_type in H_in; easy);
          try (rewrite <- H_in in H_type;
               rewrite H_type in H_rest; easy);
        try (rewrite <- H_in;
             unfold get_piggyback_block, get_block;
             simpl;
             rewrite (proj1 (about_generate_last_block
              (generate_new_block (generate_new_block (snd (fst msg0)) _) _) _));
             repeat rewrite about_generate_new_block;
             lia);
        try (rewrite <- H_in;
             unfold get_piggyback_block, get_block;
             simpl;
             rewrite (proj1 (about_generate_last_block
               (generate_new_block (generate_new_block (snd
                (fst (highest_ViewChange_message
                  (process (fst (tr i) (get_sender msg)) msg0)))) _) _) _));
             repeat rewrite about_generate_new_block;
             lia);
        try (rewrite <- H_in;
             unfold get_piggyback_block, get_block; 
             simpl;
             rewrite (proj1 (about_generate_last_block
              (generate_new_block (generate_new_block _ ))));
             repeat rewrite about_generate_new_block;
             lia).
      *  (* In the case that n0 is not the sender, contradiction *)
        rewrite H_deliver in H_in.
         simpl in H_in. rewrite in_app_iff in H_in.
         destruct H_in as [H_in | H_in];
           try contradiction.
         assert (H_useful := delivered_means_sender_made_transition).
         spec H_useful tr H_prot_copy i msg n0 lm0 H_in H_in0.
         spec H_useful p0 msg0 H_step H_deliver.
         symmetry in H_useful; easy.
      * rewrite H_timeout in H_in.
        simpl in H_in. contradiction.
Qed.

(** *** Proof of the lower bound **)

(** With the three ingredients at hand, we are ready to prove our lower bound. *) 
Lemma past_view_trigger_message_lowest_block_global :
  trigger_message_next_view_PrepareBlock_same_block_global -> 
  forall tr i n p msg, protocol_trace tr ->
    In n participants ->
    trigger_message_global tr i p msg ->
    forall b, prepare_stage_in_view_global tr i b (S p) ->
      b_height b > b_height (get_block msg). 
Proof. 
  intros H_useful2 tr i n p msg H_prot H_part H_trigger b H_prepare.
  (* Enter ingredient one: *)
  assert (H_useful1 := prepare_stage_in_view_means_PrepareBlock_sent_global). 
  spec H_useful1 tr i b (S p) H_prot H_prepare.
  destruct H_useful1 as [prepare_msg [H_type [H_view [H_block H_sent]]]].
  (* Enter ingredient two: *) 
  symmetry in H_view.
  spec H_useful2 tr H_prot i msg p H_trigger.
  spec H_useful2 prepare_msg H_type H_view H_sent. 
  rewrite <- H_useful2.
  (* Enter ingredient three: *)
  assert (H_useful3 := PrepareBlock_block_height_geq).
  spec H_useful3 tr H_prot i prepare_msg H_sent H_type.
  rewrite H_block.
  lia. 
Qed.

(** ** Global trigger message blocks as upper bounds *)

(** Second, we show that the height of the block contained in the trigger message
for a view is the highest or second highest of all blocks that reach prepare stage
in the present view. *)

(** We know that trigger messages are either PrepareQC messages for the last proposed
block, in the case of normal view change, or ViewChangeQC messages for the max height
block, in the case of abnormal view change. *)

(** Therefore, we must show this height property for each case. *)

(** The normal view change case. *)
Definition normal_trigger_message_highest_global_statement :=
  forall tr i p msg h_max, protocol_trace tr ->
    normal_trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p ->
    b_height (get_block msg) = h_max.  

(** In the abnormal view change case: *) 
Definition timeout_trigger_message_highest_or_second_highest_global_statement :=
  forall tr i p msg h_max, protocol_trace tr ->
    timeout_trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p ->
    b_height (get_block msg) = h_max \/
    b_height (get_block msg) = h_max - 1.

(** The two cases amount to the following: *)
Definition trigger_message_highest_or_second_highest_global_statement :=
  forall tr i p msg h_max, protocol_trace tr ->
    trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p ->
    b_height (get_block msg) = h_max \/
    b_height (get_block msg) = h_max - 1.

(** *** Normal view change trigger message contains the highest block *)

(** In the normal view change case, the proof is relatively straightforward. The trigger
message is a PrepareQC for the last block proposed in the view. If there exists a PrepareQC
message for that block, there must exist a PrepareBlock message for that block. By 
construction of PrepareBlock messages, the last block proposed in the view is the
highest block. Therefore, the block contained in the trigger message is the highest
prepare stage block in the view. *)

(** We first establish a connection between the block contained in the normal trigger
message and its corresponding PrepareBlock message. *)

(** Nodes cannot send messages labeled with a view greater than its current view: *) 
Lemma out_message_view_bound :
  forall tr n i, protocol_trace tr ->
    In n participants ->
    forall msg,
      In msg (out_messages (fst (tr i) n)) ->
      get_view msg <= node_view (fst (tr i) n). 
Proof.
  intros tr n i H_prot H_part msg H_sent.
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _];
      rewrite H_init in H_sent;
      inversion H_sent.
  - assert (H_view := view_same_or_plus_one i n H_prot H_part).
    destruct (In_dec message_eq_dec msg (out_messages (fst (tr i) n))) as [H_old | H_new].
    + (* In the case that the message is old *)
      spec IH_prot H_old; lia.
    + (* In the case that the message is new *)
      clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
      * (* In the normal transition case *)
        assert (n0 = n).
        { apply out_message_change_tells_sender
           with tr i p0 msg0 lm0; try assumption. exists msg; tauto. }
        subst.
        destruct p0;
          destruct H_step as [H_update H_rest];
          rewrite H_update in H_sent;
          simpl in H_sent;
          try rewrite in_app_iff in H_sent; 
          repeat destruct H_sent as [H_sent | H_sent];
          try contradiction;
          rewrite H_update; simpl; 
            try (rewrite <- H_sent;
                 unfold get_view; simpl; lia);
            assert (H_valid : view_valid (fst (tr i) n) msg0) by tauto;
            rewrite H_valid; 
            try (apply pending_PrepareVote_correct in H_sent;
                 destruct H_sent as [_ [_ H_view_msg]];
                 rewrite H_view_msg;
                 unfold view_valid in H_rest;
                 replace (get_view msg0) with (node_view (fst (tr i) n)) by easy;
                 lia);
            try (subst; lia).
      * (* In the timeout case *) 
        rewrite H_timeout in H_sent;
          simpl in H_sent; 
          apply is_member_correct in H_part;
          rewrite H_part in H_sent;
          contradiction.
Qed.

(** At the local out message buffer level, blocks tagged as last block are higher
than any other block in the same view: *)
Lemma last_block_highest_block_sent :
 forall (tr : GTrace) (n : node), In n participants ->
 forall (i p : nat) (msg : message), protocol_trace tr ->
  get_message_type msg = PrepareBlock ->
  get_view msg = p ->
  In msg (out_messages (fst (tr i) n)) ->
  b_last (get_block msg) = true ->
  forall (msg' : message), get_message_type msg' = PrepareBlock ->
  get_view msg' = p ->
  In msg' (out_messages (fst (tr i) n)) ->
  b_height (get_block msg) >= b_height (get_block msg').
Proof.
  intros tr n H_part i p msg H_prot H_type H_view H_in H_last msg' H_type' H_view' H_in'.
   induction i as [|i IH_prot]; intros. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in';
      inversion H_in'.
  - assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
    * (* In the normal transition case *)
      destruct (In_dec message_eq_dec msg (out_messages (fst (tr i) n))) as [H_old | H_new];
        destruct (In_dec message_eq_dec msg' (out_messages (fst (tr i) n))) as [H_old' | H_new'].
    + (* In case both messages are old *)
      now spec IH_prot H_old H_old'.
    + (* In case msg' is new and msg is old *)
      clear IH_prot.
      assert (n0 = n).
      { apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption. exists msg'; tauto. }
      subst.
      destruct (message_eq_dec msg msg') as [H_eq | H_neq]; try (subst; lia).
      destruct p0;
        assert (H_step_copy := H_step); 
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_update in H_in';
        simpl in H_in';
        (* In all the cases that don't send messages *) 
        try contradiction;
        (* In all the type contradiction for msg cases *)
        try rewrite in_app_iff in H_in';
        repeat destruct H_in' as [H_in' | H_in'];
        try contradiction;
        try (rewrite <- H_in' in H_type';
             discriminate);
        try (apply pending_PrepareVote_correct in H_in'; rewrite H_type' in H_in'; easy);
        try (subst; rewrite H_type' in H_rest; easy);
        try (assert (H_bound : get_view msg <= node_view (fst (tr i) n)) by 
                (apply out_message_view_bound; assumption);
             rewrite <- H_in' in H_view';
             unfold get_view in H_view' at 1; simpl in H_view';
             rewrite <- H_view' in H_bound; lia);
        (* In the initial block proposal case *)
        try (assert (H_init : fst (tr i) n = NState_init (node_id (fst (tr i) n))) by tauto;
             rewrite H_init in H_old;
             inversion H_old).
    + (* In case msg is new and msg' is old *)
            clear IH_prot.
      assert (n0 = n).
      { apply out_message_change_tells_sender
         with tr i p0 msg0 lm0; try assumption. exists msg; tauto. }
      subst.
      destruct (message_eq_dec msg msg') as [H_eq | H_neq]; try (subst; lia).
      destruct p0;
        assert (H_step_copy := H_step); 
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_update in H_in;
        simpl in H_in;
        (* In all the cases that don't send messages *) 
        try contradiction;
        (* In all the type contradiction for msg cases *)
        try rewrite in_app_iff in H_in;
        repeat destruct H_in as [H_in | H_in];
        try contradiction;
        try (rewrite <- H_in in H_type;
             discriminate);
        try (apply pending_PrepareVote_correct in H_in; rewrite H_type in H_in; easy);
        try (subst; rewrite H_type in H_rest; easy);
        try (assert (H_bound : get_view msg' <= node_view (fst (tr i) n)) by 
                (apply out_message_view_bound; assumption);
             rewrite <- H_in in H_view';
             unfold get_view in H_view' at 2; simpl in H_view';
             rewrite H_view' in H_bound; lia);
        (* In the initial block proposal case *)
        try (assert (H_init : fst (tr i) n = NState_init (node_id (fst (tr i) n))) by tauto;
             rewrite H_init in H_old';
             inversion H_old').
    + (* In case both messages are new *)
       clear IH_prot.
      assert (n0 = n).
      { apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption. exists msg'; tauto. }
      subst.
      destruct (message_eq_dec msg msg') as [H_eq | H_neq]; try (subst; lia).
      destruct p0;
        assert (H_step_copy := H_step); 
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_update in H_in;
        simpl in H_in;
        (* In all the cases that don't send messages *) 
        try contradiction;
        (* In all the type contradiction for msg cases *)
        try rewrite in_app_iff in H_in;
        repeat destruct H_in as [H_in | H_in];
          try contradiction;
          try (rewrite <- H_in in H_type;
               discriminate);
          try (apply pending_PrepareVote_correct in H_in; rewrite H_type in H_in; easy);
          try (subst; rewrite H_type in H_rest; easy);
          (* In all the non-last block for msg cases *) 
          try (rewrite <- H_in in H_last; 
               simpl in H_last;
               rewrite about_non_last_block in H_last;
               discriminate);
          (* Three remaining PrepareBlock cases *)
          rewrite H_update in H_in';
          simpl in H_in';
          (* In all the cases that don't send messages *) 
          try contradiction;
          (* In all the type contradiction for msg' cases *)
          try rewrite in_app_iff in H_in';
          repeat destruct H_in' as [H_in' | H_in'];
          try contradiction;
          try (rewrite <- H_in' in H_type';
               simpl in H_type'; 
               discriminate);
          try (apply pending_PrepareVote_correct in H_in'; rewrite H_type in H_in'; easy);
          try (subst; rewrite H_type in H_rest; easy);
          try (rewrite H_in' in H_rest;
               rewrite H_type' in H_rest;
               easy);
          (* Finally, in the remaining cases *)
          rewrite <- H_in;
          rewrite <- H_in';
          try (simpl;
               try repeat rewrite (proj1 (about_generate_last_block _));
               try repeat rewrite (about_generate_new_block _);
               lia).
      * (* In the timeout case *)
        apply is_member_correct in H_part.
        spec IH_prot.
        rewrite H_timeout in H_in.
        simpl in H_in. 
        rewrite H_part in H_in. 
        assumption.
        spec IH_prot.
        rewrite H_timeout in H_in'.
        simpl in H_in'.
        rewrite H_part in H_in'.
        assumption. assumption.
Qed. 

(** The sender of all PrepareBlock messages in a view is the block proposer of that view: *)
Lemma PrepareBlock_sender_is_new_proposer_local :
  forall (tr : GTrace) (i p : nat) (n : node) (msg : message),
  protocol_trace tr ->
  In n participants ->
  get_message_type msg = PrepareBlock ->
  get_view msg = p ->
  In msg (out_messages (fst (tr i) n)) ->
  is_block_proposer n p.
Proof.
  intros tr i p n msg H_prot H_part H_type H_view H_in.
  induction i as [|i IH_prot]. 
  - destruct H_prot as [H_init _];
      rewrite H_init in H_in;
      inversion H_in.
  - destruct (In_dec message_eq_dec msg (out_messages (fst (tr i) n))) as [H_old | H_new].
    + now spec IH_prot H_old.
    + clear IH_prot.
      assert (H_prot_copy := H_prot); 
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
    * (* In the normal transition case *)
      assert (n0 = n).
      apply out_message_change_tells_sender with tr i p0 msg0 lm0; try assumption.
      exists msg; tauto.
      subst.
      (* Case analysis on the transition *)
      destruct p0;
        assert (H_step_copy := H_step); 
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_update in H_in;
        simpl in H_in;
        (* In all the cases that don't send messages *) 
        try contradiction;
      (* In the cases that do send messages *)
        try assert (H_view_eq : view_valid (fst (tr i) (get_sender msg)) msg0) by tauto;
        try (rewrite H_view_eq in H_rest;
             rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
             assumption);
        try apply in_app_iff in H_in; 
        try repeat destruct H_in as [H_in | H_in];
        try contradiction; 
        try (apply pending_PrepareVote_correct in H_in; rewrite H_type in H_in; easy);
        try (rewrite <- H_in in H_type;
             discriminate);
        try (subst;
             rewrite H_view in H_rest;
             rewrite (protocol_trace_state_sane H_prot_copy) in H_rest; 
             easy);
        try (rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
             destruct H_rest as [H_init H_rest];
             rewrite H_init in H_in; simpl in H_in;
             rewrite <- H_in in H_view; simpl in H_view;
             subst; tauto);
        try (destruct H_rest as [H_init H_rest];
             rewrite H_init in H_in;
             simpl in H_in;
             subst; simpl;
             rewrite (protocol_trace_state_sane H_prot_copy) in H_rest; tauto).
      apply in_app_iff in H_in;
        destruct H_in as [H_in | H_in];
        try contradiction.
      apply pending_PrepareVote_correct in H_in;
        rewrite H_type in H_in;
        easy. 
      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto. 

      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto.
      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto.
      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto.
      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto.
      rewrite <- H_in; simpl;
        rewrite (protocol_trace_state_sane H_prot_copy) in H_rest;
        tauto. 
    * rewrite H_timeout in H_in. 
      simpl in H_in. 
      apply is_member_correct in H_part. 
      rewrite H_part in H_in.
      contradiction.
Qed.

Lemma PrepareBlock_sender_is_new_proposer_global :
 forall (tr : GTrace) (i p : nat) (msg : message), protocol_trace tr ->
 get_message_type msg = PrepareBlock ->
 get_view msg = p ->
 In msg (snd (tr i)) ->
 is_block_proposer (get_sender msg) p.
Proof. 
  intros tr i p msg H_prot H_type H_view H_in.
  apply PrepareBlock_sender_is_new_proposer_local with tr i msg; try assumption.
  now apply participation_rights_global with tr i.
  apply global_local_out_if; try assumption.
  now apply participation_rights_global with tr i.
  apply filter_In.  split. assumption.
  apply node_eqb_correct; reflexivity.
Qed.

(** All PrepareBlock messages sent in the same view have the same sender. *)
Lemma PrepareBlock_sender_view_injective_global :
 forall (tr : GTrace) (i p : nat) (msg : message), protocol_trace tr ->
  get_message_type msg = PrepareBlock ->
  get_view msg = p ->
  In msg (snd (tr i)) ->
  forall (msg' : message), get_message_type msg' = PrepareBlock ->
  get_view msg' = p ->
  In msg' (snd (tr i)) ->
  get_sender msg = get_sender msg'.
Proof.
  intros tr i p msg H_prot H_type H_view H_in msg' H_type' H_view' H_in'.
  assert (H_proposer1 : is_block_proposer (get_sender msg) p) by
   now apply PrepareBlock_sender_is_new_proposer_global with tr i.
  assert (H_proposer2 : is_block_proposer (get_sender msg') p) by
   now apply PrepareBlock_sender_is_new_proposer_global with tr i.
  now apply is_new_proposer_unique with p p. 
Qed.

(** Any block labeled as the last block in a PrepareBlock message is higher
than any other block in a PrepareBlock message in the same view: *)
Lemma last_block_highest_block_global :
  forall(tr : GTrace) (i p : nat) (msg : message), protocol_trace tr ->
  get_message_type msg = PrepareBlock ->
  get_view msg = p ->
  In msg (snd (tr i)) ->
  b_last (get_block msg) = true ->
  forall (msg' : message), get_message_type msg' = PrepareBlock ->
  get_view msg' = p ->
  In msg' (snd (tr i)) ->
  b_height (get_block msg) >= b_height (get_block msg').
Proof.
  intros tr i p msg H_prot H_type H_view H_in H_last msg' H_type' H_view' H_in'.
  assert (get_sender msg = get_sender msg') by
   now apply PrepareBlock_sender_view_injective_global with tr i p.
  assert (H_part : In (get_sender msg) participants) by
   now apply participation_rights_global with tr i.
  assert (In msg (out_messages (fst (tr i) (get_sender msg)))).
  { apply global_local_out_if; try assumption.
    apply filter_In. split; try assumption.
    apply node_eqb_refl. }
  assert (In msg' (out_messages (fst (tr i) (get_sender msg')))). 
  { apply global_local_out_if; try assumption.
    now rewrite <- H.
    apply filter_In. split; try assumption.
    apply node_eqb_refl. }  
  apply last_block_highest_block_sent with tr (get_sender msg) i p; try assumption.
  now rewrite H.
Qed.

(** Finally, we use the connection made above to show our goal: *) 
Lemma normal_trigger_message_highest_global :
  forall tr i p msg h_max, protocol_trace tr ->
    normal_trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p ->
    b_height (get_block msg) = h_max.  
Proof.
  intros tr i p msg h_max H_prot H_trigger H_max.
  destruct H_trigger as [H_type [H_view [H_last H_in]]].  
  (* Obtaining the PrepareBlock message *)  
  assert (H_useful := PrepareQC_sent_means_PrepareBlock_sent_global).
  spec H_useful tr i msg H_prot H_in H_type.
  destruct H_useful as [msg' [H_type' [H_view' [H_block' H_in']]]]. 
  (* (get_block msg) is the highest in the view *) 
  assert (H_useful := last_block_highest_block_global). 
  spec H_useful tr i p msg' H_prot H_type'.
  spec H_useful. firstorder lia.
  spec H_useful H_in'.
  spec H_useful.
  rewrite <- H_block'; assumption.
  rewrite H_block'.
  (* Now the message we want to feed it is the max prepare height message *)
  destruct H_max as [H_exists H_max].
  destruct H_exists as [b [H_prepare H_height]].
  apply prepare_means_PrepareVote_PrepareQC_exists_global in H_prepare; try assumption. 
  destruct H_prepare as [msg0 [H_in0 [H_view0 [H_block0 [H_type_left | H_type_right]]]]].
  - (* In the case that the Prepare message is a PrepareVote *)
    apply PrepareVote_sent_means_PrepareBlock_sent_global
     with tr i _ in H_type_left; try assumption. 
    destruct H_type_left as [msg0_pb [H_type0_pb [H_view0_pb [H_block0_pb H_in0_pb]]]].
    spec H_useful msg0_pb H_type0_pb.
    spec H_useful. firstorder lia.
    spec H_useful H_in0_pb.
    spec H_max (get_block msg').
    spec H_max.
    right. exists msg. repeat split; try assumption.
    rewrite H_block0 in H_block0_pb.
    rewrite <- H_block0_pb in H_useful.
    lia. 
  - apply PrepareQC_sent_means_PrepareBlock_sent_global
      with tr i _ in H_type_right; try assumption.
    destruct H_type_right as [msg0_pb [H_type0_pb [H_view0_pb [H_block0_pb H_in0_pb]]]].
    spec H_useful msg0_pb H_type0_pb.
    spec H_useful. firstorder lia.
    spec H_useful H_in0_pb.
    spec H_max (get_block msg').
    spec H_max.
    right. exists msg. repeat split; try assumption.
    rewrite H_block0 in H_block0_pb.
    rewrite <- H_block0_pb in H_useful.
    lia.
Qed.

(** *** Timeout trigger message contains highest or second highest block *)

(** Next, we prove the height property for timeout trigger messages. *)

(** The proof in this case is slightly more complex. The timeout trigger message
is a ViewChangeQC message aggregated from quorum ViewChange messages, containing
the highest block computed from all the ViewChange messages. We call this block
the max height block. Let b' be the highest prepare stage block globally, meaning
that there exists at least one node n such that b' is in prepare stage locally. Let b'' be
the parent of b'. Because b' is in highest prepare stage globally, there must be at
least quorum nodes for whom b'' is in prepare stage locally. Because ViewChange messages
contain the locally highest prepare stage block, and the locally highest prepare stage
block is at least b'' for majority nodes, any quorum of ViewChange messages' max 
height block must be at least b''. *)

(** The global maximum prepare height is either the highest or second highest: *) 
Lemma is_max_prepare_height_in_view_disj_global :
  forall tr i h p, protocol_trace tr ->
    is_max_prepare_height_in_view_global tr i h p ->
    forall b, prepare_stage_in_view_global tr i b p ->
      b_height b = h \/ b_height b < h.
Proof.
  intros tr i h p H_prot H_highest b H_prepare.
  destruct (classic (is_max_prepare_height_in_view_global tr i (b_height b) p)) as [H_yes | H_no]. 
  + (* If (b_height b) is the highest *)
    left.
    destruct H_highest as [H_prepare1 H_highest1].
    destruct H_prepare1 as [b1 [H_prepare1 H_height1]].
    destruct H_yes as [H_prepare2 H_highest2].
    destruct H_prepare2 as [b2 [H_prepare2 H_height2]].
    spec H_highest1 b2 H_prepare2.
    spec H_highest2 b1 H_prepare1.
    lia.
  + (* If (b_height b) is not the highest *)
    destruct H_highest as [H_prepare1 H_highest1].
    destruct H_prepare1 as [b1 [H_prepare1 H_height1]].
    spec H_highest1 b H_prepare.
    lia.
Qed. 

(** If there exists a ViewChangeQC message in the global broadcast message buffer,
then there must exist a specific quorum of ViewChange messages broadcast globally
from which it was aggregated: *)
Lemma timeout_trigger_message_global_means_exists_ViewChange_quorum :
  forall tr i p msg, protocol_trace tr ->
    (* If msg triggered the view change from p to (S p) *) 
    timeout_trigger_message_global tr i p msg ->
    (* Then there must exist a list of ViewChange messages that are broadcast globally
       in view p, implicitly those that are processed by the new proposer *)
    exists lm,
      (forall msg, In msg lm -> In msg (filter (fun msg => Nat.eqb (get_view msg) p &&
        message_type_eqb (get_message_type msg) ViewChange) (snd (tr i)))) /\
      (* That has reached quorum *) 
      quorum lm /\
      (* That was used by the new proposer (identity irrelevant) to create the ViewChangeQC message *) 
      exists n, get_block msg = get_block (highest_message_in_list n ViewChange lm).
Proof.
  intros tr i p msg H_prot H_trigger. 
  induction i as [|i IH_prot].
  - destruct H_prot as [H_init _]. 
    red in H_trigger; rewrite H_init in H_trigger.
    simpl in H_trigger. tauto.
  - destruct (timeout_trigger_message_global_dec tr i p msg) as [H_old | H_new].
    + spec IH_prot H_old.
      destruct IH_prot as [lm [H_subset H_rest]].
      exists lm; repeat split; try tauto.
      intros msg0 H_in0. apply filter_In.
      spec H_subset msg0 H_in0. 
      apply filter_In in H_subset.
      split.
      now apply global_messages_monotonic_step; try assumption.
      tauto.
    + clear IH_prot. 
      unfold timeout_trigger_message_global in *.
      assert (~ In msg (snd (tr i))) by tauto.
      clear H_new.
      destruct H_trigger as [H_type [H_view H_in]].
      assert (H_prot_copy := H_prot);
        destruct H_prot as [_ H_prot];
        spec H_prot i;
        destruct H_prot as [[n0 [H_in0 [p0 [msg0 [lm0 [H_step H_deliver]]]]]] | H_timeout].
    * (* In the normal transition case *) 
      rewrite H_deliver in H_in.
      simpl in H_in.
      apply in_app_iff in H_in;
        destruct H_in as [H_in | H_in];
        try contradiction.
      assert (H_step_copy := H_step);
        destruct p0;
        destruct H_step as [H_update [H_out H_rest]];
        rewrite H_out in H_in;
        simpl in H_in;
        try contradiction;
        repeat destruct H_in as [H_in | H_in];
        try contradiction;
        try (rewrite <- H_in in H_type;
             simpl in H_type;
             discriminate);
        try (apply pending_PrepareVote_correct in H_in;
             rewrite H_type in H_in;
             easy).
      assert (H_quorum : view_change_quorum_in_view (process
       (fst (tr i) n0) msg0) (node_view (fst (tr i) n0))) by tauto. 
      red in H_quorum.
      exists (processed_ViewChange_in_view (process (fst (tr i) n0) msg0)
       (node_view (fst (tr i) n0))); repeat split.
      (* Proving the subset relation *)
      intros msg' H_in'.
      apply filter_In in H_in'.
      destruct H_in' as [H_in' H_rest'].
      apply filter_In. split.
      apply processed_means_sent_global with n0; try assumption.
      rewrite H_update; simpl.
      simpl in H_in'. tauto.
      apply andb_prop in H_rest'.
      destruct H_rest' as [H_type' H_view'].
      apply andb_true_intro. split.
      rewrite <- H_view.
      rewrite <- H_in. 
      simpl. assumption.
      apply message_type_eqb_correct. symmetry.
      apply message_type_eqb_correct in H_type'. assumption. assumption.
      rewrite <- H_in. simpl.
      (* highest_block property *) 
      exists n0. unfold highest_message_in_list.
      unfold highest_ViewChange_message.
      f_equal. f_equal. unfold GenesisBlock_message.
      simpl.
      rewrite (protocol_trace_state_sane H_prot_copy).
      easy. 
    * (* In the timeout case *)
      rewrite H_timeout in H_in;
        contradiction.
Qed.

(** The highest block of any quorum list of ViewChange messages is at least
maximum height minus one: *)
Definition at_least_second_highest :=
  forall tr i h p, protocol_trace tr ->
    is_max_prepare_height_in_view_global tr i h p ->
    forall (lm : list message),
      (* Subset of all ViewChange messages *) 
      (forall msg, In msg lm ->
        In msg (filter (fun msg0 : message =>
        (get_view msg0 =? p) && message_type_eqb (get_message_type msg0) ViewChange) (snd (tr i)))) ->
      (* Quorum of ViewChange messages *)
      quorum lm ->
      forall n, b_height (get_block (highest_message_in_list n ViewChange lm)) >= h - 1.

(** Establishing a relationship between the maximum prepare height and the height of the
timeout trigger message block towards the final statement below: *)
Lemma timeout_trigger_message_at_least_second_highest_global :
  at_least_second_highest -> 
  forall tr i p msg h_max, protocol_trace tr ->
    timeout_trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p -> 
    b_height (get_block msg) >= h_max - 1. 
Proof.     
  intros H_useful tr i p msg h_max H_prot H_timeout H_highest. 
  assert (H_useful2 := timeout_trigger_message_global_means_exists_ViewChange_quorum). 
  spec H_useful2 tr i p msg H_prot H_timeout.
  destruct H_useful2 as [lm [H_subset [H_quorum [n H_highest_msg]]]].
  spec H_useful tr i h_max p H_prot H_highest.
  spec H_useful lm H_subset H_quorum n.
  rewrite H_highest_msg.
  assumption.
Qed. 

(** We are now able to show that the block contained in the trigger message for
a view is either the highest block in the view, or the second highest block in the view: *)
Lemma timeout_trigger_message_highest_or_second_highest_global :
  at_least_second_highest -> 
  forall tr i p msg h_max, protocol_trace tr ->
    timeout_trigger_message_global tr i p msg ->
    is_max_prepare_height_in_view_global tr i h_max p ->
    b_height (get_block msg) = h_max \/
    b_height (get_block msg) = h_max - 1. 
Proof.
  intros H_ass tr i p msg h_max H_prot H_timeout H_max.
  assert (H_useful := is_max_prepare_height_in_view_disj_global). 
  spec H_useful tr i h_max p H_prot H_max.
  spec H_useful (get_block msg).
  spec H_useful.
  apply trigger_message_block_prepare_stage_global;
    try assumption; right; tauto. 
  destruct H_useful as [H_highest | H_second].
  - tauto.
  - (* Now we need to show that it cannot be lower than h_max - 1 *)
    (* There is another pigeonhole principle argument embedded in here *)
    assert (H_useful := timeout_trigger_message_at_least_second_highest_global).
    spec H_useful H_ass tr i p msg h_max H_prot.
    spec H_useful H_timeout H_max.
    lia.
Qed. 

(** ** Global trigger message blocks increase with view *)

(** Having established global trigger message blocks as both lower bounds and
higher bounds, the final critical fact we need to show is that the height of
trigger message blocks increases as view increases. *)
Lemma trigger_message_past_step_exists_global :
  forall tr i v msg, protocol_trace tr ->
    trigger_message_global tr i (S v) msg ->
    exists msg', trigger_message_global tr i v msg'.
Proof.   
  intros tr i v msg H_prot H_trigger.
  assert (H_useful := past_view_exists_trigger_message_global). 
  spec H_useful tr H_prot.
  red in H_trigger.
  destruct H_trigger as [H_left | H_right].
  red in H_left.
  spec H_useful (get_sender msg) i.
  spec H_useful. now apply participation_rights_global with tr i.
  spec H_useful v. spec H_useful.
  assert (H_bound := (out_message_view_bound)).
  spec H_bound tr (get_sender msg) i H_prot.
  spec H_bound.
  now apply participation_rights_global with tr i.
  spec H_bound msg.
  spec H_bound.
  apply global_local_out_if; try assumption.
  now apply participation_rights_global with tr i.
  apply filter_In. split. tauto.
  apply node_eqb_correct; reflexivity.
  destruct H_left as [H_type [H_view H_rest]].
  lia. assumption.
  red in H_right.
  spec H_useful (get_sender msg) i.
  spec H_useful. now apply participation_rights_global with tr i.
  spec H_useful v. spec H_useful.
  assert (H_bound := (out_message_view_bound)).
  spec H_bound tr (get_sender msg) i H_prot.
  spec H_bound.
  now apply participation_rights_global with tr i.
  spec H_bound msg.
  spec H_bound.
  apply global_local_out_if; try assumption.
  now apply participation_rights_global with tr i.
  apply filter_In. split. tauto.
  apply node_eqb_correct; reflexivity.
  destruct H_right as [H_type [H_view H_rest]].
  lia. assumption.
Qed.

Lemma trigger_message_past_exists_global :
  forall tr i v msg, protocol_trace tr ->
    trigger_message_global tr i v msg ->
    forall v', v' <= v ->
      exists msg', trigger_message_global tr i v' msg'. 
Proof.
  intros tr i v msg H_prot H_trigger v_past H_past.
  generalize dependent msg. 
  induction v as [|v IHv]; intros.
  - inversion H_past; subst.
    exists msg.     
    assumption.
  - assert (v_past <= v \/ v_past = S v) by lia. 
    destruct H. spec IHv H.
    assert (H_useful := trigger_message_past_step_exists_global H_prot H_trigger).
    destruct H_useful as [msg' H_trigger'].
    spec IHv msg' H_trigger'.
    assumption.
    clear IHv. subst.
    now exists msg. 
Qed.

(** The proof pattern for this lemma is typical of many induction-based
proof: we first show the property for one step, then we show it by
induction for an arbitrary number of steps. *)
Lemma trigger_message_view_morphism_step_global :
  trigger_message_next_view_PrepareBlock_same_block_global ->
  forall tr j v1 msg1 msg2, protocol_trace tr ->
    trigger_message_global tr j v1 msg1 ->
    trigger_message_global tr j (S v1) msg2 ->
    b_height (get_block msg1) <= b_height (get_block msg2). 
Proof.
  intros H_useful1 tr j v1 msg1 msg2 H_prot H_trigger1 H_trigger2.
  spec H_useful1 tr H_prot j msg1 v1.
  apply trigger_message_block_prepare_stage_global in H_trigger2; try assumption. 
  apply prepare_stage_in_view_means_PrepareBlock_sent_global in H_trigger2; try assumption. 
  destruct H_trigger2 as [pb_msg2 [H_type2 [H_view2 [H_block2 H_sent2]]]].
  symmetry in H_view2.
  spec H_useful1 H_trigger1 pb_msg2 H_type2 H_view2 H_sent2.
  rewrite <- H_useful1.
  apply Nat.lt_le_incl.
  rewrite H_block2.
  now apply PrepareBlock_block_height_geq with tr j. 
Qed.   

Lemma trigger_message_view_morphism_global :
  trigger_message_next_view_PrepareBlock_same_block_global ->
  forall tr j v1 v2 msg1 msg2, protocol_trace tr ->
    v1 < v2 ->
    trigger_message_global tr j v1 msg1 ->
    trigger_message_global tr j v2 msg2 ->
    b_height (get_block msg1) <= b_height (get_block msg2).
Proof.                                             
  intros H_ass tr j v1 v2 msg1 msg2 H_prot H_past H_trigger1 H_trigger2.
  generalize dependent msg2.
  induction v2 as [|v2 IHv2]; intros.
  - inversion H_past. 
  - assert (v1 < v2 \/ v1 = v2) by lia.
    destruct H.
    assert (H_useful := trigger_message_past_exists_global). 
    spec H_useful tr j (S v2) msg2 H_prot H_trigger2 v2. spec H_useful. lia.
    destruct H_useful as [msg2' H_trigger2'].
    spec IHv2 H msg2' H_trigger2'.
    assert (H_useful := trigger_message_view_morphism_step_global).
    spec H_useful H_ass tr j v2 msg2' msg2 H_prot H_trigger2'. spec H_useful H_trigger2. lia.
    subst. clear IHv2.
    now apply trigger_message_view_morphism_step_global with tr j v2. 
Qed. 
  
(** ** Final cases of precommit stage height injectivity *)

(** Finally, we show the case of the precommit stage height injectivity proof
when the parent and child block reach prepare stage in the same view. We extract
the two symmetric cases in which b1 and b2 reach prepare stage in v1 and v2, and v1 <> v2. *)
Lemma precommit_now_height_injective_symmetric :
  exists_max_prepare_height_in_view_global ->
  at_least_second_highest -> 
  trigger_message_next_view_PrepareBlock_same_block_global -> 
  forall (tr : GTrace), protocol_trace tr ->
    forall (i : nat) (n m : node),
      node_view (fst (tr i) n) < node_view (fst (tr i) m) - 1 -> 
      In n participants ->
      In m participants ->
      forall (b1 b2 : block),
        b1 <> b2 -> 
        precommit_stage_now tr i n b1 ->
        precommit_stage_now tr i m b2 -> 
        b_height b1 = b_height b2 ->
        False.
Proof.                          
  intros H_useful3 H_second H_ass tr H_prot i n m H_lt H_part_n.
  intros H_part_m b1 b2 H_neq H_precommit1 H_precommit2 H_height.
  destruct H_precommit1 as [b_child1 [H_height1 [H_prepare1 H_prepare_child1]]]. 
  destruct H_precommit2 as [b_child2 [H_height2 [H_prepare2 H_prepare_child2]]].  

  remember (node_view (fst (tr i) n)) as v1;
    remember (node_view (fst (tr i) m)) as v2. 
  (* b2 must be higher than the trigger message in (v2 - 1), for view change from (v2 - 1) to v2 *)   
  assert (H_useful := past_view_trigger_message_lowest_block_global).
  spec H_useful H_ass tr i m (v2 - 1).  

  (* Obtaining the trigger message in (v2 - 1) *) 
  assert (H_trigger := past_view_exists_trigger_message_global).
  spec H_trigger tr H_prot m i H_part_m (v2 - 1).
  spec H_trigger. lia.
  destruct H_trigger as [msg_v2 H_trigger_v2].
  spec H_useful msg_v2 H_prot H_part_m H_trigger_v2.
  replace (S (v2 - 1)) with v2 in H_useful by lia.
  spec H_useful b2.
  unfold prepare_stage in H_prepare2. 
  spec H_useful.
  now apply prepare_stage_in_view_means_prepare_stage_in_view_global with m. 
  (* Now we have established that b2 is higher than the trigger message for (v2 - 1) *)
  (* We want to establish that b1 is lower than the trigger message for v1 *)
  (* Obtaining the trigger message for (S v1) *)
  assert (H_trigger2 := past_view_exists_trigger_message_global).
  spec H_trigger2 tr H_prot m i H_part_m v1.
  spec H_trigger2. lia.
  destruct H_trigger2 as [msg_v1 H_trigger1].

  (* Obtaining the highest prepare height for v1 *) 
  spec H_useful3 tr i v1 H_prot.
  spec H_useful3.
  (* Showing that a global prepare stage block exists *)
  exists b1. now apply prepare_stage_in_view_means_prepare_stage_in_view_global with n.
  destruct H_useful3 as [h_max H_highest_v1]. 

  (* Now we want to say that msg_v1 <= msg_v2 *)
  assert (b_height (get_block msg_v1) <= b_height (get_block msg_v2))
   by (apply trigger_message_view_morphism_global with tr i v1 (v2-1); try assumption; lia).
  
  (* Next we want to say that b_height b1 < b_height (get_block msg_v1) *)  
  assert (H_prepare1_global : prepare_stage_in_view_global tr i b1 v1).
  { now apply prepare_stage_in_view_means_prepare_stage_in_view_global with n. } 
  assert (b_height b1 < b_height (get_block msg_v1)).
  { assert (H_disj := is_max_prepare_height_in_view_disj_global).
    spec H_disj tr i h_max v1 H_prot H_highest_v1 b1 H_prepare1_global. 

    destruct H_disj as [H_false | H_true].
    - destruct H_highest_v1 as [_ H_highest_v1].
      spec H_highest_v1 b_child1.
      spec H_highest_v1.
      now apply prepare_stage_in_view_means_prepare_stage_in_view_global with n.
      assert (b_height b_child1 = S (b_height b1)).
      { rewrite <- H_height1. symmetry; apply parent_block_height. }
      lia. 
    - destruct H_trigger1 as [H_normal1 | H_timeout1].
      + (* In the normal case *)
        assert (H_highest := normal_trigger_message_highest_global).
        spec H_highest tr i v1 msg_v1 h_max H_prot H_normal1 H_highest_v1.  
        lia.
      + (* In the timeout case *)
        assert (H_second' := timeout_trigger_message_highest_or_second_highest_global).
        spec H_second' H_second tr i v1 msg_v1 h_max H_prot H_timeout1. spec H_second' H_highest_v1.
        lia. }
  lia.
Qed. 

(** Middle case. *)
Definition precommit_now_height_injective_middle :=
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node),
      node_view (fst (tr i) n) = node_view (fst (tr i) m) - 1 -> 
      In n participants ->
      In m participants ->
      forall (b1 b2 : block),
        b1 <> b2 -> 
        precommit_stage_now tr i n b1 ->
        precommit_stage_now tr i m b2 -> 
        b_height b1 = b_height b2 ->
        False.
  
(** We use the helper lemma above to discharge two cases in the final
proof, and we use same view prepare stage height injectivity to discharge
the middle case, in which v1 = v2. *)
Lemma precommit_now_height_injective :
  exists_max_prepare_height_in_view_global ->
  at_least_second_highest -> 
  trigger_message_next_view_PrepareBlock_same_block_global -> 
  precommit_now_height_injective_middle -> 
  forall (tr : GTrace), protocol_trace tr ->
    forall (i : nat) (n m : node),
      In n participants ->
      In m participants ->
      forall (b1 b2 : block),
        b1 <> b2 -> 
        precommit_stage_now tr i n b1 ->
        precommit_stage_now tr i m b2 -> 
        b_height b1 = b_height b2 ->
        False.
Proof.                         
  intros H_max H_second H_ass H_mid tr H_prot i n m.
  intros H_part_n H_part_m b1 b2 H_neq H_precommit1 H_precommit2 H_height.
  remember (node_view (fst (tr i) n)) as v1;
    remember (node_view (fst (tr i) m)) as v2.
  assert (v1 < v2 - 1 \/ v1 = v2 - 1 \/ v1 > v2 - 1) by lia. 
  destruct H as [H_lt | [H_eq | H_gt]].
  - subst;
      now apply precommit_now_height_injective_symmetric with tr i n m b1 b2.
  - subst. red in H_mid.
    now apply H_mid with tr i n m b1 b2.
  - assert (v2 < v1 - 1 \/ v2 = v1 \/ v2 = v1 - 1) by lia.
    clear H_gt. 
    destruct H as [H_lt | [H_eq1 | H_eq2]].
    + subst.
      assert (b2 <> b1) by (apply not_eq_sym in H_neq; assumption).
      symmetry in H_height.
      now apply precommit_now_height_injective_symmetric with tr i m n b2 b1.
    + subst.
      apply prepare_stage_same_view_height_injective
       with tr i n m b1 b2 (node_view (fst (tr i) n)); try assumption.
    destruct H_precommit1 as [b_child1 [H_height1 [H_prepare1 H_prepare_child1]]].
    assumption.
    destruct H_precommit2 as [b_child2 [H_height2 [H_prepare2 H_prepare_child2]]].
    rewrite <- H_eq1. assumption.
    + subst.
      unfold precommit_now_height_injective_middle in H_mid.
      assert (b2 <> b1) by (apply not_eq_sym in H_neq; assumption).
      symmetry in H_height.
      now apply H_mid with tr i m n b2 b1.
Qed.
