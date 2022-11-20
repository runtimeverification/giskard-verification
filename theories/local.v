From Coq Require Import Arith Bool List Lia.
From Giskard Require Import structures.

Import ListNotations.

Set Implicit Arguments.

(** * Local state operations, properties, and transitions *)

(** Local state transitions capture message sending, receiving and processing
behaviors of individual nodes. Local state transitions can be defined as a
quaternary relation on:
- pre-state, 
- incoming message, 
- post-state, and
- outgoing message(s).

Valid Giskard local state transitions can be defined as a predicate on these relations. *)

(** ** Local state operations *)

(** The following section defines operations that transform the pre-state
to post-state in local state transitions. *)

(** Received messages are stored in the in buffer. *) 
Definition received (s : NState) (m : message) : Prop :=
  In m (in_messages s).

(** Sent messages are stored in the out buffer, as history.  *) 
Definition sent (s : NState) (m : message) : Prop :=
  In m (out_messages s).

Definition record (s : NState) (m : message) : NState :=
 mkNState (node_view s) (node_id s)
  (in_messages s) (counting_messages s)  (m :: out_messages s) (timeout s).

Definition record_plural (s : NState) (lm : list message) : NState :=
 mkNState (node_view s) (node_id s)
  (in_messages s) (counting_messages s)  (lm ++ out_messages s) (timeout s).

(** Broadcast messages are stored in the in buffer, awaiting processing. *) 
Definition add (s : NState) (m : message) : NState :=
 mkNState (node_view s) (node_id s)
  (m :: in_messages s) (counting_messages s)  (out_messages s) (timeout s).

Definition add_plural (s : NState) (lm : list message) : NState :=
 mkNState (node_view s) (node_id s)
  (lm ++ in_messages s) (counting_messages s) (out_messages s)  (timeout s).

(** Invalid messages are removed from the in buffer, and thus unable to be processed. *) 
Definition discard (s : NState) (m : message) : NState :=
 mkNState (node_view s) (node_id s)
  (remove message_eq_dec m (in_messages s)) (counting_messages s) (out_messages s)  (timeout s).

(** Processed messages are removed from the in buffer and added to the counting buffer. *)
Definition process (s : NState) (msg : message) : NState :=
 mkNState (node_view s) (node_id s)
  (remove message_eq_dec msg (in_messages s)) (msg :: counting_messages s) (out_messages s) (timeout s).

(** During a normal or abnormal view change, the view is incremented,
and the in message buffer and timeout flag reset. *)
Definition increment_view (s : NState) : NState :=
  mkNState (S (node_view s)) (node_id s) [] (counting_messages s) (out_messages s) false.

(** ** Local state properties *)

(** The following section defines properties that constitute pre- and post- conditions
for local state transitions. *)

(** A message has a valid view with respect to a local state when it is equal to the
local state's current view. Nodes only process "non-expired" messages sent in its current view. *)
Definition view_valid (s : NState) (msg : message) : Prop :=
  node_view s = get_view msg.

Definition view_validb (s : NState) (msg : message) : bool :=
  Nat.eqb (node_view s) (get_view msg).

(** *** Byzantine behavior *)

(** The primary form of Byzantine behavior Giskard considers is double voting:
sending two PrepareVote messages for two different blocks of the same height within the same view.
We call two messages equivocating if they evidence double voting behavior of their sender. *)
Definition equivocating_messages (s : NState) (msg1 msg2 : message) : Prop :=
  In msg1 (out_messages s) /\
  In msg2 (out_messages s) /\
  get_view msg1 = get_view msg2 /\
  get_message_type msg1 = PrepareVote /\
  get_message_type msg2 = PrepareVote /\
  get_block msg1 <> get_block msg2 /\
  b_height (get_block msg1) = b_height (get_block msg2).

(** Duplicate block checking for either:
- a PrepareVote message in the processed message buffer for a different block of the same height, or
- a PrepareVote or PrepareQC message in the sent message buffer for a different block of the same height. *)
Definition exists_same_height_block_old (s : NState) (b : block) : Prop :=
  (* Either PrepareBlock has been processed, but no vote has been cast *) 
  (exists msg, In msg (counting_messages s) /\
          get_message_type msg = PrepareBlock /\ 
          b_height b = b_height (get_block msg) /\
          b <> get_block msg)
  (* Or a PrepareVote or PrepareQC has been sent *) 
  \/
  (exists msg, In msg (out_messages s) /\
          (get_message_type msg = PrepareVote \/
           get_message_type msg = PrepareQC) /\ 
          b_height b = b_height (get_block msg) /\
          b <> get_block msg). 

Definition exists_same_height_block (s : NState) (b : block) : Prop :=
  exists msg, In msg (out_messages s) /\
         get_message_type msg = PrepareVote /\
         b_height b = b_height (get_block msg) /\
         b <> get_block msg. 

Definition exists_same_height_PrepareBlock (s : NState) (b : block) : Prop :=
  exists msg, In msg (counting_messages s) /\
         get_message_type msg = PrepareBlock /\
         b_height b = b_height (get_block msg) /\
         b <> get_block msg.

Definition same_height_block_msg (b : block) (msg : message) :=
 get_message_type msg = PrepareVote /\
 b_height b = b_height (get_block msg) /\
 b <> get_block msg.

Definition same_height_block_msg_dec (b : block) (msg : message) :
  { same_height_block_msg b msg }+{ ~ same_height_block_msg b msg }.
Proof.
destruct (message_type_eq_dec (get_message_type msg) PrepareVote).
- destruct (Nat.eq_dec (b_height b) (b_height (get_block msg))).
  * destruct (block_eq_dec b (get_block msg)).
    + right.
      intro.
      destruct H.
      destruct H0.
      congruence.
    + left.
      split; [assumption|].
      split; [assumption|].
      assumption.
  * right.
    unfold same_height_block_msg.
    intro.
    destruct H.
    destruct H0.
    congruence.
- right.
  unfold same_height_block_msg.
  simpl.
  intro.
  destruct H.
  congruence.
Defined.

Program Definition exists_same_height_block_dec (s : NState) (b : block) :
 { exists_same_height_block s b }+{~ exists_same_height_block s b} :=
match Exists_dec (same_height_block_msg b) (out_messages s) (same_height_block_msg_dec b) with
| left H_dec => left _
| right H_dec => right _
end.
Next Obligation.
clear Heq_anonymous.
apply Exists_exists in H_dec.
destruct H_dec.
destruct H.
destruct H0.
destruct H1.
exists x.
split; [assumption|].
split; [assumption|].
split; [assumption|].
assumption.
Defined.
Next Obligation.
clear Heq_anonymous.
intro.
contradict H_dec.
apply Exists_exists.
destruct H.
destruct H.
destruct H0.
destruct H1.
exists x.
split; [assumption|].
split; [assumption|].
split; [assumption|].
assumption.
Defined.

Definition exists_same_height_blockb : NState -> block -> bool :=
 fun s b => if exists_same_height_block_dec s b then true else false.

Lemma exists_same_height_block_correct : forall (s : NState) (b : block),
 exists_same_height_block s b <-> exists_same_height_blockb s b = true.
Proof.
intros; split; unfold exists_same_height_blockb;
  destruct (exists_same_height_block_dec _ _); congruence.
Qed.

(** *** Prepare stage definitions *)

(** Blocks in Giskard go through three stages: Prepare, Precommit and Commit.
The local definitions of these three stages are: 
- a block is in prepare stage in some local state s iff it has received quorum PrepareVote messages
  or a PrepareQC message in the current view or some previous view, and
- a block is in precommit stage in some local state s iff its child block is in prepare stage in s, and
- a block is in commit stage in some local state s iff its child block is in precommit stage in s. *)

(** We can parameterize the definition of a block being in prepare stage by some view. *)

(** Processed PrepareVote messages in some view about some block: *) 
Definition processed_PrepareVote_in_view_about_block (s : NState) (view : nat) (b : block) : list message :=
  filter (fun msg => message_type_eqb (get_message_type msg) PrepareVote &&
                  block_eqb (get_block msg) b &&
                  Nat.eqb (get_view msg) view)
         (counting_messages s).

Definition vote_quorum_in_view (s : NState) (view : nat) (b : block) : Prop :=
  quorum (processed_PrepareVote_in_view_about_block s view b).

Definition PrepareQC_in_view (s : NState) (view : nat) (b : block) : Prop :=
  exists msg : message,
    In msg (counting_messages s) /\ 
    get_view msg = view /\
    get_block msg = b /\
    get_message_type msg = PrepareQC.

Definition prepare_stage_in_view (s : NState) (view : nat) (b : block) : Prop :=
  vote_quorum_in_view s view b
  \/
  PrepareQC_in_view s view b. 

Definition prepare_stage_in_viewb  (s : NState) (view : nat) (b : block) : bool :=
  quorumb (processed_PrepareVote_in_view_about_block s view b) 
  ||
  existsb (fun msg => message_type_eqb (get_message_type msg) PrepareQC
                                    && Nat.eqb (get_view msg) view
                                    && block_eqb (get_block msg) b)
  (counting_messages s).

(** We use this parameterized definition to define the general version of a block being
in prepare stage: A block has reached prepare stage in some state iff it has reached prepare
stage in some view that is less than or equal to the current view. *)
Definition prepare_stage (s : NState) (b : block) :=
  exists v', v' <= node_view s /\ prepare_stage_in_view s v' b.

(** *** View change definitions *)

(** Participating nodes in Giskard vote in units of time called views. Each view has the same
fixed set of participating nodes, which consists oof one block proposer for the view, and
validators. Participating nodes take turns to be the block proposer, and the identity of
the block proposer for any given view is known to all participating nodes. A view generally
proceeds as follows: at the beginning of the view, the block proposer proposes a fixed
number of blocks, which validators vote on. If all blocks receive quorum votes, the nodes
increment their local view and wait for new block proposals in the new view. Otherwise,
a timeout occurs, and nodes exchange messages to communicate their acknowledgement of the
timeout and determine the parent block for the first block of the new view. The end of a
view for a participating node is marked by either: 
- the last block proposed by the block proposer reaching prepare stage in its local state, or 
- the receipt of a ViewChangeQC message following a timeout.

We call the former a normal view change, and the latter an abnormal view change.
Because we assume that all local clocks are synchronized, in the case of an abnormal
view change, all nodes timeout at once. However, because nodes process messages at
different speeds, blocks reach prepare stage at different speeds, and consequently,
in the case of a normal view change, nodes are not guaranteed to increment their
local view at the same time. *)

(** In the case of an abnormal view change, the timeout flag is simultaneously flipped
for all participating nodes, and each sends a ViewChange message containing their
local highest block at prepare stage. Nodes then enter a liminal stage in which only
three kinds of messages can be processed: PrepareQC, ViewChange and ViewChangeQC. *)

(** Nodes will ignore all block proposals and block votes during this stage. Upon
receiving quorum ViewChange messages, validator nodes increment their view and wait
for new blocks to be proposed. The new block proposer aggregates the max height
block from its received ViewChange messages, and uses it to produce new blocks
for the new view. *)

(** The following section contains definitions required for abnormal view changes. *)

(** Quorum ViewChange messages in some view: *)
Definition processed_ViewChange_in_view (s : NState) (view : nat) : list message :=
  filter (fun msg => message_type_eqb ViewChange (get_message_type msg) &&
                  Nat.eqb (get_view msg) view)
         (counting_messages s).

Lemma processed_ViewChange_in_view_correct :
  forall s view msg,
    In msg (processed_ViewChange_in_view s view) ->
    In msg (counting_messages s) /\ 
    get_message_type msg = ViewChange /\
    get_view msg = view.
Proof. 
  intros s view msg H_in.
  apply filter_In in H_in.
  destruct H_in as [H_in H_typeview].
  apply andb_prop in H_typeview.
  destruct H_typeview as [H_type H_view].
  repeat split; try tauto. symmetry; now apply message_type_eqb_correct.
  apply Nat.eqb_eq. assumption.
Qed.

Definition view_change_quorum_in_view (s : NState) (view : nat) : Prop :=
  quorum (processed_ViewChange_in_view s view).

(** Maximum height block from all processed ViewChange messages in view: *) 
Definition highest_ViewChange_block_in_view (s : NState) (view : nat) : block :=
  fold_right higher_block
             GenesisBlock
             (map (get_block) (processed_ViewChange_in_view s view)).

Definition highest_ViewChange_block_height_in_view (s : NState) (view : nat) : nat :=
  b_height (highest_ViewChange_block_in_view s view). 

(** The last block of each view is identifiable to each participating node:  *) 
Definition last_block (b : block) : Prop :=
  b_last b = true.

(** Because not every view is guaranteed to have a block in prepare stage,
the definition of <<highest_prepare_block_in_view>> must be able to recursively
search for the highest prepare block in all past views: *)
Fixpoint highest_prepare_block_in_view (s : NState) (view : nat) : block :=
  match view with
    | 0 => GenesisBlock
    | S view' =>
      fold_right higher_block
       (highest_prepare_block_in_view s view')
       (map get_block
         (filter (fun msg => prepare_stage_in_viewb s view (get_block msg))
          (counting_messages s)))
    end.

(** The following definition constructs the ViewChange message to be
sent by each participating node upon a timeout. *)
Definition highest_prepare_block_message (s : NState) : message :=
 mkMessage PrepareQC (node_view s) (node_id s)
  (highest_prepare_block_in_view s (node_view s)) GenesisBlock.


(** ** Message construction *)

(** In Giskard, some message types "carry" other messages: 
- PrepareBlock messages for the first block in a view carry the PrepareQC
  message of its parent block, PrepareBlock messages for non-first blocks
  carry the PrepareQC of the parent block of the first block, and
- PrepareVote messages carry the PrepareQC message of its parent block, and
- ViewChange messages carry the PrepareQC message of the highest local
  prepare stage block. *)

(** We do not model this at the type level (i.e., by having inductive message
type definitions), but rather simulate this behavior using pre- and post-conditions
in our local transitions. For example, a node only processes a PrepareBlock message
in the in message buffer if the PrepareQC message that is "piggybacked" onto has also
been received, and the transition effectively processes both of these messages in one step. *)

(** PrepareBlocks are computed from either: 
- the final PrepareVote/PrepareQC message of the previous round, or 
- the ViewChangeQC from the previous round. 

The messages in both of these cases contain the parent block for the newly proposed blocks.
Note that because blocks are proposed in sequence, only the first PrepareBlock message carries
the parent block's PrepareQC message - the remaining blocks cannot do so because their parent
blocks have not reached prepare stage yet, and therefore their PrepareQC messages cannot exist.
Therefore, all PrepareBlock messages in a view carry the same PrepareQC message: that of
the first block's parent. *)

(** Note that although all PrepareBlock messages are produced and sent together in one
single transition, this does not mean that:
- they are processed at the same time, and
- we falsely enforce the discipline that the second proposed block contains the first
  block's PrepareQC when in fact it has not reached PrepareQC. *)

Definition make_PrepareBlocks (s : NState) (previous_msg : message) : list message :=
  [(mkMessage PrepareBlock 
    (node_view s)
    (node_id s) 
    (generate_new_block (get_block previous_msg)) (* New block produced *) 
    (get_block previous_msg) (* PrepareQC of highest block from previous round *)
   )
   ;
   (mkMessage PrepareBlock
    (node_view s)
    (node_id s)
    (generate_new_block
      (generate_new_block (get_block previous_msg))) (* New block produced *) 
    (get_block previous_msg) (* PrepareQC of highest block from previous round *)
   )
   ;
   (mkMessage PrepareBlock 
    (node_view s)
    (node_id s)
    (* In particular, here we produce a block that is labeled as last block for the view *)
    (generate_last_block
      (generate_new_block
         (generate_new_block (get_block previous_msg)))) (* New block produced *) 
    (get_block previous_msg)
   )]. (* PrepareQC of highest block from previous round *)

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

(** A <<PrepareVote>> carries the <<PrepareQC>> of its parent, and can only be sent
after parent block reaches prepare stage, which means one of its inputs must be
either a <<PrepareVote>> or <<PrepareQC>>. *)

(** <<PrepareVote>>s are also computed from <<PrepareBlock>> messages,
which means another one of its inputs must be a <<PrepareBlock>> message. *)
Definition make_PrepareVote (s : NState) (quorum_msg prepareblock_msg : message) : message :=
  mkMessage PrepareVote (* message type *)
  (node_view s) (* view number *)
  (node_id s) (* node id *) 
  (get_block prepareblock_msg) (* block to vote for *) 
  (get_block quorum_msg).

(** Nodes create <<PrepareVote>> messages upon receiving <<PrepareBlock>> messages
for each block, and "wait" to send it until the parent block reaches prepare stage.
This is modeled by constructing <<PrepareVote>> messages on-demand given that:
- the parent block has just reached prepare stage, and
- a <<PrepareBlock>> message exists for the child block.
*)

(** Constructing pending PrepareVote messages for child messages with existing PrepareBlocks. *)
Definition pending_PrepareVote (s : NState) (quorum_msg : message) : list message :=
  map (fun prepare_block_msg => make_PrepareVote s quorum_msg prepare_block_msg)
      (filter (fun msg => Nat.eqb (get_view msg) (get_view quorum_msg) &&
                       negb (exists_same_height_blockb s (get_block msg)) &&
                       parent_ofb (get_block msg) (get_block quorum_msg) &&
                       message_type_eqb (get_message_type msg) PrepareBlock)
              (counting_messages s)). 

Lemma pending_PrepareVote_correct :
  forall s msg0 msg,
    In msg (pending_PrepareVote s msg0) ->
    get_message_type msg = PrepareVote /\
    get_sender msg = node_id s /\
    get_view msg = node_view s.
Proof.  
  intros. 
  unfold pending_PrepareVote in H.
  rewrite in_map_iff in H.
  destruct H as [msg' [H_type' H]].
  apply filter_In in H.
  destruct H. 
  repeat (apply andb_prop in H0;
          destruct H0). 
  rewrite Nat.eqb_eq in *.
  rewrite message_type_eqb_correct in H1.
  rewrite <- H_type'. unfold make_PrepareVote; repeat split; simpl; try tauto.
Qed.

(** PrepareQC messages carry nothing, and can only be sent after a quorum number of PrepareVotes,
which means its only input is a PrepareVote containing the relevant block. *)
Definition make_PrepareQC (s : NState) (msg : message) : message :=
  mkMessage PrepareQC 
  (node_view s)
  (node_id s)
  (get_block msg)
  GenesisBlock. 

(** ViewChange messages carry the <<PrepareQC>> message of the highest block to
reach prepare stage, and since they are triggered by timeouts, no input
message is required: *)
Definition make_ViewChange (s : NState) : message :=
  mkMessage ViewChange
  (node_view s)
  (node_id s)
  (highest_prepare_block_in_view s (node_view s))
  GenesisBlock.

(** Upon receiving quorum <<ViewChange>> messages, the block proposer for the new
view aggregates the max height block from all the <<ViewChange>> messages and
sends a <<ViewChangeQC>> containing this block, alongside a <<PrepareQC>> message
evidencing its prepare stage. *)  
Definition make_ViewChangeQC (s : NState) (highest_msg : message) : message :=
  mkMessage ViewChangeQC
  (node_view s)
  (node_id s) 
  (get_block highest_msg)
  GenesisBlock.

(** ** Local state transitions *)

(** Nodes are responsible for processing messages and updating their local state;
broadcasting outgoing messages is handled by the network. *)

(** In the following section, Giskard local state transitions are organized
according to the type of message being processed. *)

(** *** Message type-agnostic actions *) 

(** Block proposal-related definitions: *)
Definition GenesisBlock_message (s : NState) : message :=
  mkMessage ViewChangeQC
  0
  (node_id s)
  GenesisBlock
  GenesisBlock.    

Definition propose_block_init (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = record_plural s (make_PrepareBlocks s (GenesisBlock_message s)) /\
  lm = (make_PrepareBlocks s (GenesisBlock_message s)) /\ 
  s = NState_init (node_id s) /\
  honest_node (node_id s) /\ 
  is_block_proposer (node_id s) 0 /\
  timeout s = false.

(** When the timeout happens, nodes enter a liminal phase where they are only allowed
to process the following kinds of messages: 
- ViewChange from other nodes
- ViewChangeQC 
- PrepareQC *)

(** Upon timeout, nodes send a ViewChange message containing the highest block to reach
Prepare stage in its current view, and the PrepareQC message attesting to that block's Prepare stage. *)
(* It does not increment the view yet *) 
Definition process_timeout (s : NState) (msg : message) (s' : NState) (lm : list message) :=
  s' = record_plural s [make_ViewChange s; highest_prepare_block_message s] /\
  lm = [make_ViewChange s; highest_prepare_block_message s] /\
  honest_node (node_id s) /\ 
  timeout s = true.   

(** An expired message - discard and do not process. *)
Definition discard_view_invalid (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = discard s msg /\
  lm = [] /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  ~ view_valid s msg.
(* At this point it doesn't matter whether timeout has occurred or not *)

(** *** PrepareBlock message-related actions *)

(** If a same height block has been seen - discard the message: *)
Definition process_PrepareBlock_duplicate (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = discard s msg /\
  lm = [] /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareBlock /\ 
  view_valid s msg /\
  timeout s = false /\ 
  exists_same_height_PrepareBlock s (get_block msg).

(** Parent block has not reached Prepare - "add its PrepareVote to pending buffer" by simply
processing the PrepareBlock message and waiting for parent block to reach quorum: *)
Definition process_PrepareBlock_pending_vote (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = process s msg /\
  lm = [] /\
  received s msg /\
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareBlock /\ 
  view_valid s msg /\
  (* PrepareBlocks cannot be processed during timeout *) 
  timeout s = false /\ 
  ~ exists_same_height_PrepareBlock s (get_block msg) /\
  (* Parent block has not reached Prepare *)
  ~ prepare_stage s (parent_of (get_block msg)). 

(** Parent block has reached QC - send PrepareVote for the block in that message and record in out buffer: *) 
Definition process_PrepareBlock_vote (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = (* Record outgoing PrepareVote messages *)
       record_plural
         (process s msg)
         (pending_PrepareVote s msg) /\
  lm = (pending_PrepareVote s msg) /\
  received s msg /\
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareBlock /\ 
  view_valid s msg /\
  (* PrepareBlocks cannot be processed during timeout *) 
  timeout s = false /\ 
  prepare_stage s (parent_of (get_block msg)). 

(** *** PrepareVote message-related actions *)

(** Block has not reached prepare stage - wait to send PrepareVote messages for child: *) 
Definition process_PrepareVote_wait (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = process s msg /\
  lm = [] /\
  received s msg /\
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareVote /\ 
  view_valid s msg /\
  (* PrepareVotes cannot be processed during timeout *) 
  timeout s = false /\ 
  ~ prepare_stage (process s msg) (get_block msg). 

(** Block is about to reach QC - send PrepareVote messages for child block if it exists and send PrepareQC: *)
(* vote_quorum means quorum PrepareVote messages *)
Definition process_PrepareVote_vote (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = process
         (record_plural
            s
            ((make_PrepareQC s msg) :: pending_PrepareVote s msg))
         msg /\
  lm = (make_PrepareQC s msg) :: pending_PrepareVote s msg /\
  honest_node (node_id s) /\ 
  received s msg /\
  get_message_type msg = PrepareVote /\
  view_valid s msg /\
  (* PrepareVotes cannot be processed during timeout *) 
  timeout s = false /\
  ~ exists_same_height_block s (get_block msg) /\
  vote_quorum_in_view (process s msg) (get_view msg) (get_block msg). 

(** *** PrepareQC message-related actions *)

(** PrepareQC messages are considered equivalent to a quorum of PrepareVote messages. 
PrepareQC messages can be processed after timeout, so we do not require that timeout
has not occurred. *)

(** The PrepareQC message suffices to directly quorum a block, even if it has not received
enough PrepareVote messages, *)

(** Last block in view for to-be block proposer undergoing normal view change process:
- increment view, and
- propose block at height <<(S n)>>. *)

Definition process_PrepareQC_last_block_new_proposer (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  (* Increment the view; propose next block *) 
  s' = record_plural
         (* New state *)
         (increment_view (process s msg))
         (* All to-propose blocks *)
         (* The block generating function starts at the input block height plus one *)
         (make_PrepareBlocks (increment_view (process s msg)) msg) /\ 
  lm = (* Send all block proposals for the new view *)
  make_PrepareBlocks (increment_view (process s msg)) msg /\ 
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareQC /\ 
  view_valid s msg /\
  (* Here we don't need for timeout to be false because apparently we can still
    process PrepareQC messages in the timeout period *)
  last_block (get_block msg) /\
  is_block_proposer (node_id s) (S (node_view s)).

(** Last block in the view for to-be validator - increment view: *) 
(* No child blocks can exist, so we don't need to send anything *) 
Definition process_PrepareQC_last_block (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = increment_view (process s msg) /\ 
  lm = [] /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareQC /\ 
  view_valid s msg /\
  (* Here we don't need for timeout to be false because apparently
     we can still process PrepareQC messages in the timeout period *)
  last_block (get_block msg) /\
  ~ is_block_proposer (node_id s) (S (node_view s)).

(** Not-the-last block in the view - send PrepareVote messages for child block and wait: *)
Definition process_PrepareQC_non_last_block (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = process (record_plural s (pending_PrepareVote s msg)) msg /\
  lm = pending_PrepareVote s msg /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareQC /\ 
  view_valid s msg /\
  timeout s = false /\ 
  ~ last_block (get_block msg).

(** *** ViewChange message-related actions *)

(** ViewChange messages can be processed after timeout, so we do not require that timeout has not occurred. *) 

(** Process ViewChange at quorum for to-be block proposer:
- send highest PrepareQC message,
- send ViewChangeQC message,
- increment view, and
- propose new block according to highest block in all quorum ViewChange messages. *)
Definition higher_message (msg1 msg2 : message) : message :=
  if (block_eqb (get_block msg1) (higher_block (get_block msg1) (get_block msg2)))
  then msg1
  else msg2.

Definition highest_message_in_list (n : node) (t : message_type) (lm : list message) : message := 
  fold_right higher_message
             (mkMessage t
                        0
                        n
                        GenesisBlock
                        GenesisBlock)
             lm.

Lemma about_highest_message_in_list :
  forall n t lm msg,
    In msg lm ->
    b_height (get_block msg) <= b_height (get_block (highest_message_in_list n t lm)).
Proof.
induction lm; intros; [inversion H|].
destruct H.
- simpl.
  subst.
  unfold higher_message.
  case_eq (block_eqb (get_block msg) (higher_block (get_block msg) (get_block (highest_message_in_list n t lm)))); intros.
  * auto with arith.
  * unfold higher_block in H.
    revert H.
    case_eq (b_height (get_block msg) <? b_height (get_block (highest_message_in_list n t lm))).
    + intros Hlt Heq.
      apply Nat.ltb_lt in Hlt.
      auto with arith.
    + intros Hle.
      case (block_eq_dec (get_block msg) (get_block msg)); [|congruence].
      intro Heq.
      apply block_eqb_correct in Heq.
      congruence.
- simpl.
  unfold higher_message.
  case_eq (block_eqb (get_block msg) (higher_block (get_block msg) (get_block (highest_message_in_list n t lm)))); intros.
  * apply block_eqb_correct in H0.
    case_eq (block_eqb (get_block a) (higher_block (get_block a) (get_block (highest_message_in_list n t lm)))); intros.
    + apply block_eqb_correct in H1.
      apply IHlm in H.
      assert (b_height (get_block (highest_message_in_list n t lm)) <= b_height (get_block a)).
      -- rewrite H1.
         unfold higher_block.
         case_eq (b_height (get_block a) <? b_height (get_block (highest_message_in_list n t lm))); [lia|].
         intro Hlt.
         apply Nat.ltb_ge in Hlt.
         lia.
      -- lia.
    + apply IHlm.
      assumption.
  * case_eq (block_eqb (get_block a) (higher_block (get_block a) (get_block (highest_message_in_list n t lm)))); intros.
    + apply block_eqb_correct in H1.
      apply IHlm in H.
      assert (b_height (get_block (highest_message_in_list n t lm)) <= b_height (get_block a)).
      -- rewrite H1.
         unfold higher_block.
         case_eq ((b_height (get_block a) <? b_height (get_block (highest_message_in_list n t lm)))); [lia|].
         intro Hlt.
         apply Nat.ltb_ge in Hlt.
         lia.
      -- lia.
    + apply IHlm.
      assumption.
Qed.

Definition highest_ViewChange_message (s : NState) : message :=
  highest_message_in_list (node_id s) ViewChange (processed_ViewChange_in_view s (node_view s)).

Lemma highest_ViewChange_message_type_eq_ViewChange :
  forall s, get_message_type (highest_ViewChange_message s) = ViewChange.
Proof.
intro s.
unfold highest_ViewChange_message.
assert (forall msg, In msg (processed_ViewChange_in_view s (node_view s)) -> get_message_type msg = ViewChange).
  intros.
  apply processed_ViewChange_in_view_correct in H.
  destruct H.
  destruct H0.
  assumption.
revert H.
generalize (processed_ViewChange_in_view s (node_view s)).
generalize (node_id s).
induction l; [reflexivity|].
simpl.
intro Ht.
unfold higher_message.
destruct (block_eqb (get_block a) (higher_block (get_block a) (get_block (highest_message_in_list n ViewChange l)))).
- apply Ht; left; reflexivity.
- apply IHl.
  intros.
  apply Ht; right; assumption.
Qed.

Lemma get_view_highest_ViewChange_message_node_view :
  forall s msg, get_message_type msg = ViewChange ->
   get_view msg = node_view s ->
   In msg (counting_messages s) ->
   get_view (highest_ViewChange_message s) = node_view s.
Proof.
intros.
unfold highest_ViewChange_message.
assert (forall msg, In msg (processed_ViewChange_in_view s (node_view s)) -> get_view msg = (node_view s)).
  intros.
  apply processed_ViewChange_in_view_correct in H2.
  destruct H2.
  destruct H3.
  assumption.
assert (processed_ViewChange_in_view s (node_view s) <> []).
  clear H2.
  unfold processed_ViewChange_in_view.
  apply In_split in H1.
  destruct H1.
  destruct H1.
  rewrite H1.
  clear H1.
  induction x.
    simpl.
    rewrite H0.
    apply eq_sym in H.
    apply message_type_eqb_correct in H.
    rewrite H.
    rewrite Nat.eqb_refl.
    simpl.
    auto with datatypes.
  simpl.
  case (message_type_eqb ViewChange (get_message_type a) && (get_view a =? node_view s)); auto with datatypes.
clear H1 H0 H.
revert H2 H3.
generalize (processed_ViewChange_in_view s (node_view s)).
generalize (node_id s).
induction l; [congruence|].
simpl.
intros.
clear H3.
unfold higher_message.
case_eq (block_eqb (get_block a) (higher_block (get_block a) (get_block (highest_message_in_list n ViewChange l)))).
  intro.
  apply H2.
  left.
  reflexivity.
unfold higher_block.
destruct l.
- simpl.
  case_eq (b_height (get_block a) <? b_height GenesisBlock).
  * rewrite Nat.ltb_lt.
    intro Hlt.
    contradict Hlt.
    apply Nat.ltb_nlt.
    apply Nat.ltb_ge.
    apply GenesisBlock_height.
  * intros.
    case (block_eq_dec (get_block a) (get_block a)); [|congruence].
    intros; apply block_eqb_correct in e; congruence.
- simpl in *.
  intros.
  apply IHl; auto with datatypes.
Qed.

Lemma get_view_highest_ViewChange_message_in_counting_messages :
  forall s msg, get_message_type msg = ViewChange ->
   get_view msg = node_view s ->
   In msg (counting_messages s) ->
   In (highest_ViewChange_message s) (counting_messages s).
Proof.
intros.
unfold highest_ViewChange_message.
assert (forall msg, In msg (processed_ViewChange_in_view s (node_view s)) -> In msg (counting_messages s)).
  intros.
  apply processed_ViewChange_in_view_correct in H2.
  destruct H2.
  destruct H3.
  assumption.
assert (processed_ViewChange_in_view s (node_view s) <> []).
  clear H2.
  unfold processed_ViewChange_in_view.
  apply In_split in H1.
  destruct H1.
  destruct H1.
  rewrite H1.
  clear H1.
  induction x.
    simpl.
    rewrite H0.
    apply eq_sym in H.
    apply message_type_eqb_correct in H.
    rewrite H.
    rewrite Nat.eqb_refl.
    simpl.
    auto with datatypes.
  simpl.
  case (message_type_eqb ViewChange (get_message_type a) && (get_view a =? node_view s)); auto with datatypes.
clear H H0 H1.
revert H2 H3.
generalize (processed_ViewChange_in_view s (node_view s)).
generalize (node_id s).
induction l; [congruence|].
simpl.
intros.
clear H3.
unfold higher_message.
case_eq (block_eqb (get_block a) (higher_block (get_block a) (get_block (highest_message_in_list n ViewChange l)))).
  intro.
  apply H2.
  left.
  reflexivity.
unfold higher_block.
destruct l.
- simpl.
  case_eq (b_height (get_block a) <? b_height GenesisBlock).
  * rewrite Nat.ltb_lt.
    intro Hlt.
    contradict Hlt.
    apply Nat.ltb_nlt.
    apply Nat.ltb_ge.
    apply GenesisBlock_height.
  * intros.
    case (block_eq_dec (get_block a) (get_block a)); [|congruence].
    intros; apply block_eqb_correct in e; congruence.
- simpl in *.
  intros.
  apply IHl; auto with datatypes.
Qed.

Definition process_ViewChange_quorum_new_proposer
 (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = (* Record new blocks after incrementing view *)
  record_plural (increment_view (process (process s msg)
   (mkMessage PrepareQC (get_view msg) (get_sender msg)
    (get_block (highest_ViewChange_message (process s msg))) GenesisBlock)))
    (* The input has to include the current ViewChange message, just in
       case that is the one which contains the highest block *)
      ((* PrepareQC of highest block *)
        (mkMessage PrepareQC (node_view s) (node_id s)
          (get_block (highest_ViewChange_message (process s msg))) GenesisBlock) :: 
       (* ViewChangeQC containing highest block *)
       (make_ViewChangeQC s (highest_ViewChange_message (process s msg))) ::
       (* New block proposals *)
       (make_PrepareBlocks (increment_view s) (highest_ViewChange_message (process s msg)))) /\
  lm = (* Send ViewChangeQC message before incrementing view to ensure the others can process it *)
  (mkMessage PrepareQC (node_view s) (node_id s)
    (get_block (highest_ViewChange_message (process s msg))) GenesisBlock) ::
  (make_ViewChangeQC s (highest_ViewChange_message (process s msg))) ::
  (* Send PrepareBlock messages *) 
  (make_PrepareBlocks (increment_view s) (highest_ViewChange_message (process s msg))) /\
  received s msg /\
  (* This condition is necessary given ViewChange sending behavior *) 
  received s (mkMessage PrepareQC (get_view msg) (get_sender msg)
   (get_block (highest_ViewChange_message (process s msg))) GenesisBlock) /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = ViewChange /\
  view_valid s msg /\
  (* ViewChange messages can be processed during timeout *)
  (* It is important that the parameter here is (process s msg) and not simply s *)
  view_change_quorum_in_view (process s msg) (node_view s) /\
  is_block_proposer (node_id s) (S (node_view s)).

(** Process ViewChange before quorum - keep and wait for QC: *)
Definition process_ViewChange_pre_quorum (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = process s msg /\
  lm = [] /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = ViewChange /\ 
  view_valid s msg /\
  ~ view_change_quorum_in_view (process s msg) (node_view s).


(** *** ViewChangeQC message-related actions *)

(** Process highest PrepareQC message, process ViewChangeQC, then increment view. *)

(** Critically, this is where we enforce that the PrepareQC of the max height block
is processed before view change occurs, otherwise nodes can get stuck during view change. *)
Definition process_ViewChangeQC_single (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = increment_view (process (process s
    (mkMessage PrepareQC (node_view s) (get_sender msg) (get_block msg) GenesisBlock)) msg) /\
  lm = [] /\
  received s msg /\
  received s (mkMessage PrepareQC (node_view s) (get_sender msg) (get_block msg) GenesisBlock) /\
  honest_node (node_id s) /\ 
  get_message_type msg = ViewChangeQC /\ 
  view_valid s msg.

(** *** Timeout **)

(** When timeout is triggered, send ViewChange with the highest prepare stage block.
Given the new definition of prepare stage, this block might not be from the current view at all. *) 

Definition flip_timeout (s : NState) : NState :=
  mkNState (node_view s) (node_id s) (in_messages s) (counting_messages s) (out_messages s)  true.

(** *** Malicious node actions *)

(** Malicious nodes can ignore messages: *)
Definition malicious_ignore (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = discard s msg /\
  lm = [] /\
  received s msg /\
  ~ honest_node (node_id s).

(** Malicious nodes can double vote for two blocks of the same height: *)
Definition process_PrepareBlock_malicious_vote (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = record_plural (process s msg) (pending_PrepareVote s msg) /\
  lm = pending_PrepareVote s msg /\
  received s msg /\
  ~ honest_node (node_id s) /\ 
  get_message_type msg = PrepareBlock /\ 
  view_valid s msg /\
  exists_same_height_block s (get_block msg).

(** ** Protocol transition type definitions *)

(** Valid Giskard transitions can be defined as a finite set/type of relations on pre-state,
post-state, processed message and outgoing message(s), constrained by protocol rules. *)
Inductive NState_transition_type :=
| propose_block_init_type
| discard_view_invalid_type 
| process_PrepareBlock_duplicate_type
| process_PrepareBlock_pending_vote_type 
| process_PrepareBlock_vote_type
| process_PrepareVote_vote_type
| process_PrepareVote_wait_type
| process_PrepareQC_last_block_new_proposer_type
| process_PrepareQC_last_block_type
| process_PrepareQC_non_last_block_type
| process_ViewChange_quorum_new_proposer_type
| process_ViewChange_pre_quorum_type
| process_ViewChangeQC_single_type
| process_PrepareBlock_malicious_vote_type.

Definition get_transition (t : NState_transition_type) : (NState -> message -> NState -> list message -> Prop) :=
  match t with
  | propose_block_init_type => propose_block_init
  | discard_view_invalid_type => discard_view_invalid
  | process_PrepareBlock_duplicate_type => process_PrepareBlock_duplicate
  | process_PrepareBlock_pending_vote_type => process_PrepareBlock_pending_vote
  | process_PrepareBlock_vote_type => process_PrepareBlock_pending_vote
  | process_PrepareQC_last_block_new_proposer_type => process_PrepareQC_last_block_new_proposer
  | process_PrepareQC_last_block_type => process_PrepareQC_last_block
  | process_PrepareQC_non_last_block_type => process_PrepareQC_non_last_block
  | process_PrepareVote_vote_type => process_PrepareVote_vote
  | process_PrepareVote_wait_type => process_PrepareVote_wait
  | process_ViewChange_quorum_new_proposer_type => process_ViewChange_quorum_new_proposer
  | process_ViewChange_pre_quorum_type => process_ViewChange_pre_quorum
  | process_ViewChangeQC_single_type => process_ViewChangeQC_single
  | process_PrepareBlock_malicious_vote_type => process_PrepareBlock_malicious_vote
  end.

(** ** Facts about local state transitions *)

Lemma out_messages_local_monotonic :
  forall (s1 s2 : NState) (msg : message) (lm : list message) (t : NState_transition_type),
    (get_transition t) s1 msg s2 lm ->
    forall (msg0 : message),
      In msg0 (out_messages s1) ->
      In msg0 (out_messages s2). 
Proof.     
  intros s1 s2 msg lm t H_step msg0 H_in.
  assert (H_step_copy := H_step). 
  destruct t; simpl in H_step;
    destruct H_step as [H_subst _];
    try (subst; assumption);
    try (rewrite H_subst; simpl; rewrite in_app_iff; repeat right; assumption); 
    try (rewrite H_subst in *; simpl; right;
         assert (H : In msg0 (pending_messages_about_block s1 (get_block msg)) \/ In msg0 (out_messages s1)) by tauto;
          apply in_app_iff in H; assumption);
    try (destruct H_step_copy as [_ [_ [_ [H_init _]]]]; 
         rewrite H_init in H_in; inversion H_in);
    try (rewrite H_subst; simpl; try rewrite in_app_iff; repeat right; 
         assumption).
Qed. 

Lemma counting_messages_same_view_monotonic :
  forall (s1 s2 : NState) (msg : message) (lm : list message) (t : NState_transition_type),
    (get_transition t) s1 msg s2 lm ->
    node_view s1 = node_view s2 -> 
    forall (msg0 : message),
      In msg0 (counting_messages s1) ->
      In msg0 (counting_messages s2). 
Proof.     
  intros s1 s2 msg lm t H_step H_view msg0 H_in.
  destruct t; simpl in H_step;
    destruct H_step as [H_subst _];
    simpl in H_subst; 
    try (subst; assumption); 
    try rewrite H_subst in *; simpl;
      try (simpl in H_view; lia);
      try (right; assert (In msg0 (pending_messages_about_block s1 (get_block msg)) \/ In msg0 (out_messages s1)) by tauto;
           apply in_app_iff in H; assumption);
      try tauto.
Qed.

Lemma counting_messages_local_monotonic :
  forall (s1 s2 : NState) (msg : message) (lm : list message) (t : NState_transition_type),
    (get_transition t) s1 msg s2 lm ->
    forall (msg0 : message),
      In msg0 (counting_messages s1) ->
      In msg0 (counting_messages s2). 
Proof.     
  intros s1 s2 msg lm t H_step msg0 H_in.
  assert (H_step_copy := H_step). 
  destruct t; simpl in H_step;
    destruct H_step as [H_subst _];
    try (subst; assumption);
    try (rewrite H_subst; simpl; rewrite in_app_iff; repeat right; assumption); 
    try (rewrite H_subst in *; simpl; right;
         assert (H : In msg0 (pending_messages_about_block s1 (get_block msg)) \/ In msg0 (out_messages s1)) by tauto;
         apply in_app_iff in H; assumption);
    try (destruct H_step_copy as [_ [_ [_ [H_init _]]]]; 
         rewrite H_init in H_in; inversion H_in);
    try (rewrite H_subst; simpl; try rewrite in_app_iff; repeat right; 
         assumption).
Qed.

Lemma about_local_out_messages :
  forall (s1 s2 : NState) (msg : message) (lm : list message) (p : NState_transition_type),
    get_transition p s1 msg s2 lm ->
    forall (msg0 : message),
      In msg0 lm ->
      In msg0 (out_messages s2). 
Proof. 
  intros s1 s2 msg lm p H_step msg0 H_in. 
  destruct p;
    assert (H_step_copy := H_step);
    destruct H_step as [H_update [H_out _]];
    rewrite H_out in H_in;
    (* In cases where lm = [] *) 
    try (now apply in_nil in H_in);
    try (rewrite H_update; simpl;
         rewrite in_app_iff; tauto);
    try (rewrite H_update; simpl;
         inversion H_in; subst; try tauto;
         right; apply in_app_iff; tauto);
    try (rewrite H_update; 
         simpl in *;
         destruct H_in as [H_in | [H_in | [H_in | H_in]]];
         tauto). 
Qed.

Lemma not_prepare_stage :
  forall (s : NState) (b : block),
    ~ prepare_stage s b ->
    ~ vote_quorum_in_view s (node_view s) b /\
    forall (msg : message),
      In msg (counting_messages s) ->
      get_block msg = b ->
      get_view msg = (node_view s) -> 
      get_message_type msg = PrepareQC ->
      False. 
Proof.
  intros s b H_not. split.
  intros H_not2. apply H_not.
  exists (node_view s). split. lia. left. assumption.
  intros. 
  apply H_not. exists (node_view s); split; try lia. right. exists msg. tauto.
Qed. 

Lemma prepare_stage_record_agnostic :
  forall (s : NState) (b : block) (msg : message),
    prepare_stage (record s msg) b -> 
    prepare_stage s b. 
Proof.
  intros s b msg H.
  destruct H as [v' [H_past H_prepare]]. 
  exists v'. split. assumption.
  assumption. 
Qed.

Lemma prepare_stage_record_plural_agnostic :
  forall (s : NState) (b : block) (lm : list message),
    prepare_stage (record_plural s lm) b <-> 
    prepare_stage s b. 
Proof.
  intros s b msg; split; intro H.
  destruct H as [v' [H_past H_prepare]]. 
  exists v'. split. assumption.
  assumption.
  easy. 
Qed.

Lemma prepare_stage_process_record_plural_agnostic :
  forall (s : NState) (b : block) (lm : list message) (msg : message),
    prepare_stage (process (record_plural s lm) msg) b <-> 
    prepare_stage (process s msg) b. 
Proof.
  intros s b msg; split; intro H.
  destruct H as [v' [H_past H_prepare]]. 
  exists v'. split. assumption.
  assumption.
  easy.
Qed.
