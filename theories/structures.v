From Coq Require Import Arith Bool List.
From Giskard Require Import lib.

Import ListNotations.

Set Implicit Arguments.

(** * Definitions of Giskard datatypes *)

(** ** Blocks *)

(** Blocks are equipped with decidable equality, a genesis block inhabitant,
a height, a flag indicating its last block status. *)
Parameter block : Type.
Parameter GenesisBlock : block.
Parameter b_height : block -> nat.
Parameter b_index : block -> nat.

(** The genesis block has minimal height. *)
Axiom GenesisBlock_height : forall b, b_height GenesisBlock <= b_height b.

Definition b_last (b : block) : bool := (b_index b) =? 3.

Parameter block_eqb : block -> block -> bool.
Axiom block_eqb_correct : forall b1 b2, block_eqb b1 b2 = true <-> b1 = b2.

Definition block_eq_dec : forall b1 b2 : block, {b1 = b2} + {b1 <> b2}.
Proof.
intros.
case_eq (block_eqb b1 b2); intros.
- left; apply block_eqb_correct; assumption.
- right.
  intro.
  apply block_eqb_correct in H0.
  congruence.
Defined.

Parameter generate_new_block : block -> block.
Parameter generate_last_block : block -> block.
Axiom about_generate_last_block :
 forall b, b_height (generate_last_block b) = S (b_height b) /\ b_last (generate_last_block b) = true.
Axiom about_non_last_block : forall b, b_last (generate_new_block b) = false.

(** ** Parent relation *)

(** We assume a primitive parent relation on blocks. *)
Parameter parent_of : block -> block. 
Parameter parent_ofb : block -> block -> bool.
Axiom parent_ofb_correct : forall b1 b2, parent_of b1 = b2 <-> parent_ofb b1 b2 = true.
Axiom generate_new_block_parent : forall b, parent_of (generate_new_block b) = b.
Axiom parent_block_height : forall b, S (b_height (parent_of b)) = b_height b.

Lemma about_generate_new_block : forall b, b_height (generate_new_block b) = S (b_height b).
Proof.
 intros.
 rewrite <- parent_block_height.
 rewrite generate_new_block_parent.
 reflexivity.
Qed.

(** ** Nodes *)

Parameter node : Type.
Parameter node_eqb : node -> node -> bool.
Axiom node_eqb_correct : forall n1 n2, node_eqb n1 n2 = true <-> n1 = n2.

Lemma node_eqb_refl : forall n, node_eqb n n = true.
Proof. 
 intros. assert (n = n) by tauto.
 now apply node_eqb_correct in H.
Qed.

Lemma node_eqb_comm : forall n1 n2, node_eqb n1 n2 = node_eqb n2 n1.
Proof.
  intros; destruct (node_eqb n1 n2) eqn:?;
   destruct (node_eqb n2 n1) eqn:?; auto.
  - rewrite node_eqb_correct in Heqb.
    rewrite Heqb in Heqb0.
    rewrite node_eqb_refl in Heqb0; congruence.
  - rewrite node_eqb_correct in Heqb0.
    rewrite Heqb0 in Heqb.
    rewrite node_eqb_refl in Heqb; congruence.
Qed.

Lemma node_eqb_no : forall n1 n2, n1 <> n2 -> node_eqb n1 n2 = false.
Proof.
intros.
case_eq (node_eqb n1 n2); auto.
intros.
apply node_eqb_correct in H0; congruence.
Qed.  

Definition node_eq_dec : forall n1 n2 : node, {n1 = n2}+{n1 <> n2}.
Proof.
intros.
case_eq (node_eqb n1 n2); intros.
- left; apply node_eqb_correct; assumption.
- right.
  intro.
  apply node_eqb_correct in H0.
  congruence.
Defined.

(** Honest node property. *) 
Parameter honest_node : node -> Prop.
Parameter honest_nodeb : node -> bool.
Axiom honest_nodeb_correct : forall (n : node), honest_node n <-> honest_nodeb n = true.

(** ** Quorums *)

Parameter has_at_least_two_thirdsb : list node -> bool.
Definition has_at_least_two_thirds (l : list node) : Prop := has_at_least_two_thirdsb l = true.

Parameter has_at_least_one_thirdb : list node -> bool.
Definition has_at_least_one_third (l : list node) : Prop := has_at_least_one_thirdb l = true.

Axiom majority_growth : forall (l : list node),
    has_at_least_two_thirds l ->
    forall (n : node),
      has_at_least_two_thirds (n :: l).

Axiom empty_has_no_two_thirds' : forall (l : list node), has_at_least_two_thirds l -> exists n, In n l.
Theorem empty_has_no_two_thirds  : ~ has_at_least_two_thirds [].
Proof.
  intro H.
  destruct (empty_has_no_two_thirds' H).
  assumption.
Qed.
Axiom empty_has_no_one_third' : forall (l : list node), has_at_least_one_third  l -> exists n, In n l.
Theorem empty_has_no_one_third   : ~ has_at_least_one_third  [].
Proof.
  intro H.
  destruct (empty_has_no_one_third' H).
  assumption.
Qed.

Axiom minority_subset : forall (l : list node),
    has_at_least_one_third l ->
    forall (l_superset : list node),
      (forall n, In n l -> In n l_superset) ->
      has_at_least_one_third l_superset.

Lemma majority_shrink : forall (n : node) (l : list node),
 ~ has_at_least_two_thirds (n :: l) ->
 ~ has_at_least_two_thirds l.
Proof.
  intros n l H_not_in H_not_in_tl.
  apply H_not_in.
  apply majority_growth. assumption.
Qed.

Axiom intersection_property : 
    forall (l1 l2 : list node),
      has_at_least_two_thirds l1 ->
      has_at_least_two_thirds l2 ->
      exists (l : list node),
        has_at_least_one_third l /\
        forall (n : node), In n l -> In n l1 /\ In n l2.

Definition is_member : node -> list node -> bool :=
 fun n ns => if in_dec node_eq_dec n ns then true else false.
Lemma is_member_correct : forall (n : node) (ln : list node), is_member n ln = true <-> In n ln.
Proof.
 intros; split; unfold is_member; intros;
  destruct (in_dec _ _); congruence.
Qed.

(** No more than one third malicious node assumption. *)
Parameter participants : list node.
Axiom evil_participants : ~ has_at_least_one_third (filter (fun n => negb (honest_nodeb n)) participants).

(** ** Messages *)

(** A message type is one of:
- <<PrepareBlock>>: implicitly carries highest block of previous view,
- <<PrepareVote>>: implicitly carries <<PrepareQC>> of parent,
- <<ViewChange>>: Implicitly carries <<PrepareQC>> of highest block in view,
- <<PrepareQC>>: Carries nothing, i.e., GenesisBlock, and
- <<ViewChangeQC>>: Carries nothing, i.e., GenesisBlock.
*)

Inductive message_type :=
| PrepareBlock
| PrepareVote
| ViewChange
| PrepareQC
| ViewChangeQC.

Definition message_type_eq_dec : forall (mt1 mt2 : message_type), {mt1 = mt2}+{mt1 <> mt2}.
Proof.
decide equality.
Defined.

Definition message_type_eqb : message_type -> message_type -> bool :=
fun mt1 mt2 => if message_type_eq_dec mt1 mt2 then true else false.

Lemma message_type_eqb_correct : forall (mt1 mt2 : message_type),
  message_type_eqb mt1 mt2 = true <-> mt1 = mt2.
Proof.
intros; split; unfold message_type_eqb;
  destruct (message_type_eq_dec _ _); congruence.
Qed.

(** A message contains:
- <<get_message_type>>: the message type,
- <<get_view>>: a timestamp of a view,
- <<get_sender>>: the sender node,
- <<get_block>>: the primary block, and
- <<get_piggyback_block>>: piggyback block.
*)

Record message := mkMessage {
 get_message_type : message_type;
 get_view : nat;
 get_sender : node;
 get_block : block;
 get_piggyback_block : block;
}.

Definition message_eq_dec : forall (m1 m2: message), {m1 = m2}+{m1 <> m2}.
Proof.
decide equality.
- apply block_eq_dec.
- apply block_eq_dec.
- apply node_eq_dec.
- apply Nat.eq_dec.
- apply message_type_eq_dec.
Defined.

Definition message_eqb : message -> message -> bool :=
fun m1 m2 => if message_eq_dec m1 m2 then true else false.

Lemma message_eqb_correct : forall (m1 m2 : message),
  message_eqb m1 m2 = true <-> m1 = m2.
Proof.
intros; split; unfold message_eqb;
  destruct (message_eq_dec _ _); congruence.
Qed.

(** ** Node state *)

(** Node state contains:
- <<node_view>>: view number,
- <<node_id>>: node identifier,
- <<in_messages>>: incoming message buffer,
- <<counting_messages>>: processed message buffer,
- <<out_messages>>: outgoing message buffer, and
- <<timeout>>: timeout flag.
*)

Record NState := mkNState {
 node_view : nat;
 node_id : node;
 in_messages : list message;
 counting_messages : list message;
 out_messages : list message;
 timeout : bool;
}.

Definition NState_init (n : node) : NState :=
  mkNState 0 n [] [] [] false.

Definition NState_eq_dec : forall (s1 s2 : NState), {s1 = s2} + {s1 <> s2}.
Proof.
decide equality.
- apply Bool.bool_dec.
- apply (list_eq_dec message_eq_dec).
- apply (list_eq_dec message_eq_dec).
- apply (list_eq_dec message_eq_dec).
- apply node_eq_dec.
- apply Nat.eq_dec.
Defined.

(** ** Supplementary definitions **)

(** Block proposer status is a function of the view number and node id. *) 
Parameter is_block_proposer : node -> nat -> Prop.

(** We require that views have unique block proposers. *) 
Axiom is_new_proposer_unique :
  forall (n1 n2 : node) (v1 v2 : nat),
    is_block_proposer n1 v1 ->
    is_block_proposer n2 v2 ->
    v1 = v2 -> 
    n1 = n2.

Definition higher_block (b1 b2 : block) : block :=
 if (b_height b1) <? (b_height b2) then b2 else b1.

Definition message_with_higher_block (msg1 msg2 : message) : message :=
 if (b_height (get_block msg1)) <? (b_height (get_block msg2)) then msg2 else msg1.

Definition quorumb (lm : list message) : bool :=
  has_at_least_two_thirdsb (map get_sender lm). 

Definition quorum (lm : list message) : Prop :=
  has_at_least_two_thirds (map get_sender lm). 

Axiom quorum_subset :
  forall lm1 lm2,
    quorum lm1 -> 
    (forall msg, In msg lm1 -> In msg lm2) ->
    quorum lm2.

Lemma quorum_growth :
 forall (lm : list message), quorum lm ->
   forall (msg : message), quorum (msg :: lm).
Proof.
 intros lm H msg.
 unfold quorum in *.
 now apply majority_growth.
Qed.
