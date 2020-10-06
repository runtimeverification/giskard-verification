From Coq Require Import Arith Bool List.
From Giskard Require Import lib structures local global prepare precommit.

Import ListNotations.

Set Implicit Arguments.

(** * Safety property three: Commit stage height injectivity *)

(** ** Commit stage definition *)

(** We say that a block is in commit stage in some local state iff it is in precommit stage
and its child block is in precommit stage. *)
Definition commit_stage (tr : GTrace) (i : nat) (n : node) (b : block) :=
  exists b_child,
    parent_of b_child = b /\
    precommit_stage tr i n b /\ 
    precommit_stage tr i n b_child.

(** ** Commit stage height injectivity statement *)

(** The third and final safety property states that no two same height blocks can be at
commit stage, i.e., commit stage block height is injective. *)

(** In any global state <<i>> in a valid protocol trace <<tr>> that begins with the
initial state and respects the protocol transition rules, if there are two participating
nodes <<n>> and <<m>>, and two distinct blocks <<b1>> and <<b2>> of the same height
that are both at precommit stage for <<n>> and <<m>>'s local state, respectively,
then we can prove a contradiction. *)

Definition commit_height_injective_statement :=
  forall (tr : GTrace),
    protocol_trace tr ->
    forall (i : nat) (n m : node),
      In n participants ->
      In m participants ->
      forall (b1 b2 : block),
        b1 <> b2 -> 
        commit_stage tr i n b1 ->
        commit_stage tr i m b2 -> 
        b_height b1 = b_height b2 ->
        False.

(** ** Proof of commit stage height injectivity *)

(** Intuition behind the proof: From the definition of commit stage, we know that each
block must also be in precommit stage. Because the two blocks are of equal height and
different, their respective children must also be of equal height and different.
We then apply precommit stage height injectivity to directly obtain a contradiction. *)
Theorem commit_height_injective :
  precommit_stage_height_injective_statement ->
  commit_height_injective_statement.
Proof.
  intros H_precommit tr H_prot i n m H_part_n H_part_m b1 b2 H_neq H_commit1 H_commit2 H_height.
  destruct H_commit1 as [b_child1 [H_parent1 [H_precommit1 _]]].
  destruct H_commit2 as [b_child2 [H_parent2 [H_precommit2 _]]].
  red in H_precommit.
  spec H_precommit tr H_prot i n m b1 b2.
  spec H_precommit H_part_n H_part_m. 
  spec H_precommit.
  intro H_false. 
  subst. contradiction.
  spec H_precommit H_precommit1 H_precommit2 H_height.
  inversion H_precommit. 
Qed.
