From Coq Require Import Arith List.

Import ListNotations.

Set Implicit Arguments.

(** * Supplementary general tactics and results *)

Tactic Notation "spec" hyp(H) := 
  match type of H with ?a -> _ => 
  let H1 := fresh in (assert (H1: a); 
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) := 
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) := 
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) := 
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) := 
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) := 
  (generalize (H a b c d e); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) := 
  (generalize (H a b c d e f); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr (g):=  
  (generalize (H a b c d e f g); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr (g) constr(h) :=  
  (generalize (H a b c d e f g h); clear H; intro H).

Lemma remove_subset :
  forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (x1 x2 : A),
    In x1 (remove eq_dec x2 l) ->
    In x1 l. 
Proof.
  intros A eq_dec l x1 x2 H_in.
  induction l as [|hd tl IHl].
  inversion H_in. 
  simpl in H_in.
  destruct (eq_dec x2 hd). subst.
  spec IHl H_in. right. assumption.
  simpl in H_in. destruct H_in. subst. left; reflexivity.
  right. now apply IHl.
Qed.

Theorem modus_tollens : forall (P Q : Prop), (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros P Q HPQ HQ.
  intro HP.
  contradict HQ.
  apply HPQ.
  assumption.
Qed.

Lemma le_S_disj :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right; reflexivity.
  left; exact H1.  
Qed.
