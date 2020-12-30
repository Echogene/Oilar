Require Import Utf8.
Require Import GroupTheory.GroupDefinition.

Module GroupAction (G : Group).
Import G.

(* The set on which the group acts. *)
Parameter S : Set.

(* The group action. *)
Parameter α : G → S → S.

(* Add an operator for readability. *)
Notation "s ← g" := (α g s) (at level 50, left associativity).

(* Composition works. *)
(* Equivalent to (α g·h s) = (α h (α g s)). *)
Axiom act_comp : ∀ s g h, s←(g·h) = s←g←h.

(* The identity element does nothing. *)
Axiom act_id : ∀ s, s←e = s.

Lemma action_as_function : ∀ g, α g = λ s, s←g.
Proof.
  trivial.
Qed.

Lemma identity_action : α e = λ s, s.
Proof.
  rewrite action_as_function.
  (* I have no idea what tactics to use here. *)
  admit.
Admitted.

End GroupAction.