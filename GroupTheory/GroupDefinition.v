Require Import Utf8.

Module Type Group.

(* The set of a group. *)
Parameter G : Set.

(* The binary operator. *)
Parameter op : G → G → G.

(* The group identity. *)
Parameter e : G.

(* Add an operator for readability. *)
Infix "·" := op (at level 50, left associativity).

(* The inverse operator. *)
Parameter i : G → G.

(* Add a more familiar notation for inverse. *)
Notation "a ⁻¹" := (i a) (at level 40).

(* The group operator is associative. *)
Axiom assoc : ∀ a b c, (a·b)·c = a·(b·c).

(* e is the right-identity for all elements. *)
Axiom id_r : ∀ a, a·e = a.

(* a⁻¹ is the right-inverse of a for all elements. *)
Axiom inv_r : ∀ a, a·a⁻¹ = e.

End Group.