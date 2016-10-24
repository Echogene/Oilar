Require Import Coq.Unicode.Utf8.

(* The set of the group. *)
Parameter G : Set.

(* The binary operator. *)
Parameter f : G → G → G.

(* For readability, we use infix · to stand for the binary operator. *)
Infix "·" := f (at level 50, left associativity).

(* The group identity. *)
Parameter e : G.

(* The inverse operator. *)
Parameter i : G → G.

(* Add a more familiar form of the inverse operator. *)
Notation "a ⁻¹" := (i a) (at level 20, left associativity).

(* The operator [·] is also right-associative. *)
Axiom associativity : ∀ a b c, a·b·c = a·(b·c).

(* [e] is the right-identity for all elements [a] *)
Axiom right_identity : ∀ a, a·e = a.

(* [a⁻¹] is the right-inverse of [a]. *)
Axiom right_inverse : ∀ a, a·a⁻¹ = e.

Proposition right_multiply_both_sides :
  ∀ a b c, a = b → a·c = b·c.
Proof.
  intros a b c.
  intros a_is_b.
  rewrite a_is_b.
  reflexivity.
Qed.

Notation "'multiply' d 'on' 'the' 'right' 'by' c" := (right_multiply_both_sides _ _ c d) (at level 100).

Proposition right_cancel_left_side :
  ∀ a b c, a·c = b → a = b·c⁻¹.
Proof.
  intros a b c.
  intros to_cancel.
  set (cancelled := multiply to_cancel on the right by c⁻¹).
  rewrite associativity in cancelled.
  rewrite right_inverse in cancelled.
  rewrite right_identity in cancelled.
  exact cancelled.
Qed.

Notation "'cancel' 'the' 'left-hand' 'side' 'of' d 'on' 'the' 'right' 'by' c" := (right_cancel_left_side _ _ c d) (at level 100).

Proposition right_cancel_both_sides :
  ∀ a b c, a·c = b·c → a = b.
Proof.
  intros a b c.
  intros to_cancel.
  set (cancelled := cancel the left-hand side of to_cancel on the right by c).
  rewrite associativity in cancelled.
  rewrite right_inverse in cancelled.
  rewrite right_identity in cancelled.
  exact cancelled.
Qed.

Notation "'cancel' d 'on' 'the' 'right' 'by' c" := (right_cancel_both_sides _ _ c d) (at level 100).

Corollary right_cancelling :
  ∀ a b c, a = b ↔ a·c = b·c.
Proof.
  intros a b c.
  refine (conj _ _).
    (* → *)
    exact (right_multiply_both_sides a b c).
    (* ← *)
    exact (right_cancel_both_sides a b c).
Qed.

Lemma more_right_cancelling :
  ∀ a b c LHS RHS,
    a·c = LHS
    → b·c = RHS
    → a = b
    → LHS = RHS.
Proof.
  intros a b c LHS RHS.
  intros ac_is_LHS bc_is_RHS a_is_b.
  rewrite a_is_b in ac_is_LHS.
  rewrite ac_is_LHS in bc_is_RHS.
  exact bc_is_RHS.
Qed.

(* The identity [e] is unique. *)
Theorem unique_identity : ∀ a, a·a = a → a = e.
Proof.
  intros a.
  intros aa_is_a.
  set (cancelled := cancel the left-hand side of aa_is_a on the right by a).
  rewrite right_inverse in cancelled.
  exact cancelled.
Qed.

Proposition left_multiply_both_sides :
  ∀ a b c, a = b → c·a = c·b.
Proof.
  intros a b c.
  intros a_is_b.
  rewrite a_is_b.
  reflexivity.
Qed.

Notation "'multiply' d 'on' 'the' 'left' 'by' c" := (left_multiply_both_sides _ _ c d) (at level 100).

(* [a⁻¹] is also the left-inverse of [a]. *)
Theorem left_inverse : ∀ a, a⁻¹·a = e.
Proof.
  intros a.
  refine (unique_identity (a⁻¹·a) _).
    rewrite <- associativity.
    refine (multiply _ on the right by a).
      rewrite associativity.
      rewrite right_inverse.
      rewrite right_identity.
      reflexivity.
Qed.

(* [e] is also the left-identity. *)
Theorem left_identity : ∀ a, e·a = a.
Proof.
  intros a.
  refine (cancel _ on the right by a⁻¹).
    rewrite associativity.
    rewrite right_inverse.
    rewrite right_identity.
    reflexivity.
Qed.

(* The inverse anti-distributes over multiplication. *)
Theorem inverse_anti_distribution : ∀ a b, (a·b)⁻¹ = b⁻¹·a⁻¹.
Proof.
  intros a b.
  refine (cancel _ on the right by a·b).
    rewrite left_inverse.
    rewrite <- associativity.
    refine (cancel _ on the right by b⁻¹).
      rewrite associativity.
      rewrite right_inverse.
      rewrite associativity.
      rewrite right_identity.
      rewrite associativity.
      rewrite left_inverse.
      rewrite right_identity.
      rewrite left_identity.
      reflexivity.
Qed.

(* The inverse of the inverse is the original element, or inversion is an involution. *)
Theorem inverse_involution : ∀ a, (a⁻¹)⁻¹ = a.
Proof.
  intros a.
  refine (cancel _ on the right by a⁻¹).
    rewrite left_inverse.
    rewrite right_inverse.
    reflexivity.
Qed.

(* The identity element is self-inverse. *)
Theorem identity_inverse : e⁻¹ = e.
Proof.
  refine (cancel _ on the right by e).
    rewrite left_inverse.
    rewrite right_identity.
    reflexivity.
Qed.
