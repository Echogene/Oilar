Require Import Utf8.
Require Import GroupDefinition.

Generalizable Variables G.

Proposition right_multiply_both_sides `{Group G} :
  ∀ a b c, a = b → a·c = b·c.
Proof.
  intros a b c.
  intros a_is_b.
  rewrite a_is_b.
  reflexivity.
Qed.

Notation "'multiply' d 'on' 'the' 'right' 'by' c" := (right_multiply_both_sides _ _ c d) (at level 100).

Proposition right_cancel_left_side `{Group G} :
  ∀ a b c, a·c = b → a = b·c⁻¹.
Proof.
  intros a b c.
  intros to_cancel.
  set (cancelled := multiply to_cancel on the right by c⁻¹).
  erewrite sg_assoc in cancelled.
  rewrite g_right_inverse in cancelled.
  rewrite g_right_identity in cancelled.
  exact cancelled.
Qed.

Notation "'cancel' 'the' 'left-hand' 'side' 'of' d 'on' 'the' 'right' 'by' c" := (right_cancel_left_side _ _ c d) (at level 100).

Proposition right_cancel_both_sides `{Group G} :
  ∀ a b c, a·c = b·c → a = b.
Proof.
  intros a b c.
  intros to_cancel.
  set (cancelled := cancel the left-hand side of to_cancel on the right by c).
  erewrite sg_assoc in cancelled.
  rewrite g_right_inverse in cancelled.
  rewrite g_right_identity in cancelled.
  exact cancelled.
Qed.

Notation "'cancel' d 'on' 'the' 'right' 'by' c" := (right_cancel_both_sides _ _ c d) (at level 100).

Corollary right_cancelling `{Group G} :
  ∀ a b c, a = b ↔ a·c = b·c.
Proof.
  intros a b c.
  refine (conj _ _).
    (* → *)
    exact (right_multiply_both_sides a b c).
    (* ← *)
    exact (right_cancel_both_sides a b c).
Qed.

Lemma more_right_cancelling `{Group G} :
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
Theorem unique_identity `{Group G} : ∀ a : G, a·a = a → a = e.
Proof.
  intros a.
  intros aa_is_a.
  set (cancelled := cancel the left-hand side of aa_is_a on the right by a).
  rewrite g_right_inverse in cancelled.
  exact cancelled.
Qed.

Proposition left_multiply_both_sides `{Group G} :
  ∀ a b c, a = b → c·a = c·b.
Proof.
  intros a b c.
  intros a_is_b.
  rewrite a_is_b.
  reflexivity.
Qed.

Notation "'multiply' d 'on' 'the' 'left' 'by' c" := (left_multiply_both_sides _ _ c d) (at level 100).

(* [e] is also the left-identity. *)
Theorem left_identity `{Group G} : ∀ a : G, e·a = a.
Proof.
  intros a.
  refine (cancel _ on the right by a⁻¹).
    rewrite sg_assoc.
    rewrite g_right_inverse.
    rewrite g_right_identity.
    reflexivity.
Qed.

(* [a⁻¹] is also the left-inverse of [a]. *)
Theorem left_inverse `{Group G} : ∀ a : G, a⁻¹·a = e.
Proof.
  intros a.
  refine (unique_identity (a⁻¹·a) _).
    rewrite <- sg_assoc.
    refine (multiply _ on the right by a).
      rewrite sg_assoc.
      rewrite g_right_inverse.
      rewrite g_right_identity.
      reflexivity.
Qed.


(* The inverse anti-distributes over multiplication. *)
Theorem inverse_anti_distribution `{Group G} : ∀ a b, (a·b)⁻¹ = b⁻¹·a⁻¹.
Proof.
  intros a b.
  refine (cancel _ on the right by a·b).
    rewrite left_inverse.
    rewrite sg_assoc.
    replace (a⁻¹·(a·b)) with ((a⁻¹·a) · b).
    rewrite left_inverse.
    replace (e · b) with b.
    rewrite left_inverse.
    reflexivity.
    rewrite left_identity.
    reflexivity.
    rewrite sg_assoc.
    reflexivity.
Qed.

(* The inverse of the inverse is the original element, or inversion is an involution. *)
Theorem inverse_involution `{Group G} : ∀ a, (a⁻¹)⁻¹ = a.
Proof.
  intros a.
  refine (cancel _ on the right by a⁻¹).
    rewrite left_inverse.
    rewrite g_right_inverse.
    reflexivity.
Qed.

(* The identity element is self-inverse. *)
Theorem identity_inverse `{Group G} : e⁻¹ = e.
Proof.
  refine (cancel _ on the right by e).
    rewrite left_inverse.
    rewrite g_right_identity.
    reflexivity.
Qed.
