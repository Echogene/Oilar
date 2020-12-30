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
Unshelve.
  exact groups_are_semigroups.
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
Unshelve.
  exact groups_are_semigroups.
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