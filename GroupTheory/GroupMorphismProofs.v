Require Import Utf8.
Require Import GroupDefinition.
Require Import GroupMorphism.

Generalizable Variables G H.

Definition identity `{A : Type} : A → A := λ x, x.

Proposition identity_changes_nothing `{A : Type} :
  ∀ a : A, identity a = a.
Proof.
  intro a.
  trivial.
Qed.

Instance identity_is_isomorphism `{Group G} : GroupIsomorphism G G identity.
Proof.
  repeat split.
  intros a b.
  intro a_is_b.
  assumption.
  intros g.
  rewrite identity_changes_nothing.
  exists g.
  reflexivity.
Qed.

Definition inverse `{Group G} : G → G := λ g, g⁻¹.

Proposition inverse_maps_to_inverse `{Group G} :
  ∀ g, inverse g = g⁻¹.
Proof.
  intro a.
  trivial.
Qed.