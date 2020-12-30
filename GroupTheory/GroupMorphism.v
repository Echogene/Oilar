Require Import Utf8.
Require Import GroupDefinition.

Generalizable Variables G H f.

Class GroupHomomorphism (G : Set) `{Group G} (H : Set) `{Group H} (f: G → H): Prop := {
  (* Morphisms distribute over the group product. *)
  ghm_distributes : ∀ a b, f (a·b) = (f a)·(f b);

  (* Morphisms preserve the inverse function. *)
  ghm_inverses_preserved : ∀ a, (f (a⁻¹)) = (f a)⁻¹;

  (* The identity is a fixed point of morphisms. *)
  ghm_identity_fixed : (f (g_e)) = (g_e);
}.

Class GroupMonomorphism (G : Set) `{Group G} (H : Set) `{Group H} (f: G → H): Prop := {
  gmm_ghm :> GroupHomomorphism G H f;
  gmm_injective : ∀ a b, f a = f b → a = b;
}.

Instance monomorphisms_are_morphisms `{GroupMonomorphism G H f}: GroupHomomorphism G H f.
Proof.
  exact gmm_ghm.
Qed.

Class GroupEpimorphism (G : Set) `{Group G} (H : Set) `{Group H} (f: G → H): Prop := {
  gem_ghm :> GroupHomomorphism G H f;
  gem_surjective : ∀ (g : G), ∃ (h : H), f g = h;
}.

Instance epimorphisms_are_morphisms `{GroupEpimorphism G H f}: GroupHomomorphism G H f.
Proof.
  exact gem_ghm.
Qed.

Class GroupIsomorphism (G : Set) `{Group G} (H : Set) `{Group H} (f: G → H): Prop := {
  gim_gmm :> GroupMonomorphism G H f;
  gim_gem :> GroupEpimorphism G H f;
}.

Class GroupEndomorphism (G : Set) `{Group G} (f: G → G): Prop := {
  genm_ghm :> GroupHomomorphism G G f;
}.

Class GroupAutomorphism (G : Set) `{Group G} (f: G → G): Prop := {
  gam_gim :> GroupIsomorphism G G f;
}.