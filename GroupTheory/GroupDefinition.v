Require Import Utf8.

Generalizable Variables G.

(* http://www.eelis.net/research/math-classes/mscs.pdf *)

Class SemiGroupOp (A: Set) := sg_op: A → A → A.

(* Add an operator for readability. *)
Infix "·" := sg_op (at level 50, left associativity).
Notation "(·)" := sg_op (only parsing).

Class SemiGroup {G : Set} {op : SemiGroupOp G}: Prop := {
  (* The group operator is associative. *)
  sg_assoc : ∀ a b c, (a·b)·c = a·(b·c);
}.

Class GroupInv (A: Set) := g_i: A → A.

(* Add a more familiar notation for inverse. *)
Notation "a ⁻¹" := (g_i a) (at level 40).

Class Group {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e: G}: Prop := {
  g_sg :> SemiGroup;
  (* e is the right-identity for all elements. *)
  g_right_identity : ∀ a, a·e = a;
  (* a⁻¹ is the right-inverse of a for all elements. *)
  g_right_inverse : ∀ a, a·a⁻¹ = e;
}.

Class AbelianGroup {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e: G}: Prop := {
  ag_g :> @Group G op i e;
  (* The operation is commutative. *)
  ag_commutative : ∀ a b, a·b = b·a;
}.

Instance groups_are_semigroups `{Group G}: (@SemiGroup G _).
Proof.
  exact g_sg.
Qed.
Instance AsSemiGroup `(A: Group): SemiGroup := (@g_sg _ _ _ _ A).

Instance abelian_groups_are_groups
    {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e : G} {P : @AbelianGroup G op i e} :
    (@Group G op i e).
Proof.
  exact ag_g.
Qed.
Instance AsGroup `(A: AbelianGroup): Group := (@ag_g _ _ _ _ A).
