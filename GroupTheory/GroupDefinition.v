Require Import Utf8.

Generalizable Variables G.

(* http://www.eelis.net/research/math-classes/mscs.pdf *)

Class SemiGroupOp A := sg_op: A → A → A.

(* Add an operator for readability. *)
Notation "a · b" := (sg_op a b) (at level 50, left associativity).

Class SemiGroup {G : Set} {op : SemiGroupOp G}: Prop := {
  (* The group operator is associative. *)
  sg_assoc : ∀ a b c, op (op a b) c = op a (op b c);
}.

Class GroupInv A := g_i: A → A.

(* Add a more familiar notation for inverse. *)
Notation "a ⁻¹" := (g_i a) (at level 40).

Class GroupId A := g_e: A.

Class Group {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e: GroupId G}: Prop := {
  g_sg :> SemiGroup;
  (* e is the right-identity for all elements. *)
  g_right_identity : ∀ a, op a e = a;
  (* a⁻¹ is the right-inverse of a for all elements. *)
  g_right_inverse : ∀ a, op a (i a) = e;
}.

Class AbelianGroup {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e: GroupId G}: Prop := {
  ag_g :> Group;
  (* The operation is commutative. *)
  ag_commutative : ∀ a b, op a b = op b a;
}.

Instance AsGroup `(A: AbelianGroup): Group := (@ag_g _ _ _ _ A).
