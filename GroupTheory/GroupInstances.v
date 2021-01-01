Require Import Utf8.
Require Import GroupDefinition.
Require Import Setoid.

(* The group with one element is an abelian group. *)

Inductive One : Set :=
  | e1 : One.

Definition C₁_op : SemiGroupOp One := fun (a: One) (b: One) => e1.
Definition C₁_i : GroupInv One := fun (a: One) => e1.

Instance C₁ : @AbelianGroup One C₁_op C₁_i e1.
Proof.
  repeat split.
  intros a.
  destruct a.
  simpl. reflexivity.
Qed.

(* The cyclic group with two elements is an abelian group. *)

Inductive Two : Set :=
  | zero : Two
  | one : Two.

Definition C₂_op : SemiGroupOp Two := fun (a: Two) (b: Two) =>
  match a, b with
  | zero, _ => b
  | _, zero => a
  | one, one => zero
  end.

Definition C₂_i : GroupInv Two := fun (a: Two) =>
  match a with
  | zero => zero
  | one => one
  end.

Instance C₂ : @AbelianGroup Two C₂_op C₂_i zero.
Proof.
  repeat split.
  intros a b c.
  destruct a.
  all: simpl.
  reflexivity.
  destruct b.
  destruct c.
  all : simpl.
  reflexivity. reflexivity.
  destruct c.
  reflexivity. reflexivity.
  intros a.
  destruct a.
  all: simpl.
  reflexivity. reflexivity.
  intros a.
  destruct a.
  all: simpl.
  reflexivity. reflexivity.
  intros a b.
  destruct a.
  destruct b.
  all: simpl.
  reflexivity. reflexivity.
  destruct b.
  all: simpl.
  reflexivity. reflexivity.
Qed.

(* The direct product of two groups is a group. *)

Definition GroupProduct_op
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: GroupId G} `{@Group G g_op g_i g_e}
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: GroupId H} `{@Group H h_op h_i h_e}
    : SemiGroupOp (prod G H) := fun (a: prod G H) (b: prod G H) =>
  match a, b with
  | (x, y), (s, t) => (g_op x s, h_op y t)
  end.

Definition GroupProduct_i
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: GroupId G} `{@Group G g_op g_i g_e}
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: GroupId H} `{@Group H h_op h_i h_e}
    : GroupInv (prod G H) := fun (a: prod G H) =>
  match a with
  | (x, y) => (g_i x, h_i y)
  end.

Instance GroupProduct
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: GroupId G} (P : @Group G g_op g_i g_e)
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: GroupId H} (Q : @Group H h_op h_i h_e)
    : (@Group
        (prod G H)
        (@GroupProduct_op G g_op g_i g_e P H h_op h_i h_e Q)
        (@GroupProduct_i G g_op g_i g_e P H h_op h_i h_e Q)
        (g_e, h_e)
    ).
Proof.
  repeat split.
  intros a b c.
  compute.
  destruct a.
  destruct b.
  destruct c.
  repeat rewrite sg_assoc.
  reflexivity.
  intros a.
  compute.
  destruct a.
  repeat rewrite g_right_identity.
  reflexivity.
  intros a.
  compute.
  destruct a.
  repeat rewrite g_right_inverse.
  reflexivity.
Qed.

Instance AbelianGroupProduct
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: GroupId G} (P : @AbelianGroup G g_op g_i g_e)
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: GroupId H} (Q : @AbelianGroup H h_op h_i h_e)
    : (@AbelianGroup
        (prod G H)
        (@GroupProduct_op G g_op g_i g_e (AsGroup P) H h_op h_i h_e (AsGroup Q))
        (@GroupProduct_i G g_op g_i g_e (AsGroup P) H h_op h_i h_e (AsGroup Q))
        (g_e, h_e)
    ).
Proof.
  repeat split.
  intros a b c.
  compute.
  destruct a.
  destruct b.
  destruct c.
  repeat rewrite sg_assoc.
  reflexivity.
  intros a.
  compute.
  destruct a.
  repeat rewrite g_right_identity.
  reflexivity.
  intros a.
  compute.
  destruct a.
  repeat rewrite g_right_inverse.
  reflexivity.
  intros a b.
  compute.
  destruct a.
  destruct b.
  rewrite ag_commutative.
  replace (h_op h h0) with (h_op h0 h).
  reflexivity.
  rewrite ag_commutative.
  reflexivity.
Qed.

Notation "A × B" := (AbelianGroupProduct A B) (at level 30, right associativity).

(* The Klein four-group is the product of C₂ and C₂. *)

Definition K₄ := C₂ × C₂.

