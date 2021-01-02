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
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: G} `{@Group G g_op g_i g_e}
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: H} `{@Group H h_op h_i h_e}
    : SemiGroupOp (prod G H) := fun (a: prod G H) (b: prod G H) =>
  match a, b with
  | (x, y), (s, t) => (g_op x s, h_op y t)
  end.

Definition GroupProduct_i
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: G} `{@Group G g_op g_i g_e}
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: H} `{@Group H h_op h_i h_e}
    : GroupInv (prod G H) := fun (a: prod G H) =>
  match a with
  | (x, y) => (g_i x, h_i y)
  end.

Instance GroupProduct
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: G} (P : @Group G g_op g_i g_e)
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: H} (Q : @Group H h_op h_i h_e)
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
  repeat rewrite (@sg_assoc G g_op _).
  repeat rewrite (@sg_assoc H h_op _).
  reflexivity.
  intros a.
  compute.
  destruct a.
  rewrite (@g_right_identity G g_op _).
  rewrite (@g_right_identity H h_op _).
  reflexivity.
  assumption.
  assumption.
  intros a.
  compute.
  destruct a.
  rewrite (@g_right_inverse G g_op g_i _ _).
  rewrite (@g_right_inverse H h_op h_i _ _).
  reflexivity.
Qed.

Print ag_commutative.

Instance AbelianGroupProduct
    {G : Set} {g_op : SemiGroupOp G} {g_i : GroupInv G} {g_e: G} (P : @AbelianGroup G g_op g_i g_e)
    {H : Set} {h_op : SemiGroupOp H} {h_i : GroupInv H} {h_e: H} (Q : @AbelianGroup H h_op h_i h_e)
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
  repeat rewrite (@sg_assoc G g_op _).
  repeat rewrite (@sg_assoc H h_op _).
  reflexivity.
  intros a.
  compute.
  destruct a.
  rewrite (@g_right_identity G g_op _).
  rewrite (@g_right_identity H h_op _).
  reflexivity.
  exact abelian_groups_are_groups.
  exact abelian_groups_are_groups.
  intros a.
  compute.
  destruct a.
  rewrite (@g_right_inverse G g_op g_i _ _).
  rewrite (@g_right_inverse H h_op h_i _ _).
  reflexivity.
  intros a b.
  compute.
  destruct a.
  destruct b.
  rewrite (@ag_commutative G g_op g_i g_e).
  rewrite (@ag_commutative H h_op h_i h_e).
  reflexivity.
  assumption.
  assumption.
Qed.

Notation "A × B" := (AbelianGroupProduct A B) (at level 30, right associativity).

(* The Klein four-group is the product of C₂ and C₂. *)

Definition K₄ := C₂ × C₂.

