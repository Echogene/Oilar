Require Import Utf8.
Require Import GroupDefinition.
Require Import DirectProduct.
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

(* The Klein four-group is the product of C₂ and C₂. *)

Definition K₄ := C₂ × C₂.

