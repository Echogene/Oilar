Require Import Utf8.
Require Import GroupDefinition.

Class GroupActionOp G S := ga_op: G → S → S.

(* Add an operator for readability. *)
Notation "g ↷ s" := (ga_op g s) (at level 45, right associativity).

Class GroupAction
    (G : Set) {e : G} `{Group G}
    (S: Set)
    (α: GroupActionOp G S)
: Prop := {
  ga_composition : ∀ g h s, (g·h)↷s = g↷h↷s;
  ga_identity : ∀ s, e↷s = s
}.
