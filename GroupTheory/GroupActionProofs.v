Require Import Utf8.
Require Import GroupDefinition.
Require Import GroupAction.
Require Import GroupProofs.
Require Import Setoid.

Generalizable Variables G.

Definition operation_as_action `{Group G} : GroupActionOp G G := λ g h, g·h.

Proposition groups_act_over_themselves
    {G : Set} {op : SemiGroupOp G} {i : GroupInv G} {e : G} {P : @Group G op i e} :
    @GroupAction G e _ _ _ _ G operation_as_action.
Proof.
  split.
  intros.
  compute.
  rewrite (@sg_assoc G op _).
  reflexivity.
  intros.
  compute.
  rewrite (@left_identity G op i e P _).
  reflexivity.
Qed.