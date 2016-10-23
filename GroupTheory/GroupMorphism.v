Add LoadPath "~/.lib/Coq/GroupTheory".

Require Import Utf8.
Require Import GroupDefinition.

Module GroupMorphism (G : Group) (H : Group).
Import G.
Import H.

Parameter f : G → H.

End GroupMorphism.