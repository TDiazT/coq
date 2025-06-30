Set Primitive Projections.

Record foo (A : Type) :=
  { bar : Type ; baz := Set; bad : baz = bar }.

Set Nonrecursive Elimination Schemes.

Fail Record notprim : Prop :=
  { irrel : True; relevant : nat }.
(* The command has indeed failed with message:
  The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent. 
  This is introduced by the constraints Prop -> Type *)