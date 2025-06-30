Set Primitive Projections.
Fail Record Box (T : Type) : Prop := wrap {prop : T}.
(* The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent. 
    This is introduced by the constraints Prop -> Type *)
Fail Definition down (x : Type) : Prop := Box x.
Definition up (x : Prop) : Type := x.

Fail Definition back A : up (down A) -> A := @prop A.
