Set Primitive Projections.
Record unit : Set := tt {}.
Fail Check fun x : unit => eq_refl : tt = x.
Fail Check fun x : unit => eq_refl : x = tt.
Fail Check fun x y : unit => (eq_refl : x = tt) : x = y.
Fail Check fun x y : unit => eq_refl : x = y.

Record ok : Set := tt' { a : unit }.

Fail Record nonprim : Prop := { undef : unit }.
(* The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent. 
  This is introduced by the constraints Prop -> Type *)
Record prim : Prop := { def : True }.
