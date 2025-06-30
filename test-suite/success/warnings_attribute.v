
Set Primitive Projections.

Fail #[warnings="+non-primitive-record"]
 Record foo : Prop := { _ : nat }.

Fail #[warnings="-non-primitive-record"]
 Record foo : Prop := { _ : nat }.
