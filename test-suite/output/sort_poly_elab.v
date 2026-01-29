Set Universe Polymorphism.
Unset Collapse Sorts ToType.
Set Printing Universes.
Set Printing Sort Qualities.
Set Printing All.

Definition qsort := Type.
About qsort.

Definition qsort' : Type := Type.
About qsort'.

Section Inductives.
  Inductive sigma (A:Type) (B:A -> Type) : Type
    := pair : forall x : A, B x -> sigma A B.
  About sigma.

  Definition sigma_srect A B
    (P : sigma A B -> Type)
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.
  About sigma_srect.

  Definition pr1 {A B} (s:sigma A B) : A
    := match s with pair _ _ x _ => x end.
  About pr1.

  Definition pr2 {A B} (s:sigma A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.
  About pr2.
End Inductives.

Section Records.
  Set Primitive Projections.

  Record R1 (A:Type) : Type := { R1f1 : A }.
  About R1.

  #[projections(primitive=no)]
  Record R2 (A:Type) := { R2f1 : A; R2f2 : nat }.
  About R2.
  About R2f1.
  About R2f2.


  Unset Primitive Projections.

  Inductive eq {A} x : A -> Type :=
  eq_refl : eq x x.

  Inductive bool := true | false.

  Record R3 := {
    R3f1 : bool ;
    R3f2 : bool ;
  }.
  About R3.
  About R3f1.
  About R3f2.

  (* Elimination constraints are added specifically for each projection *)
  Record R4 (A : Type) := {
    R4f1 : A ;
    R4f2 : eq R4f1 R4f1 ;
    R4f3 : bool
  }.
  About R4.
  About R4f1.
  About R4f2.
  About R4f3.

  Record R5 := {
    R5f1 : bool ;
    R5f2 : let r := {| R4f1 := true; R4f2 := eq_refl true ; R4f3 := R5f1 |} in
         if R4f3 bool r then
          bool
        else
          bool ;
    R5f3 : bool
  }.
  About R5.
  About R5f1.
  About R5f2.
  About R5f3.

  Record R6 := {
    R6f1 : bool ;
    R6f2 : let f' :=
          fix F n :=
            if R6f1 then n else O
        in
        match f' O with
        | O => bool
        | S _ => nat
        end
        }.
  About R6.
  About R6f1.
  About R6f2.

  Record R7 := {
    R7f1 : Type ;
    R7f2 : Type ;
    R7f3 : bool;
    R7f4 : forall (b : bool),
          match b with
          | true => match R7f3 with (* Depends on R7f3 *)
                    | true => R7f1
                    | false => R7f2
                    end
          | false => bool
          end
    }.
  About R7.
  About R7f1.
  About R7f2.
  About R7f3.
  About R7f4.

End Records.

Module Classes.

  Class C1 (A : Type) : Type := {
    C1f1 : A
  }.
  About C1.
  About C1f1.

  Inductive unit : Type := tt.

  Instance C1I1 : C1 unit := { C1f1 := tt }.
  About C1I1.

  Program Instance C1ProgramI1 : C1 unit.
  Next Obligation.
    exact tt.
  Defined.
  About C1ProgramI1.

  #[refine]
  Instance C1RefineI1 : C1 unit := { C1f1 := _ }.
  exact tt.
  Defined.
  About C1RefineI1.

  Instance C1InteractiveI1 : C1 unit.
  Proof. constructor. exact tt. Defined.
  About C1InteractiveI1.

  Axiom (C1AxiomaticI1 : C1 unit).
  Existing Instance C1AxiomaticI1.
  About C1AxiomaticI1.

  Inductive C1InductiveI1 := mkInductive.

  Existing Class C1InductiveI1.
  About C1InductiveI1.

End Classes.

Unset Universe Polymorphism.
Set Collapse Sorts ToType.

Fail #[universes(collapse_sort_variables=no)]
Inductive Attr : Type := attr.

#[universes(polymorphic, collapse_sort_variables=no)]
Inductive Attr : Type := attr.
About Attr.
