Require Import Notations.
Require Import Ltac.
Require Import Logic.

#[universes(template)]
Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

(*
Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p : prod A B) := match p with pair x y => x end.
  Definition snd (p: prod A B) := match p with pair x y => y end.

End projections.
*)

Set Universe Polymorphism.

Inductive sum@{sl sr s|ul ur|} (A : Type@{sl|ul}) (B : Type@{sr|ur}) : Type@{s|max(ul,ur)} :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Definition idV@{sl sr s s'|ul ur|} {A : Type@{sl|ul}} {B : Type@{sr|ur}} (x : sum@{sl sr s|ul ur} A B)
  : sum@{sl sr s'|ul ur} A B :=
  match x return sum@{sl sr s'|ul ur} A B with
  | inl a => inl a
  | inr b => inr b
  end.

Compute idV@{Prop Type Prop Type|Set Set} (inl I).

Print idV.
