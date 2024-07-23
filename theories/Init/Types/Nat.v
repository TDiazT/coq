(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import PreludeOptions.
Require Import Coq.Init.Notations.

Section NatSortPoly.
  Sort s.

  Inductive nat : Type@{s|Set} :=
    | O : nat
    | S (_ : nat) : nat.

  Fixpoint plus (a b : nat) : nat :=
    match a with
      | O => b
      | S n => S (plus n b)
    end.

  Definition pred (a : nat) : nat :=
    match a with
      | O => O
      | S n => n
    end.

End NatSortPoly.

Definition nat_rect@{s | u|} : forall P : nat@{Type|} -> Type@{s | u},
P O -> (forall n : nat@{Type|}, P n -> P (S n)) -> forall n : nat@{Type|}, P n :=
fun P f f0 =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end.

Declare Scope hex_nat_scope.
Delimit Scope hex_nat_scope with xnat.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%_nat.

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

Local Open Scope nat_scope.