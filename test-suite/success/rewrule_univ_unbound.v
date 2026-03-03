(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Universe Polymorphism.
#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise@{u} : forall (A : Type@{Exc; u}), A).
Unset Collapse Sorts ToType.

Inductive bool : Type := true | false.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Rewrite Rule raise_nat_match :=
| @{u u'} |- match raise@{u} nat as t0 return (?P : Type@{Exc; u'}) with
  | O => _
  | _ => _
  end => raise@{u'} (?P@{t0 := raise@{u} nat}).

Eval cbn in match raise nat with | O => O | S n => S n end.

Inductive eq {A} (a : A) : A -> Type := eq_refl : eq a a.

Goal eq (match raise nat with | O => O | S n => S n end) (raise nat).
  cbn.
  reflexivity.
Qed.
