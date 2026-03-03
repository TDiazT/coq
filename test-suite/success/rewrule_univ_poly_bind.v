(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Universe Polymorphism.
#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise@{u} : forall (A : Type@{Exc; u}), A).
Unset Collapse Sorts ToType.

Inductive bool@{s;u} : Type@{s;u} := true | false.

Inductive nat@{s;u} : Type@{s;u} :=
| O : nat
| S : nat -> nat.

Rewrite Rule raise_nat_match :=
| @{u u' u''} |- match raise@{u} nat@{Exc;u'} as t0 return (?P : Type@{Exc; u''}) with
  | O => _
  | _ => _
  end => raise@{u''} (?P@{t0 := raise@{u} nat@{Exc;u'}}).
