(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Set Universe Polymorphism.
#[universes(polymorphic=no)]
Sort Exc.

#[unfold_fix]
Symbol (raise@{u} : forall (A : Type@{Exc; u}), A).

Inductive nat : Type@{Exc; Set} :=
 | O : nat
 | S : nat -> nat.

Inductive bool : Type@{Exc; Set} :=
 | true
 | false.

Rewrite Rule raise_nat_match :=
| @{u u'} |- match raise@{u} nat as t0 return (?P : Type@{Exc; u'}) with
  | O => _
  | _ => _
  end => raise@{u'} ((?P@{t0 := raise@{u} nat}) : Type@{Exc; u'}).

Eval cbn in match raise nat with | O => O | S n => S n end.
