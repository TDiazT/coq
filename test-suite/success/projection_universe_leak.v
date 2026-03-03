Set Universe Polymorphism.

Definition relation (A : Type) := A -> A -> Type.

Section Acc.
  Universes i j.
  Context {A : Type@{i}} (R : relation@{i j} A).

  Cumulative Inductive Acc (x : A) : Type@{max(i,j)} :=
  | Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

  Definition well_founded := forall x, Acc x.
End Acc.

(* Regression test:
   The compiler used to introduce an extra projection universe on single-constructor
   inductives and leak it into the inductive universe context, making this
   polymorphic statement fail with an unbound universe error. *)
Lemma wf_universe_instance_stable@{i j}
  {A : Type@{i}} {R : relation@{i j} A} {wfR : well_founded R} : True.
Proof. exact I. Qed.

