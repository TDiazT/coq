Sort Extr.

Constraint Extr ~> Prop.
Constraint Extr ~> SProp.
Constraint Type ~> Extr.

Set Universe Polymorphism.
Set Sort Polymorphism.

Axiom Univ@{l} : Type@{Extr|l+1}.
Axiom code@{l} : Prop -> Univ@{l}.
Axiom El@{l} : Univ@{l} -> Prop.
Axiom El_code : forall A, El (code A) = A.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition nat_rect@{i} := nat_poly@{Type Type | i}.
Definition nat_rec@{i} := nat_poly@{Type Type | i}.
Definition nat_ind@{i} := nat_poly@{Type Prop | i}.
Definition nat_sind@{i} := nat_poly@{Type SProp | i}.

Definition P (b : nat@{Extr|}) :=
  match b return Univ with
    O => code True
  | _ => code False
  end.

Lemma eq_true : forall (n:nat@{Extr|}), O = n -> El (P n).
Proof.
  intros b e.  destruct e. cbn. rewrite El_code. exact I.
Qed.

Lemma nat_discr (n : nat@{Extr|}): O = S n -> False.
Proof.
  intro e. rewrite <- (El_code _). exact (eq_true _ e).
Qed.

Inductive Vect (A : Type) : nat@{Extr|} -> Type :=
| vnil : Vect A O
| vcons : forall (a:A) n, Vect A n -> Vect A (S n).

Fail Definition length A n : Vect A n -> nat@{Type|} := fun _ => n. 

Fixpoint length A n : Vect A n -> nat@{Type|} := 
  fun v => match v with 
    | vnil _ => O 
    | vcons _  a n v => S (length A n v)
    end.
