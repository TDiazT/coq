(* These should go in their own file *)
From Coq.Ltac2 Require Import Ltac2.

Ltac2 rewrite0 (h : constr) :=
    unshelve (eapply (J_nodep _ _ _ _ _ $h)).

#[global]
Ltac2 Notation "rewrite!" h(constr) := rewrite0 h.

Ltac2 rewrite0_r (h : constr) :=
  unshelve (eapply (J_nodep_r _ _ _ _ _ (eq_sym $h))).

#[global]
Ltac2 Notation "rewrite!" "<-" h(constr) := rewrite0_r h.
