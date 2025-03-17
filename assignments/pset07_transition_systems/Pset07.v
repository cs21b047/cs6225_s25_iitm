(** * 6.887 Formal Reasoning About Programs, Spring 2017 - Pset 4 *)

Require Import Frap Pset07Sig.


Theorem increment2_init_turn_ok :
  invariantFor increment2_sys increment2_init_turn_inv.
Proof.
apply invariant_induction; simplify.
invert H.
invert H0.
invert H1.
intros _.
reflexivity.
unfold increment2_init_turn_inv in *.
intros PRIV_EQ.
invert H0; simplify.
invert H1; simplify; try equality.
invert H1; simplify; try equality.
Qed.

Theorem increment2_flag_ok:
  invariantFor increment2_sys increment2_flag_inv.
Proof.
apply invariant_induction; simplify.
invert H.
invert H0.
invert H1.
apply Flag_inv with (pr1 := SetFlag) (pr2 := SetFlag) (f1 := false) (f2 := false);
simplify; equality.
Admitted.

Theorem increment2_correct_ok :
  invariantFor increment2_sys increment2_inv.
Proof.
Admitted.