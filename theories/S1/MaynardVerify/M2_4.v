(* MaynardVerify/M2_4.v -- M2 closed-form check, rows 28..34. *)

From PrimeGapS1.MaynardVerify Require Import Def.

Lemma M2_check_rows_28_34 :
  M2_check_rows (List.seq 28 7) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
