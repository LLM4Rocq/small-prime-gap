(* MaynardVerify/M2_2.v -- M2 closed-form check, rows 14..20. *)

From PrimeGapS1.MaynardVerify Require Import Def.

Lemma M2_check_rows_14_20 :
  M2_check_rows (List.seq 14 7) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
