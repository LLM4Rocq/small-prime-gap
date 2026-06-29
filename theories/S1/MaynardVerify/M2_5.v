(* MaynardVerify/M2_5.v -- M2 closed-form check, rows 35..41. *)

From PrimeGapS1.MaynardVerify Require Import Def.

Lemma M2_check_rows_35_41 :
  M2_check_rows (List.seq 35 7) = true.
Proof.
  (* The tactic-engine `vm_compute` and the kernel re-check at `Qed`
     each ran the full 7x42 VM reduction (~262s + ~258s).  Emitting the
     proof term directly with `vm_cast_no_check` skips the tactic-side
     computation and leaves the kernel to do the VM conversion exactly
     once -- same axiom-free VM check, roughly half the wall time. *)
  vm_cast_no_check (eq_refl true).
Qed.
