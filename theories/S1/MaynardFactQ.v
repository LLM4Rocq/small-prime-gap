(* ==================================================================
   MaynardFactQ.v — factorial / binomial as rat, small helpers.

   These definitions wrap MathComp's nat-level factorial and binomial
   into ratios in `rat`, so that all subsequent Maynard-spec formulas
   can live in a single ring (`rat`) under `vm_compute`.
   ================================================================== *)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition factQ (n : nat) : rat := (n`!)%:R.
Definition binQ (n k : nat) : rat := ('C(n, k))%:R.

Lemma factQ_nz (n : nat) : factQ n != 0.
Proof. by rewrite /factQ pnatr_eq0 -lt0n fact_gt0. Qed.

