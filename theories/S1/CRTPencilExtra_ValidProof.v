(* Valid-range check (1 < p < 2^31) for the 500 EXTRA primes.  Fast. *)

From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.

Open Scope Z_scope.

Definition two_pow_31 : Z := 2147483648.

Definition check_extra_valid : bool :=
  List.forallb (fun p => (Z.ltb 1 (Uint63.to_Z p) && Z.ltb (Uint63.to_Z p) two_pow_31)%bool)
               crt_primes_pencil_extra.

Lemma check_extra_valid_true : check_extra_valid = true.
Proof. vm_compute. reflexivity. Qed.

Opaque crt_primes_pencil_extra.

Lemma extra_valid_at (p : Uint63.int) (Hin : In p crt_primes_pencil_extra) :
  (Z.ltb 1 (Uint63.to_Z p) && Z.ltb (Uint63.to_Z p) two_pow_31)%bool = true.
Proof. exact (proj1 (List.forallb_forall _ _) check_extra_valid_true p Hin). Qed.

(* Every extra prime is > 43 (in fact > 1073756473). *)
Definition check_extra_gt_43 : bool :=
  List.forallb (fun p => Z.ltb 43 (Uint63.to_Z p)) crt_primes_pencil_extra.

Lemma check_extra_gt_43_true : check_extra_gt_43 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma extra_gt_43_at (p : Uint63.int) (Hin : In p crt_primes_pencil_extra) :
  Z.ltb 43 (Uint63.to_Z p) = true.
Proof. exact (proj1 (List.forallb_forall _ _) check_extra_gt_43_true p Hin). Qed.
