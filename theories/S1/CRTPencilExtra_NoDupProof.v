(* NoDup check for crt_primes_pencil (1210 primes). ~0.1s vm_compute. *)

From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63.

From PrimeGapS1 Require Import CRTLift.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.

Open Scope Z_scope.

Definition check_pencil_NoDup : bool :=
  nodup_Z (List.map Uint63.to_Z crt_primes_pencil).

Lemma check_pencil_NoDup_true : check_pencil_NoDup = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_primes_pencil_NoDup : NoDup (List.map Uint63.to_Z crt_primes_pencil).
Proof. apply nodup_Z_sound. exact check_pencil_NoDup_true. Qed.
