(* ==================================================================
   CRTPencilExtraPrimesProof.v

   Assembly + cheap checks for the 500 EXTRA primes that, combined
   with the original 710 mainline primes, give the 1210-prime list
   `crt_primes_pencil` used by the pencil-determinant lift.

   Heavy vm_computes stay in sibling files:
     CRTPencilExtra_PrimesProof.v  -- primality of the 500 extras
                                     (~6 min vm_compute)
     CRTPencilExtraChecksProof.v   -- per-prime mod check over 500
                                     extras (~9 min vm_compute)

   This file performs the cheap checks (NoDup over 1210 keys, valid
   range over 500 extras) and bundles them with the 710-mainline
   lemmas in CRTLift.v to expose `crt_primes_pencil_NoDup`,
   `crt_primes_pencil_valid`, `crt_primes_pencil_all_prime`,
   `crt_product_pencil`, and `crt_product_pencil_pos`.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From Stdlib Require Import Uint63.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import ModularArith CRTBridge CRTLift PrimeCheck CRTCheck Fermat.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilExtra_PrimesProof.

Open Scope Z_scope.

(* ================================================================== *)
(*  NoDup over the full 1210-prime list (cheap vm_compute, ~0.1 s).    *)
(* ================================================================== *)

Definition check_pencil_NoDup : bool :=
  nodup_Z (List.map Uint63.to_Z crt_primes_pencil).

Lemma check_pencil_NoDup_true : check_pencil_NoDup = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_primes_pencil_NoDup : NoDup (List.map Uint63.to_Z crt_primes_pencil).
Proof. apply nodup_Z_sound. exact check_pencil_NoDup_true. Qed.

(* ================================================================== *)
(*  Valid-range check (1 < p < 2^31) for the 500 EXTRA primes.         *)
(* ================================================================== *)

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

(* ================================================================== *)
(*  Assembly: all-prime + valid + product positivity over 1210 primes. *)
(* ================================================================== *)

Lemma crt_primes_pencil_all_prime :
  forall p, In p (List.map Uint63.to_Z crt_primes_pencil) -> Znumtheory.prime p.
Proof.
  intros p Hin. apply List.in_map_iff in Hin. destruct Hin as [pi [Hpeq Hin]]. subst p.
  unfold crt_primes_pencil in Hin. apply List.in_app_or in Hin.
  destruct Hin as [Hin1|Hin2].
  - exact (crt_primes_710_all_prime _ (List.in_map _ _ _ Hin1)).
  - apply check_prime_Z_sound. exact (extra_prime_at pi Hin2).
Qed.

Lemma crt_primes_pencil_valid :
  forall p, In p crt_primes_pencil -> valid_prime p.
Proof.
  intros p Hin. unfold crt_primes_pencil in Hin. apply List.in_app_or in Hin.
  destruct Hin as [Hin1|Hin2].
  - exact (crt_primes_valid p Hin1).
  - unfold valid_prime.
    have H := extra_valid_at p Hin2.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    unfold two_pow_31 in H2.
    split; lia.
Qed.

(* Product of all pencil primes. *)
Definition crt_product_pencil : Z :=
  List.fold_left Z.mul (List.map Uint63.to_Z crt_primes_pencil) 1%Z.

Lemma crt_product_pencil_pos : (0 < crt_product_pencil)%Z.
Proof.
  unfold crt_product_pencil.
  set (l := List.map Uint63.to_Z crt_primes_pencil).
  have Hall : forall x, In x l -> (0 < x)%Z.
  { intros x Hx. apply List.in_map_iff in Hx. destruct Hx as [pi [Hpeq Hin]]. subst x.
    have := crt_primes_pencil_valid pi Hin. unfold valid_prime. lia. }
  enough (forall acc, (0 < acc)%Z -> (0 < List.fold_left Z.mul l acc)%Z) by (apply H; lia).
  clear -Hall.
  induction l as [|x xs IH]; intros acc Hacc; simpl in *; first by exact Hacc.
  apply IH.
  - intros y Hy. apply Hall; right; exact Hy.
  - apply Z.mul_pos_pos; first by exact Hacc.
    apply Hall; left; reflexivity.
Qed.
