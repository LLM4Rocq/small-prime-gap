(* ==================================================================
   CRTPencilExtraPrimesProof.v

   Assembly: NoDup + all-prime + valid-range + crt_product_pos for
   the full crt_primes_pencil list (710 mainline + 500 extras).

   Heavy vm_computes are pre-cached in sibling files:
     CRTPencilExtra_NoDupProof.v   — NoDup (1210 keys, ~0.1 s)
     CRTPencilExtra_PrimesProof.v  — primality of 500 extras (~6 min)
     CRTPencilExtra_ValidProof.v   — valid range of 500 extras (cheap)
   This file just glues them with the original 710-prime lemmas in
   CRTLift.v, then defines the 1210-prime product and proves its sign.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From Stdlib Require Import Uint63.

From mathcomp Require Import all_ssreflect.

From PrimeGapS1 Require Import ModularArith CRTBridge CRTLift PrimeCheck CRTCheck Fermat.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilExtra_NoDupProof.
From PrimeGapS1 Require Import CRTPencilExtra_PrimesProof.
From PrimeGapS1 Require Import CRTPencilExtra_ValidProof.

Open Scope Z_scope.

Lemma crt_primes_pencil_all_prime :
  forall p, In p (List.map Uint63.to_Z crt_primes_pencil) -> Znumtheory.prime p.
Proof.
  intros p Hin. apply List.in_map_iff in Hin. destruct Hin as [pi [Hpeq Hin]]. subst p.
  unfold crt_primes_pencil in Hin. apply List.in_app_or in Hin.
  destruct Hin as [Hin1|Hin2].
  - exact (crt_primes_710_all_prime _ (List.in_map _ _ _ Hin1)).
  - apply check_prime_Z_sound. exact (extra_prime_at pi Hin2).
Qed.

Opaque crt_primes_pencil_extra.

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
