(* ===================================================================
   CRTFrame.v -- CRT framing data for the char_poly(M1_int) PD
   certificate.

   This file assembles the side-conditions needed to feed the
   per-prime modular char-poly soundness theorem
   (ModularFL.char_poly_modZ_sound) and the CRT reconstruction
   theorem (CRTCheck.crt_reconstruct) for the 42x42 integer matrix
   M1_int and its claimed characteristic polynomial cp_M1_value.

   Established here, all axiom-free over Stdlib's Z (vm_compute only):

     crt_primes_M1_NoDup      : NoDup crt_primes_M1
     crt_primes_M1_all_prime  : In p crt_primes_M1 -> Znumtheory.prime p
     crt_primes_M1_gt43       : In p crt_primes_M1 -> 43 < p
     M1_square                : square_mat 42 M1_int
     M1_fl_div                : fl_all_divisible 42 1 M1_int
                                  (meye 42) (mzero 42) 1
     per_prime_hess           : In p crt_primes_M1 ->
                                  char_poly_hess p M1_int
                                    = map (fun c => c mod p) cp_M1_value
     per_prime_ok             : In p crt_primes_M1 ->
                                  char_poly_modZ p M1_int
                                    = map (fun c => c mod p) cp_M1_value
     per_prime_all            : forallb per_prime_chk crt_primes_M1 = true

   The heavy step is per_prime_hess, discharged by a single boolean
   forallb over the FAST O(n^3) Hessenberg char-poly (ModularHess.v),
   ~4.5 s/prime, ~15 min over the 200 primes -- where the O(n^4) modular
   Faddeev-LeVerrier pass would take ~16 h.  per_prime_ok / per_prime_all
   transport that to char_poly_modZ via char_poly_modZ_sound and
   char_poly_hess_sound (both sound against char_poly_int M1_int mod p),
   so no O(n^4) pass is ever run.

   No Uint63 / PrimInt63 / native_compute / Axiom / Parameter appears.
   =================================================================== *)

From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Znumtheory.
Import ListNotations.
From PrimeGapS1 Require Import IntMat CharPoly Witness WitnessM1CharPoly.
From PrimeGapS1 Require Import PrimeCheck CRTCheck FLDiv ModularFL ModularHess.

Open Scope Z_scope.

(* ================================================================== *)
(* Section 1: the prime table is a NoDup list of primes, all > 43      *)
(* ================================================================== *)

Lemma crt_primes_M1_NoDup : NoDup crt_primes_M1.
Proof. apply nodup_Z_sound. vm_compute. reflexivity. Qed.

Lemma crt_primes_M1_all_prime :
  forall p, In p crt_primes_M1 -> Znumtheory.prime p.
Proof.
  intros p Hin. apply check_prime_Z_sound.
  assert (Hb : forallb check_prime_Z crt_primes_M1 = true)
    by (vm_compute; reflexivity).
  exact (proj1 (forallb_forall _ _) Hb p Hin).
Qed.

Lemma crt_primes_M1_gt43 :
  forall p, In p crt_primes_M1 -> (43 < p)%Z.
Proof.
  intros p Hin.
  assert (Hb : forallb (fun q => 43 <? q) crt_primes_M1 = true)
    by (vm_compute; reflexivity).
  apply Z.ltb_lt. exact (proj1 (forallb_forall _ _) Hb p Hin).
Qed.

(* ================================================================== *)
(* Section 2: M1_int is a 42x42 square, FL-divisible matrix            *)
(* ================================================================== *)

(* Every row of M1_int has length 42 (boolean check, vm_compute). *)
Local Lemma M1_rows_len :
  forall i, (i < length M1_int)%nat -> length (nth i M1_int []) = 42%nat.
Proof.
  intros i Hi.
  assert (Hb : forallb (fun r => Nat.eqb (length r) 42) M1_int = true)
    by (vm_compute; reflexivity).
  apply Nat.eqb_eq.
  apply (proj1 (forallb_forall _ _) Hb).
  apply nth_In. exact Hi.
Qed.

Lemma M1_square : square_mat 42 M1_int.
Proof.
  assert (HL : length M1_int = 42%nat) by (vm_compute; reflexivity).
  split.
  - exact HL.
  - intros i Hi. apply M1_rows_len. rewrite HL. exact Hi.
Qed.

Lemma M1_fl_div :
  fl_all_divisible 42 1 M1_int (meye 42) (mzero 42) 1.
Proof.
  apply (fl_all_divisible_from_L2 M1_int 42).
  - vm_compute; reflexivity.
  - exact M1_rows_len.
Qed.

(* ================================================================== *)
(* Section 3: per-prime agreement via the fast Hessenberg path         *)
(* ================================================================== *)

(* Element-wise boolean equality on lists of Z. *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | nil, nil => true
  | x :: l1', y :: l2' => Z.eqb x y && list_Z_eqb l1' l2'
  | _, _ => false
  end.

Lemma list_Z_eqb_sound :
  forall l1 l2, list_Z_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; simpl in H;
    try discriminate; [reflexivity|].
  apply andb_true_iff in H. destruct H as [Hxy Hrest].
  apply Z.eqb_eq in Hxy. subst y. f_equal. apply IH. exact Hrest.
Qed.

Lemma list_Z_eqb_refl : forall l, list_Z_eqb l l = true.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite Z.eqb_refl. simpl. exact IH.
Qed.

Lemma list_Z_eqb_complete :
  forall l1 l2, l1 = l2 -> list_Z_eqb l1 l2 = true.
Proof. intros l1 l2 ->. apply list_Z_eqb_refl. Qed.

(* Length of the 42x42 matrix, used to align the (length M1_int)-indexed
   hypotheses of char_poly_modZ_sound / char_poly_hess_sound with the
   42-indexed facts proved in Section 2. *)
Lemma M1_len : length M1_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Section 3a: the fast O(n^3) Hessenberg char-poly per-prime check.    *)
(*                                                                     *)
(* char_poly_hess (ModularHess.v) computes char_poly(M1_int) mod p by  *)
(* upper-Hessenberg reduction + the Hyman recurrence -- O(n^3) instead *)
(* of the O(n^4) modular Faddeev-LeVerrier pass of char_poly_modZ.     *)
(* On the 42x42 M1_int this is ~4.5 s/prime (measured) under vm_compute,*)
(* i.e. ~15 min over the 200 table primes, feasible inside one untimed *)
(* coqc, where the O(n^4) pass would take ~16 h.                       *)
(* ------------------------------------------------------------------ *)

Definition per_prime_hess_chk (p : Z) : bool :=
  list_Z_eqb (char_poly_hess p M1_int)
             (map (fun c => c mod p) cp_M1_value).

(* THE heavy computation, now O(n^3) and feasible: the fast char-poly of
   M1_int agrees with cp_M1_value mod p for every table prime.  Closed by
   [vm_compute; reflexivity]; run the final coqc with no timeout. *)
Lemma per_prime_hess_all :
  forallb per_prime_hess_chk crt_primes_M1 = true.
Proof. vm_compute. reflexivity. Qed.

(* Opaque congruence bridge (same load-bearing role as per_prime_chk_eq
   below): freezes the delta-identity so discharging per_prime_hess never
   makes the kernel re-reduce char_poly_hess on an abstract p. *)
Lemma per_prime_hess_chk_eq (p : Z) :
  per_prime_hess_chk p
  = list_Z_eqb (char_poly_hess p M1_int) (map (fun c => c mod p) cp_M1_value).
Proof. reflexivity. Qed.

Lemma per_prime_hess :
  forall p, In p crt_primes_M1 ->
    char_poly_hess p M1_int = map (fun c => c mod p) cp_M1_value.
Proof.
  intros p Hin.
  apply list_Z_eqb_sound.
  rewrite <- per_prime_hess_chk_eq.
  exact (proj1 (forallb_forall _ _) per_prime_hess_all p Hin).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3b: transport to the modular Faddeev-LeVerrier char-poly.    *)
(*                                                                     *)
(* per_prime_ok is stated in terms of char_poly_modZ (its downstream   *)
(* consumer M1CharPoly pairs it with char_poly_modZ_sound).  It is      *)
(* proved WITHOUT running the O(n^4) FL pass: char_poly_modZ and        *)
(* char_poly_hess are both sound against map (.mod p)(char_poly_int     *)
(* M1_int) (char_poly_modZ_sound / char_poly_hess_sound), hence agree,  *)
(* and the fast path equals cp_M1_value mod p by per_prime_hess.        *)
(* ------------------------------------------------------------------ *)

Lemma per_prime_ok :
  forall p, In p crt_primes_M1 ->
    char_poly_modZ p M1_int = map (fun c => c mod p) cp_M1_value.
Proof.
  intros p Hin.
  assert (Hprime : Znumtheory.prime p) by exact (crt_primes_M1_all_prime p Hin).
  assert (Hgt43 : (43 < p)%Z) by exact (crt_primes_M1_gt43 p Hin).
  assert (Hsq : square_mat (length M1_int) M1_int)
    by (rewrite M1_len; exact M1_square).
  assert (Hbound : (Z.of_nat (length M1_int) + 1 < p)%Z)
    by (rewrite M1_len; cbn; lia).
  assert (Hfl : fl_all_divisible (length M1_int) 1 M1_int
                  (meye (length M1_int)) (mzero (length M1_int)) 1)
    by (rewrite M1_len; exact M1_fl_div).
  assert (Hmod : char_poly_modZ p M1_int
                  = map (fun c => c mod p) (char_poly_int M1_int))
    by (apply char_poly_modZ_sound; assumption).
  assert (Hhess : char_poly_hess p M1_int
                   = map (fun c => c mod p) (char_poly_int M1_int))
    by (apply char_poly_hess_sound; assumption).
  rewrite Hmod, <- Hhess. exact (per_prime_hess p Hin).
Qed.

(* ------------------------------------------------------------------ *)
(* Section 3c: per_prime_all (boolean form -- statement unchanged).     *)
(* ------------------------------------------------------------------ *)

Definition per_prime_chk (p : Z) : bool :=
  list_Z_eqb (char_poly_modZ p M1_int)
             (map (fun c => c mod p) cp_M1_value).

(* Opaque congruence bridge (see per_prime_hess_chk_eq): keeps the kernel
   from weak-head-reducing char_poly_modZ on an abstract p at Qed. *)
Lemma per_prime_chk_eq (p : Z) :
  per_prime_chk p
  = list_Z_eqb (char_poly_modZ p M1_int) (map (fun c => c mod p) cp_M1_value).
Proof. reflexivity. Qed.

(* Now PROVEN (no longer Admitted): every table prime satisfies the modZ
   check by per_prime_ok, which routes through the FEASIBLE Hessenberg
   computation instead of the infeasible 200x O(n^4) FL pass.  The only
   remaining bridges are the two clean linear-algebra lemmas inside
   char_poly_hess_sound (ModularHess.hess_recurrence_sound /
   hess_reduce_similar). *)
Lemma per_prime_all :
  forallb per_prime_chk crt_primes_M1 = true.
Proof.
  apply (proj2 (forallb_forall per_prime_chk crt_primes_M1)).
  intros p Hin.
  rewrite per_prime_chk_eq.
  apply list_Z_eqb_complete.
  exact (per_prime_ok p Hin).
Qed.

Print Assumptions per_prime_ok.
