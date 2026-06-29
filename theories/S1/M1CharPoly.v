(**md*** M1CharPoly: char_poly(M1_int) = cp_M1_value via CRT ***)

(* ===================================================================
   M1CharPoly.v -- the integer characteristic-polynomial identity for
   the 42x42 witness matrix M1_int, certified by CRT over Stdlib's Z.

   Two results are exported:

     char_poly_int_M1_eq : char_poly_int M1_int = cp_M1_value
     cp_M1_alternates    : alternating_signs cp_M1_value = true
                           /\ 0 < nth 0 cp_M1_value 0
                           /\ 0 < last cp_M1_value 0

   The first is proved coefficient-by-coefficient (both lists have
   length 43).  For each index k and each prime p of the table
   crt_primes_M1, the two k-th coefficients are congruent mod p,
   because (a) ModularFL.char_poly_modZ_sound -- fed
   CRTFrame.M1_square / M1_fl_div / crt_primes_M1_all_prime /
   crt_primes_M1_gt43 -- gives
       char_poly_modZ p M1_int = map (.mod p) (char_poly_int M1_int)
   and (b) CRTFrame.per_prime_ok gives
       char_poly_modZ p M1_int = map (.mod p) cp_M1_value.
   The Hadamard-style coefficient bound from Bound
   (char_poly_int_coeff_bound) together with a single vm_compute
   check that 4 * fl_coeff_bound 42 (max_abs_entry M1_int) is below
   the product of the table primes lets CRTCheck.crt_reconstruct
   collapse the congruences into an honest equality over Z.

   The second result records that the coefficients of cp_M1_value
   strictly alternate in sign with positive constant and leading
   terms -- the integer shadow of M1 being positive definite (all
   eigenvalues real and > 0).

   No Uint63 / PrimInt63 / native_compute / Axiom / Parameter appears;
   the only nonstandard assumption inherited is CRTFrame.per_prime_all
   (a TODO-BRIDGE vm_compute upstream).
   =================================================================== *)

From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Znumtheory.
Import ListNotations.
From PrimeGapS1 Require Import IntMat CharPoly Witness WitnessM1CharPoly.
From PrimeGapS1 Require Import CRTCheck ModularFL Bound CRTFrame FLDiv.

Open Scope Z_scope.

(* ================================================================== *)
(* Section 1: structural facts about M1_int                            *)
(* ================================================================== *)

Local Lemma M1_len : length M1_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Local Lemma M1_rows :
  forall i, (i < length M1_int)%nat -> length (nth i M1_int []) = length M1_int.
Proof.
  intros i Hi.
  assert (Hb : forallb (fun r => Nat.eqb (length r) 42) M1_int = true)
    by (vm_compute; reflexivity).
  rewrite M1_len. apply Nat.eqb_eq.
  apply (proj1 (forallb_forall _ _) Hb). apply nth_In. exact Hi.
Qed.

(* ================================================================== *)
(* Section 2: the coefficient bound and that cp_M1_value respects it   *)
(* ================================================================== *)

(* Hadamard-style bound on every coefficient of char_poly_int M1_int. *)
Local Definition cp_bound : Z :=
  fl_coeff_bound (length M1_int) (max_abs_entry M1_int).

Local Lemma cp_bound_nonneg : 0 <= cp_bound.
Proof. rewrite <- Z.leb_le. vm_compute. reflexivity. Qed.

(* Every coefficient of the claimed polynomial is within the bound. *)
Local Lemma cp_coeff_bound (k : nat) :
  Z.abs (nth k cp_M1_value 0) <= cp_bound.
Proof.
  destruct (Nat.lt_ge_cases k (length cp_M1_value)) as [Hk|Hk].
  - assert (Hb : forallb (fun x => Z.abs x <=? cp_bound) cp_M1_value = true)
      by (vm_compute; reflexivity).
    apply Z.leb_le.
    apply (proj1 (forallb_forall _ _) Hb (nth k cp_M1_value 0) (nth_In _ _ Hk)).
  - rewrite nth_overflow by exact Hk. exact cp_bound_nonneg.
Qed.

(* ================================================================== *)
(* Section 3: modular-arithmetic glue                                  *)
(* ================================================================== *)

Local Lemma mod_eq_divide (a b p : Z) :
  p <> 0 -> a mod p = b mod p -> (p | a - b).
Proof.
  intros Hp Heq. apply Z.mod_divide; [exact Hp|].
  rewrite Zminus_mod, Heq, Z.sub_diag. apply Z.mod_0_l; exact Hp.
Qed.

Local Lemma nth_map_eq_mod (l1 l2 : list Z) (p : Z) (k : nat) :
  map (fun c => c mod p) l1 = map (fun c => c mod p) l2 ->
  (nth k l1 0) mod p = (nth k l2 0) mod p.
Proof.
  intro H.
  rewrite <- (map_nth (fun c => c mod p) l1 0 k).
  rewrite <- (map_nth (fun c => c mod p) l2 0 k).
  rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(* Section 4: per-prime divisibility of the coefficient difference     *)
(* ================================================================== *)

Local Lemma coeff_div (k : nat) (p : Z) :
  In p crt_primes_M1 ->
  (p | nth k (char_poly_int M1_int) 0 - nth k cp_M1_value 0).
Proof.
  intros Hin.
  assert (Hp0 : p <> 0).
  { pose proof (crt_primes_M1_gt43 p Hin). lia. }
  assert (Hsound : char_poly_modZ p M1_int
                    = map (fun c => c mod p) (char_poly_int M1_int)).
  { apply char_poly_modZ_sound.
    - exact (crt_primes_M1_all_prime p Hin).
    - rewrite M1_len. exact M1_square.
    - pose proof (crt_primes_M1_gt43 p Hin). rewrite M1_len. lia.
    - rewrite M1_len. exact M1_fl_div. }
  assert (Hframe : char_poly_modZ p M1_int
                    = map (fun c => c mod p) cp_M1_value)
    by exact (per_prime_ok p Hin).
  assert (Heq : map (fun c => c mod p) (char_poly_int M1_int)
                 = map (fun c => c mod p) cp_M1_value).
  { rewrite <- Hsound. exact Hframe. }
  apply mod_eq_divide; [exact Hp0|].
  apply nth_map_eq_mod. exact Heq.
Qed.

(* ================================================================== *)
(* Section 5: CRT reconstruction, coefficient by coefficient           *)
(* ================================================================== *)

Local Lemma coeff_eq (k : nat) :
  nth k (char_poly_int M1_int) 0 = nth k cp_M1_value 0.
Proof.
  apply (crt_reconstruct _ _ crt_primes_M1).
  - exact crt_primes_M1_NoDup.
  - exact crt_primes_M1_all_prime.
  - intros p Hin. exact (coeff_div k p Hin).
  - assert (Hc : Z.abs (nth k (char_poly_int M1_int) 0) <= cp_bound).
    { unfold cp_bound. exact (char_poly_int_coeff_bound M1_int M1_rows k). }
    pose proof (cp_coeff_bound k) as Hd.
    assert (Hb4 : 4 * cp_bound < fold_left Z.mul crt_primes_M1 1)
      by (rewrite <- Z.ltb_lt; vm_compute; reflexivity).
    lia.
Qed.

(* ================================================================== *)
(* Section 6: the main identity                                         *)
(* ================================================================== *)

Theorem char_poly_int_M1_eq : char_poly_int M1_int = cp_M1_value.
Proof.
  apply (nth_ext _ _ 0 0).
  - assert (Hl : length cp_M1_value = 43%nat) by (vm_compute; reflexivity).
    rewrite Hl, length_char_poly_int_gen.
    unfold mat_dim. rewrite M1_len. reflexivity.
  - intros k Hk. exact (coeff_eq k).
Qed.

(* ================================================================== *)
(* Section 7: strict sign alternation of the coefficients              *)
(* ================================================================== *)

(* Adjacent coefficients have strictly opposite signs (their product is
   negative); a degree-42 monic char-poly of a positive-definite matrix
   factors as prod (x - lambda_i) with all lambda_i > 0. *)
Fixpoint alternating_signs (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: rest =>
      match rest with
      | [] => true
      | y :: _ => (x * y <? 0) && alternating_signs rest
      end
  end.

Theorem cp_M1_alternates :
  alternating_signs cp_M1_value = true
  /\ 0 < nth 0 cp_M1_value 0
  /\ 0 < last cp_M1_value 0.
Proof.
  split; [|split].
  - vm_compute. reflexivity.
  - rewrite <- Z.ltb_lt. vm_compute. reflexivity.
  - rewrite <- Z.ltb_lt. vm_compute. reflexivity.
Qed.
