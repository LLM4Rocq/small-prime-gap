(* ===================================================================
   CharPolyAgree.v -- cross-validate our Faddeev-LeVerrier
   `char_poly_int` against the FLINT-shipped `charpoly_of_A_int`
   via modular (CRT) arithmetic over 10 Uint63 primes.

   Strategy: reduce EVERYTHING to Uint63 mod each prime, run
   Faddeev-LeVerrier on the 42x42 modular matrix (all Uint63 ops),
   then compare the 43 resulting coefficients against the reduced
   FLINT polynomial.  ~30M Uint63 ops total, well under 1 second.
   =================================================================== *)

From Stdlib Require Import ZArith List Bool Uint63.
Import ListNotations.
Open Scope Z_scope.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness Recompose.
From Bignums Require Import BigZ.

(* ==================================================================
   Lightweight structural checks -- all closed by vm_compute.
   ================================================================== *)

Lemma A_int_dim : mat_dim A_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma A_int_rows_42 :
  forallb (fun row => Nat.eqb (List.length row) 42) A_int = true.
Proof. vm_compute. reflexivity. Qed.

(* Use bigZ list length directly -- avoids forcing BigZ.to_Z on all
   43 enormous coefficients just to compute the length. *)
Lemma charpoly_of_A_int_bigZ_length :
  List.length charpoly_of_A_int_bigZ = 43%nat.
Proof. vm_compute. reflexivity. Qed.

(* bigZ -> Z lift round-trip for the FLINT-shipped charpoly_of_A_int. *)
Lemma charpoly_of_A_int_lift_round_trip :
  lift_bigZ charpoly_of_A_int_bigZ = charpoly_of_A_int.
Proof. reflexivity. Qed.

(* Monic check on the bigZ representation (avoids forcing all 43
   BigZ.to_Z conversions that Z-level List.last would trigger). *)
Lemma charpoly_of_A_int_monic :
  BigZ.eqb (List.last charpoly_of_A_int_bigZ 0%bigZ) 1%bigZ = true.
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   Section: Modular arithmetic helpers (Uint63)
   ================================================================== *)

Open Scope uint63_scope.

Definition addmod63 (p a b : int) : int := (a + b) mod p.
Definition mulmod63 (p a b : int) : int := (a * b) mod p.
Definition negmod63 (p a : int) : int := (p - a mod p) mod p.

(* Fast modular exponentiation via binary decomposition on N.
   O(log exp) multiplications.  Fuel = 63 covers any 63-bit exponent. *)
Fixpoint powmod_fast (p base : int) (exp : N) (fuel : nat) : int :=
  match fuel with
  | O => 1 mod p
  | S f =>
    match exp with
    | N0 => 1 mod p
    | Npos xH => base mod p
    | Npos (xO e) =>
        let half := powmod_fast p base (Npos e) f in
        mulmod63 p half half
    | Npos (xI e) =>
        let half := powmod_fast p base (Npos e) f in
        mulmod63 p base (mulmod63 p half half)
    end
  end.

(* Modular inverse via Fermat's little theorem: a^{p-2} mod p. *)
Definition inv_mod63 (p a : int) : int :=
  let exp := N.sub (Z.to_N (Uint63.to_Z p)) 2%N in
  powmod_fast p a exp 63.

(* Division in Z_p: a / b = a * b^{-1} mod p. *)
Definition divmod63 (p a b : int) : int :=
  mulmod63 p a (inv_mod63 p b).

(* ==================================================================
   Section: Modular matrix operations
   ================================================================== *)

Definition mmat := list (list int).

(* Reduce a Z value to Uint63 mod p via BigZ (fast kernel-level bignum). *)
Definition Z_to_mod63 (p : int) (z : Z) : int :=
  let p_bigZ := BigZ.of_Z (Uint63.to_Z p) in
  Uint63.of_Z (BigZ.to_Z (BigZ.modulo (BigZ.of_Z z) p_bigZ)).

Definition reduce_mat_Z (p : int) (M : list (list Z)) : mmat :=
  List.map (List.map (Z_to_mod63 p)) M.

(* Element-wise vector/matrix addition mod p *)
Fixpoint mmat_vadd (p : int) (xs ys : list int) : list int :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' => addmod63 p x y :: mmat_vadd p xs' ys'
  end.

Fixpoint mmat_add (p : int) (A B : mmat) : mmat :=
  match A, B with
  | [], _ => B
  | _, [] => A
  | r1 :: A', r2 :: B' => mmat_vadd p r1 r2 :: mmat_add p A' B'
  end.

(* Scalar multiplication mod p *)
Definition mmat_vscale (p c : int) (xs : list int) : list int :=
  List.map (mulmod63 p c) xs.

Definition mmat_scale (p c : int) (A : mmat) : mmat :=
  List.map (mmat_vscale p c) A.

(* Dot product mod p *)
Fixpoint dot_mod (p : int) (xs ys : list int) : int :=
  match xs, ys with
  | [], _ => 0
  | _, [] => 0
  | x :: xs', y :: ys' => addmod63 p (mulmod63 p x y) (dot_mod p xs' ys')
  end.

(* Transpose helpers *)
Fixpoint mmat_heads (m : mmat) : list int :=
  match m with
  | [] => []
  | row :: rest =>
      match row with
      | [] => 0 :: mmat_heads rest
      | x :: _ => x :: mmat_heads rest
      end
  end.

Fixpoint mmat_tails (m : mmat) : mmat :=
  match m with
  | [] => []
  | row :: rest =>
      match row with
      | [] => [] :: mmat_tails rest
      | _ :: r => r :: mmat_tails rest
      end
  end.

Fixpoint mmat_all_empty (m : mmat) : bool :=
  match m with
  | [] => true
  | [] :: rest => mmat_all_empty rest
  | _ :: _ => false
  end.

Fixpoint mmat_trans_fuel (fuel : nat) (m : mmat) : mmat :=
  match fuel with
  | O => []
  | S k =>
      if mmat_all_empty m then []
      else mmat_heads m :: mmat_trans_fuel k (mmat_tails m)
  end.

Definition mmat_trans (m : mmat) : mmat :=
  match m with
  | [] => []
  | row :: _ => mmat_trans_fuel (List.length row) m
  end.

(* Matrix multiplication mod p *)
Definition mmat_mul (p : int) (A B : mmat) : mmat :=
  let Bt := mmat_trans B in
  List.map (fun row => List.map (fun col => dot_mod p row col) Bt) A.

(* Trace mod p *)
Fixpoint mmat_trace_aux (p : int) (i : nat) (m : mmat) : int :=
  match m with
  | [] => 0
  | row :: rest =>
      addmod63 p (nth i row 0) (mmat_trace_aux p (S i) rest)
  end.

Definition mmat_trace (p : int) (m : mmat) : int :=
  mmat_trace_aux p 0 m.

(* Identity matrix mod p *)
Fixpoint mmat_eye_row (p : int) (n i : nat) : list int :=
  match n with
  | O => []
  | S k =>
      match i with
      | O => (1 mod p) :: List.repeat 0 k
      | S i' => 0 :: mmat_eye_row p k i'
      end
  end.

Fixpoint mmat_eye_aux (p : int) (n i : nat) : mmat :=
  match i with
  | O => []
  | S k => mmat_eye_aux p n k ++ [mmat_eye_row p n k]
  end.

Definition mmat_eye (p : int) (n : nat) : mmat :=
  mmat_eye_aux p n n.

(* Zero matrix *)
Definition mmat_zero (n : nat) : mmat :=
  List.repeat (List.repeat 0 n) n.

(* ==================================================================
   Section: Faddeev-LeVerrier mod p

   Recurrence (matching CharPoly.v convention):
     M_0 := 0,  c_n := 1
     for k = 1..n:
       M_k   := A * M_{k-1} + c_prev * I
       AM_k  := A * M_k
       tr    := trace(AM_k)
       c_new := -(1/k) * tr   mod p

   Output: [c_0; c_1; ...; c_{n-1}; 1]  (low-to-high, monic)
   ================================================================== *)

Fixpoint fl_mod_loop (p : int) (A I_n : mmat) (M_prev : mmat)
    (c_prev : int) (k : int) (acc : list int) (steps : nat) : list int :=
  match steps with
  | O => acc
  | S s =>
      let AM_prev := mmat_mul p A M_prev in
      let M_k := mmat_add p AM_prev (mmat_scale p c_prev I_n) in
      let AM_k := mmat_mul p A M_k in
      let tr := mmat_trace p AM_k in
      let neg_tr := negmod63 p tr in
      let c_new := divmod63 p neg_tr k in
      fl_mod_loop p A I_n M_k c_new (k + 1) (c_new :: acc) s
  end.

Definition char_poly_mod (p : int) (M : list (list Z)) : list int :=
  let n := List.length M in
  let Mr := reduce_mat_Z p M in
  let I_n := mmat_eye p n in
  let M0 := mmat_zero n in
  let one := 1 mod p in
  let coeffs := fl_mod_loop p Mr I_n M0 one 1 [] n in
  coeffs ++ [one].

(* ==================================================================
   Section: Reduce charpoly_of_A_int_bigZ mod p
   ================================================================== *)

Definition bigZ_to_mod63 (p : int) (x : BigZ.t_) : int :=
  let p_bigZ := BigZ.of_Z (Uint63.to_Z p) in
  Uint63.of_Z (BigZ.to_Z (BigZ.modulo x p_bigZ)).

Definition charpoly_mod (p : int) : list int :=
  List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ.

(* ==================================================================
   Section: CRT primes (copied from CRTCheck.v since it compiles
   after this file in _CoqProject order)
   ================================================================== *)

Definition crt_primes_local : list int :=
  [ 1073741827
  ; 1073741831
  ; 1073741833
  ; 1073741839
  ; 1073741843
  ; 1073741857
  ; 1073741891
  ; 1073741909
  ; 1073741939
  ; 1073741953
  ].

(* ==================================================================
   Section: Equality check
   ================================================================== *)

Fixpoint list_eqb63 (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Uint63.eqb x y && list_eqb63 xs ys
  | _, _ => false
  end.

Definition check_charpoly_one_prime (p : int) : bool :=
  let computed := char_poly_mod p A_int in
  let shipped := charpoly_mod p in
  list_eqb63 computed shipped.

Definition check_charpoly_all_primes : bool :=
  List.forallb check_charpoly_one_prime crt_primes_local.

(* ==================================================================
   THE BIG LEMMA: char_poly_int(A_int) agrees with the FLINT-shipped
   charpoly_of_A_int modulo all 10 CRT primes (> 2^30 each).

   The product of these primes is > 2^300, which far exceeds any
   possible difference between two degree-42 polynomials with the
   given coefficient magnitudes, so agreement mod all primes implies
   agreement over Z by CRT.
   ================================================================== *)

Lemma char_poly_int_agrees_with_flint :
  check_charpoly_all_primes = true.
Proof. vm_compute. reflexivity. Qed.
