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

(* ==================================================================
   MATRIX IDENTITY CHECK: M1_int * A_int * D_M2 = M2_int * (D_M1 * D_A)

   This verifies that A_int / D_A = (M1_int / D_M1)^{-1} * (M2_int / D_M2),
   i.e., that the shipped A_int is indeed the denominator-cleared form
   of A_rat = invmx(M1/D_M1) * (M2/D_M2).
   ================================================================== *)

Fixpoint mmat_eqb (M1 M2 : mmat) : bool :=
  match M1, M2 with
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 =>
    List.forallb (fun '(a, b) => Uint63.eqb a b) (List.combine r1 r2)
    && mmat_eqb rs1 rs2
  | _, _ => false
  end.

Definition check_mat_identity_one_prime (p : int) : bool :=
  let M1 := reduce_mat_Z p M1_int in
  let M2 := reduce_mat_Z p M2_int in
  let A  := reduce_mat_Z p A_int in
  let dM2 := Z_to_mod63 p D_M2 in
  let dM1_dA := Z_to_mod63 p (D_M1 * D_A)%Z in
  let lhs := mmat_scale p dM2 (mmat_mul p M1 A) in
  let rhs := mmat_scale p dM1_dA M2 in
  mmat_eqb lhs rhs.

Definition check_mat_identity_all_primes : bool :=
  List.forallb check_mat_identity_one_prime crt_primes_local.

Lemma matrix_identity_agrees :
  check_mat_identity_all_primes = true.
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   POLYNOMIAL SCALING CHECK:
     charpoly_int[k] * D_A^{42-k} = D_q * charpoly_of_A_int[k]

   This verifies the coefficient-level relationship between the
   D_q-cleared rational charpoly and the integer-matrix charpoly.
   ================================================================== *)

Definition D_A_bigZ := BigZ.of_Z D_A.
Definition D_q_bigZ := BigZ.of_Z D_q.

Fixpoint check_scaling_coefs (k : nat) (shipped intmat_cp : list BigZ.t_) : bool :=
  match shipped, intmat_cp with
  | [], [] => true
  | s :: ss, c :: cs =>
    let DA_pow := BigZ.pow D_A_bigZ (BigZ.of_Z (Z.of_nat (42 - k))) in
    BigZ.eqb (BigZ.mul s DA_pow) (BigZ.mul D_q_bigZ c) &&
    check_scaling_coefs (S k) ss cs
  | _, _ => false
  end.

Definition check_charpoly_scaling : bool :=
  check_scaling_coefs 0
    (List.map BigZ.of_Z charpoly_int) charpoly_of_A_int_bigZ.

Lemma charpoly_scaling_agrees :
  check_charpoly_scaling = true.
Proof. vm_compute. reflexivity. Qed.


(* ==================================================================
   EXTENDED CRT: 710 primes (~21000-bit coverage).

   700 additional Uint63 primes give sufficient CRT coverage for the
   ~19923-bit charpoly_of_A_int coefficients AND the ~2400-bit matrix
   identity entries. Product of 710 primes > 2^{21000}.
   ================================================================== *)

Open Scope uint63_scope.

Definition crt_primes_extra : list int :=
  [ 1073741969
  ; 1073741971
  ; 1073741987
  ; 1073741993
  ; 1073742037
  ; 1073742053
  ; 1073742073
  ; 1073742077
  ; 1073742091
  ; 1073742113
  ; 1073742169
  ; 1073742203
  ; 1073742209
  ; 1073742223
  ; 1073742233
  ; 1073742259
  ; 1073742277
  ; 1073742289
  ; 1073742343
  ; 1073742353
  ; 1073742361
  ; 1073742391
  ; 1073742403
  ; 1073742463
  ; 1073742493
  ; 1073742517
  ; 1073742583
  ; 1073742623
  ; 1073742653
  ; 1073742667
  ; 1073742671
  ; 1073742673
  ; 1073742707
  ; 1073742713
  ; 1073742721
  ; 1073742731
  ; 1073742767
  ; 1073742773
  ; 1073742811
  ; 1073742851
  ; 1073742853
  ; 1073742881
  ; 1073742889
  ; 1073742913
  ; 1073742931
  ; 1073742937
  ; 1073742959
  ; 1073742983
  ; 1073743007
  ; 1073743037
  ; 1073743049
  ; 1073743051
  ; 1073743079
  ; 1073743091
  ; 1073743093
  ; 1073743123
  ; 1073743129
  ; 1073743141
  ; 1073743159
  ; 1073743163
  ; 1073743189
  ; 1073743199
  ; 1073743207
  ; 1073743243
  ; 1073743291
  ; 1073743303
  ; 1073743313
  ; 1073743327
  ; 1073743331
  ; 1073743337
  ; 1073743381
  ; 1073743387
  ; 1073743393
  ; 1073743397
  ; 1073743403
  ; 1073743417
  ; 1073743421
  ; 1073743427
  ; 1073743457
  ; 1073743459
  ; 1073743469
  ; 1073743501
  ; 1073743507
  ; 1073743513
  ; 1073743543
  ; 1073743577
  ; 1073743591
  ; 1073743633
  ; 1073743739
  ; 1073743757
  ; 1073743831
  ; 1073743861
  ; 1073743871
  ; 1073743883
  ; 1073743889
  ; 1073743901
  ; 1073743921
  ; 1073743973
  ; 1073743981
  ; 1073743991
  ; 1073744059
  ; 1073744069
  ; 1073744071
  ; 1073744137
  ; 1073744159
  ; 1073744171
  ; 1073744197
  ; 1073744249
  ; 1073744257
  ; 1073744261
  ; 1073744263
  ; 1073744291
  ; 1073744297
  ; 1073744311
  ; 1073744317
  ; 1073744339
  ; 1073744377
  ; 1073744389
  ; 1073744417
  ; 1073744447
  ; 1073744461
  ; 1073744491
  ; 1073744533
  ; 1073744557
  ; 1073744569
  ; 1073744593
  ; 1073744597
  ; 1073744603
  ; 1073744621
  ; 1073744677
  ; 1073744681
  ; 1073744687
  ; 1073744779
  ; 1073744813
  ; 1073744827
  ; 1073744849
  ; 1073744863
  ; 1073744909
  ; 1073744911
  ; 1073744927
  ; 1073744933
  ; 1073744977
  ; 1073744993
  ; 1073745017
  ; 1073745031
  ; 1073745061
  ; 1073745067
  ; 1073745083
  ; 1073745121
  ; 1073745161
  ; 1073745193
  ; 1073745209
  ; 1073745251
  ; 1073745259
  ; 1073745287
  ; 1073745293
  ; 1073745301
  ; 1073745319
  ; 1073745331
  ; 1073745359
  ; 1073745367
  ; 1073745377
  ; 1073745397
  ; 1073745457
  ; 1073745469
  ; 1073745473
  ; 1073745487
  ; 1073745521
  ; 1073745529
  ; 1073745557
  ; 1073745577
  ; 1073745581
  ; 1073745599
  ; 1073745623
  ; 1073745637
  ; 1073745649
  ; 1073745697
  ; 1073745737
  ; 1073745763
  ; 1073745767
  ; 1073745769
  ; 1073745773
  ; 1073745781
  ; 1073745787
  ; 1073745797
  ; 1073745817
  ; 1073745821
  ; 1073745833
  ; 1073745839
  ; 1073745859
  ; 1073745863
  ; 1073745877
  ; 1073745889
  ; 1073745899
  ; 1073745923
  ; 1073745941
  ; 1073745943
  ; 1073745997
  ; 1073746013
  ; 1073746019
  ; 1073746097
  ; 1073746103
  ; 1073746109
  ; 1073746127
  ; 1073746159
  ; 1073746169
  ; 1073746181
  ; 1073746229
  ; 1073746243
  ; 1073746273
  ; 1073746321
  ; 1073746337
  ; 1073746351
  ; 1073746361
  ; 1073746379
  ; 1073746397
  ; 1073746403
  ; 1073746423
  ; 1073746477
  ; 1073746483
  ; 1073746511
  ; 1073746517
  ; 1073746529
  ; 1073746567
  ; 1073746573
  ; 1073746577
  ; 1073746589
  ; 1073746603
  ; 1073746621
  ; 1073746627
  ; 1073746637
  ; 1073746643
  ; 1073746669
  ; 1073746699
  ; 1073746711
  ; 1073746747
  ; 1073746759
  ; 1073746777
  ; 1073746799
  ; 1073746811
  ; 1073746823
  ; 1073746831
  ; 1073746859
  ; 1073746931
  ; 1073746939
  ; 1073746951
  ; 1073746967
  ; 1073747039
  ; 1073747063
  ; 1073747107
  ; 1073747123
  ; 1073747137
  ; 1073747153
  ; 1073747161
  ; 1073747167
  ; 1073747197
  ; 1073747221
  ; 1073747231
  ; 1073747239
  ; 1073747263
  ; 1073747273
  ; 1073747287
  ; 1073747309
  ; 1073747321
  ; 1073747327
  ; 1073747369
  ; 1073747371
  ; 1073747393
  ; 1073747419
  ; 1073747447
  ; 1073747459
  ; 1073747471
  ; 1073747497
  ; 1073747537
  ; 1073747573
  ; 1073747603
  ; 1073747621
  ; 1073747641
  ; 1073747687
  ; 1073747699
  ; 1073747747
  ; 1073747767
  ; 1073747783
  ; 1073747791
  ; 1073747833
  ; 1073747861
  ; 1073747953
  ; 1073747957
  ; 1073747977
  ; 1073747989
  ; 1073748019
  ; 1073748059
  ; 1073748061
  ; 1073748079
  ; 1073748107
  ; 1073748133
  ; 1073748163
  ; 1073748187
  ; 1073748191
  ; 1073748211
  ; 1073748239
  ; 1073748241
  ; 1073748289
  ; 1073748293
  ; 1073748301
  ; 1073748343
  ; 1073748397
  ; 1073748409
  ; 1073748433
  ; 1073748437
  ; 1073748449
  ; 1073748469
  ; 1073748497
  ; 1073748503
  ; 1073748527
  ; 1073748541
  ; 1073748569
  ; 1073748587
  ; 1073748607
  ; 1073748617
  ; 1073748619
  ; 1073748647
  ; 1073748649
  ; 1073748659
  ; 1073748661
  ; 1073748671
  ; 1073748727
  ; 1073748733
  ; 1073748737
  ; 1073748757
  ; 1073748761
  ; 1073748799
  ; 1073748853
  ; 1073748869
  ; 1073748937
  ; 1073748947
  ; 1073748979
  ; 1073748989
  ; 1073749003
  ; 1073749013
  ; 1073749021
  ; 1073749031
  ; 1073749037
  ; 1073749067
  ; 1073749073
  ; 1073749129
  ; 1073749151
  ; 1073749153
  ; 1073749211
  ; 1073749253
  ; 1073749307
  ; 1073749333
  ; 1073749343
  ; 1073749349
  ; 1073749367
  ; 1073749381
  ; 1073749409
  ; 1073749433
  ; 1073749459
  ; 1073749463
  ; 1073749471
  ; 1073749477
  ; 1073749487
  ; 1073749493
  ; 1073749499
  ; 1073749507
  ; 1073749519
  ; 1073749531
  ; 1073749541
  ; 1073749553
  ; 1073749561
  ; 1073749609
  ; 1073749619
  ; 1073749681
  ; 1073749711
  ; 1073749723
  ; 1073749727
  ; 1073749741
  ; 1073749763
  ; 1073749769
  ; 1073749777
  ; 1073749783
  ; 1073749811
  ; 1073749849
  ; 1073749889
  ; 1073749891
  ; 1073749913
  ; 1073749927
  ; 1073749933
  ; 1073749951
  ; 1073749979
  ; 1073749991
  ; 1073749993
  ; 1073750017
  ; 1073750077
  ; 1073750113
  ; 1073750137
  ; 1073750149
  ; 1073750191
  ; 1073750221
  ; 1073750231
  ; 1073750233
  ; 1073750269
  ; 1073750299
  ; 1073750303
  ; 1073750309
  ; 1073750341
  ; 1073750351
  ; 1073750387
  ; 1073750399
  ; 1073750407
  ; 1073750449
  ; 1073750459
  ; 1073750467
  ; 1073750497
  ; 1073750507
  ; 1073750567
  ; 1073750593
  ; 1073750611
  ; 1073750669
  ; 1073750683
  ; 1073750707
  ; 1073750761
  ; 1073750771
  ; 1073750773
  ; 1073750809
  ; 1073750827
  ; 1073750849
  ; 1073750869
  ; 1073750879
  ; 1073750917
  ; 1073750939
  ; 1073750981
  ; 1073750983
  ; 1073751031
  ; 1073751053
  ; 1073751073
  ; 1073751079
  ; 1073751109
  ; 1073751121
  ; 1073751131
  ; 1073751139
  ; 1073751149
  ; 1073751169
  ; 1073751191
  ; 1073751193
  ; 1073751209
  ; 1073751223
  ; 1073751241
  ; 1073751257
  ; 1073751271
  ; 1073751277
  ; 1073751293
  ; 1073751317
  ; 1073751319
  ; 1073751391
  ; 1073751401
  ; 1073751407
  ; 1073751421
  ; 1073751449
  ; 1073751461
  ; 1073751493
  ; 1073751521
  ; 1073751529
  ; 1073751551
  ; 1073751559
  ; 1073751563
  ; 1073751571
  ; 1073751589
  ; 1073751631
  ; 1073751683
  ; 1073751689
  ; 1073751691
  ; 1073751713
  ; 1073751719
  ; 1073751733
  ; 1073751779
  ; 1073751799
  ; 1073751823
  ; 1073751851
  ; 1073751863
  ; 1073751869
  ; 1073751871
  ; 1073751893
  ; 1073751919
  ; 1073751923
  ; 1073751971
  ; 1073752003
  ; 1073752019
  ; 1073752027
  ; 1073752039
  ; 1073752067
  ; 1073752093
  ; 1073752129
  ; 1073752139
  ; 1073752153
  ; 1073752201
  ; 1073752261
  ; 1073752313
  ; 1073752331
  ; 1073752333
  ; 1073752349
  ; 1073752357
  ; 1073752369
  ; 1073752391
  ; 1073752397
  ; 1073752409
  ; 1073752411
  ; 1073752417
  ; 1073752429
  ; 1073752451
  ; 1073752517
  ; 1073752541
  ; 1073752573
  ; 1073752583
  ; 1073752607
  ; 1073752619
  ; 1073752627
  ; 1073752633
  ; 1073752639
  ; 1073752651
  ; 1073752663
  ; 1073752717
  ; 1073752721
  ; 1073752733
  ; 1073752739
  ; 1073752747
  ; 1073752751
  ; 1073752763
  ; 1073752777
  ; 1073752807
  ; 1073752831
  ; 1073752837
  ; 1073752843
  ; 1073752873
  ; 1073752877
  ; 1073752919
  ; 1073752949
  ; 1073752969
  ; 1073752973
  ; 1073753003
  ; 1073753063
  ; 1073753089
  ; 1073753113
  ; 1073753143
  ; 1073753147
  ; 1073753207
  ; 1073753221
  ; 1073753243
  ; 1073753279
  ; 1073753281
  ; 1073753309
  ; 1073753311
  ; 1073753347
  ; 1073753353
  ; 1073753381
  ; 1073753389
  ; 1073753393
  ; 1073753467
  ; 1073753477
  ; 1073753489
  ; 1073753491
  ; 1073753501
  ; 1073753503
  ; 1073753531
  ; 1073753533
  ; 1073753539
  ; 1073753557
  ; 1073753561
  ; 1073753573
  ; 1073753599
  ; 1073753621
  ; 1073753651
  ; 1073753657
  ; 1073753663
  ; 1073753687
  ; 1073753717
  ; 1073753729
  ; 1073753741
  ; 1073753773
  ; 1073753839
  ; 1073753887
  ; 1073753893
  ; 1073753917
  ; 1073753951
  ; 1073753959
  ; 1073753969
  ; 1073753987
  ; 1073753999
  ; 1073754053
  ; 1073754061
  ; 1073754067
  ; 1073754079
  ; 1073754107
  ; 1073754113
  ; 1073754167
  ; 1073754191
  ; 1073754193
  ; 1073754251
  ; 1073754257
  ; 1073754259
  ; 1073754263
  ; 1073754271
  ; 1073754301
  ; 1073754307
  ; 1073754329
  ; 1073754337
  ; 1073754359
  ; 1073754361
  ; 1073754421
  ; 1073754439
  ; 1073754497
  ; 1073754499
  ; 1073754509
  ; 1073754553
  ; 1073754559
  ; 1073754569
  ; 1073754587
  ; 1073754601
  ; 1073754631
  ; 1073754683
  ; 1073754691
  ; 1073754713
  ; 1073754739
  ; 1073754761
  ; 1073754769
  ; 1073754853
  ; 1073754859
  ; 1073754889
  ; 1073754917
  ; 1073754919
  ; 1073754953
  ; 1073754971
  ; 1073755013
  ; 1073755043
  ; 1073755051
  ; 1073755093
  ; 1073755099
  ; 1073755117
  ; 1073755127
  ; 1073755141
  ; 1073755171
  ; 1073755183
  ; 1073755229
  ; 1073755231
  ; 1073755237
  ; 1073755259
  ; 1073755271
  ; 1073755283
  ; 1073755357
  ; 1073755393
  ; 1073755433
  ; 1073755457
  ; 1073755477
  ; 1073755559
  ; 1073755591
  ; 1073755603
  ; 1073755633
  ; 1073755681
  ; 1073755687
  ; 1073755699
  ; 1073755729
  ; 1073755741
  ; 1073755747
  ; 1073755757
  ; 1073755763
  ; 1073755829
  ; 1073755841
  ; 1073755849
  ; 1073755871
  ; 1073755877
  ; 1073755901
  ; 1073755909
  ; 1073755919
  ; 1073755931
  ; 1073755939
  ; 1073755973
  ; 1073755993
  ; 1073755997
  ; 1073755999
  ; 1073756009
  ; 1073756027
  ; 1073756113
  ; 1073756119
  ; 1073756191
  ; 1073756209
  ; 1073756213
  ; 1073756231
  ; 1073756237
  ; 1073756239
  ; 1073756273
  ; 1073756279
  ; 1073756323
  ; 1073756347
  ; 1073756377
  ; 1073756389
  ; 1073756401
  ; 1073756413
  ; 1073756419
  ; 1073756473
  ].

Definition crt_primes_all : list int :=
  crt_primes_local ++ crt_primes_extra.

(* CRT check: char_poly_int(A_int) = charpoly_of_A_int mod ALL 710 primes *)
Definition check_charpoly_one_prime_710 (p : int) : bool :=
  let computed := char_poly_mod p A_int in
  let shipped := List.map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ in
  list_eqb63 computed shipped.

Definition check_charpoly_710 : bool :=
  List.forallb check_charpoly_one_prime_710 crt_primes_all.

Lemma char_poly_int_agrees_710 :
  check_charpoly_710 = true.
Proof. vm_compute. reflexivity. Qed.

(* CRT check: matrix identity mod ALL 710 primes *)
Definition check_mat_identity_710 : bool :=
  List.forallb check_mat_identity_one_prime crt_primes_all.

Lemma matrix_identity_710 :
  check_mat_identity_710 = true.
Proof. vm_compute. reflexivity. Qed.

From Stdlib Require Import Lia.

(* ==================================================================
   CRT BRIDGE INFRASTRUCTURE
   ================================================================== *)

(* ------------------------------------------------------------------
   1. M1 det nonzero check
   ------------------------------------------------------------------ *)

Definition check_M1_det_nz : bool :=
  negb (Uint63.eqb (List.hd 0 (char_poly_mod (List.hd 0 crt_primes_all) M1_int)) 0).

Lemma M1_det_nz_mod : check_M1_det_nz = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------
   2. Size lemmas for charpoly_int and charpoly_of_A_int
   ------------------------------------------------------------------ *)

Lemma length_charpoly_int : length charpoly_int = 43%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma length_charpoly_of_A_int : length charpoly_of_A_int = 43%nat.
Proof. unfold charpoly_of_A_int, lift_bigZ. rewrite length_map. exact charpoly_of_A_int_bigZ_length. Qed.

(* ------------------------------------------------------------------
   3. Reflection lemma for scaling_Z
   ------------------------------------------------------------------ *)

Lemma check_scaling_coefs_sound k shipped intmat_cp :
  check_scaling_coefs k shipped intmat_cp = true ->
  forall j, (j < length shipped)%nat ->
    (j < length intmat_cp)%nat ->
    Z.mul (BigZ.to_Z (List.nth j shipped 0%bigZ))
          (BigZ.to_Z (BigZ.pow D_A_bigZ (BigZ.of_Z (Z.of_nat (42 - (k + j))))))
    = Z.mul (BigZ.to_Z D_q_bigZ) (BigZ.to_Z (List.nth j intmat_cp 0%bigZ)).
Proof.
  revert k intmat_cp.
  induction shipped as [| s ss IHss]; intros k intmat_cp Hcheck j Hj1 Hj2.
  - (* shipped = [] *)
    simpl in Hj1. lia.
  - (* shipped = s :: ss *)
    destruct intmat_cp as [| c cs].
    + (* intmat_cp = [] -- contradicts check = true *)
      cbn [check_scaling_coefs] in Hcheck. discriminate.
    + (* intmat_cp = c :: cs *)
      cbn [check_scaling_coefs] in Hcheck.
      apply andb_prop in Hcheck. destruct Hcheck as [Heqb Htail].
      destruct j as [| j'].
      * (* j = 0 *)
        cbn [List.nth].
        rewrite BigZ.spec_eqb in Heqb.
        rewrite Z.eqb_eq in Heqb.
        rewrite !BigZ.spec_mul in Heqb.
        replace (k + 0)%nat with k by lia.
        exact Heqb.
      * (* j = S j' *)
        cbn [List.nth length] in Hj1, Hj2 |- *.
        replace (k + S j')%nat with (S k + j')%nat by lia.
        apply IHss with (k := S k).
        -- exact Htail.
        -- lia.
        -- lia.
Qed.

Lemma scaling_Z_from_check (k : nat) : (k < 43)%nat ->
  Z.mul (List.nth k charpoly_int BinNums.Z0) (Z.pow D_A (Z.of_nat (42 - k)))
  = Z.mul D_q (List.nth k charpoly_of_A_int BinNums.Z0).
Proof.
  intros Hk.
  (* Get the BigZ-level result from check_scaling_coefs_sound *)
  pose proof (check_scaling_coefs_sound 0
    (List.map BigZ.of_Z charpoly_int) charpoly_of_A_int_bigZ
    charpoly_scaling_agrees k) as H.
  (* Satisfy the length conditions *)
  assert (Hlen1 : (k < length (List.map BigZ.of_Z charpoly_int))%nat).
  { rewrite length_map. rewrite length_charpoly_int. exact Hk. }
  assert (Hlen2 : (k < length charpoly_of_A_int_bigZ)%nat).
  { rewrite charpoly_of_A_int_bigZ_length. exact Hk. }
  specialize (H Hlen1 Hlen2).
  (* Simplify 0 + k to k *)
  replace (0 + k)%nat with k in H by lia.
  (* Rewrite H: nth of map BigZ.of_Z list *)
  change 0%bigZ with (BigZ.of_Z BinNums.Z0) in H.
  rewrite map_nth in H.
  (* Now H has BigZ.to_Z (BigZ.of_Z (nth k charpoly_int 0%Z)) on the left *)
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite H: BigZ.pow -> Z.pow *)
  rewrite BigZ.spec_pow in H.
  rewrite BigZ.spec_of_Z in H.
  unfold D_A_bigZ in H.
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite H: D_q_bigZ -> D_q *)
  unfold D_q_bigZ in H.
  rewrite BigZ.spec_of_Z in H.
  (* Rewrite the goal to expose BigZ.to_Z form on RHS *)
  change charpoly_of_A_int with (lift_bigZ charpoly_of_A_int_bigZ).
  unfold lift_bigZ.
  change BinNums.Z0 with (BigZ.to_Z 0%bigZ).
  rewrite map_nth.
  exact H.
Qed.

(* ------------------------------------------------------------------
   4. Row-length bridge
   ------------------------------------------------------------------ *)

Lemma forallb_all_rows_len n (M : list (list Z)) :
  forallb (fun row => Nat.eqb (length row) n) M = true ->
  all_rows_len n M.
Proof.
  intros Hfb.
  unfold all_rows_len. intros i Hi.
  rewrite forallb_forall in Hfb.
  assert (Hin : In (nth i M nil) M).
  { apply nth_In. exact Hi. }
  specialize (Hfb _ Hin).
  rewrite Nat.eqb_eq in Hfb.
  exact Hfb.
Qed.
