(* ===================================================================
   ModularHess.v -- Axiom-free, stdlib-Z, O(n^3) modular characteristic
   polynomial via upper-Hessenberg reduction + the Hessenberg
   (Hyman-style) char-poly recurrence.

   MOTIVATION.  ModularFL.char_poly_modZ computes char_poly(M) mod p by
   the modular Faddeev-LeVerrier loop.  Each FL step performs two full
   n x n matrix products, so the whole pass is O(n^4); on the 42x42
   M1_int that is ~6.2M modular multiplications, ~328s/prime under
   vm_compute (Uint63 / native_compute being forbidden here), i.e. the
   `CRTFrame.per_prime_all` obstruction.

   This file replaces the O(n^4) FL pass by the textbook O(n^3) route:

     1. reduce M mod p                                  (reduceZ)
     2. transform to upper-Hessenberg form by a sequence of
        similarity transformations mod p                (hess_reduce)
     3. read off det(xI - H) by the Hessenberg recurrence  (hess_charpoly)

   Step 2 conjugates by elementary matrices E_{i,k+1}(m) = I + m e_{i,k+1}
   (whose inverse is I - m e_{i,k+1}); each conjugation is a row op
   (Row_i -= m Row_{k+1}) followed by the matching column op
   (Col_{k+1} += m Col_i), which zeroes the entry below the subdiagonal
   while preserving the characteristic polynomial.  The pivot
   H[k+1][k] must be invertible mod p (p prime => nonzero suffices);
   `hess_reduce` returns `None` if any pivot vanishes, in which case
   `char_poly_hess` transparently falls back to the (proven) FL pass, so
   the soundness theorem needs NO extra good-pivot hypothesis.

   Step 3 uses, for upper-Hessenberg H (0-indexed, subdiagonal
   sub_j = H[j+1][j]), the leading-principal-minor recurrence

     p_0 = 1,
     p_k = (x - H[k-1][k-1]) * p_{k-1}
           - sum_{i=0}^{k-2} H[i][k-1] * (prod_{j=i}^{k-2} sub_j) * p_i,

   for which p_n = det(xI - H) = char_poly(H).  All polynomial and matrix
   arithmetic is performed modulo p over Stdlib's Z; the FL inverse
   machinery (invmodZ via Fermat) is reused from ModularFL.

   MAIN RESULT (same shape / RHS as char_poly_modZ_sound):

     char_poly_hess_sound :
       forall (p:Z)(M:mat),
         Znumtheory.prime p ->
         square_mat (length M) M ->
         (Z.of_nat (length M) + 1 < p)%Z ->
         fl_all_divisible (length M) 1 M (meye (length M)) (mzero (length M)) 1 ->
         char_poly_hess p M = map (fun c => c mod p) (char_poly_int M).

   The `None` (bad-pivot) branch is closed outright by reusing
   ModularFL.char_poly_modZ_sound.  The `Some` (Hessenberg) branch is
   factored through two purely list-Z lemmas, each a self-contained
   classical theorem of linear algebra:

     hess_recurrence_sound  -- the Hessenberg recurrence computes the
                               char-poly mod p of the reduced matrix H
                               (Laplace expansion along the last row);
     hess_reduce_similar    -- the Hessenberg reduction is a similarity,
                               so char_poly(H) = char_poly(M) mod p.

   Both are left `Admitted` with a (* TODO-BRIDGE *) marker: each is a
   multi-hundred-line MathComp determinant/similarity development (see
   the proof-strategy notes at each lemma), beyond the scope closed
   here.  The algorithm itself is exercised by the machine-checked
   `Example`s below (char_poly_hess = char_poly_int mod p on concrete
   matrices, by vm_compute), giving a computational correctness check
   independent of those two bridges.

   No Uint63 / PrimInt63 / native_compute / Axiom / Parameter appears.
   =================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From PrimeGapS1 Require Import IntMat CharPoly ModularFL Fermat FLDiv PrimeCheck.
From Stdlib Require Znumtheory.

(* ================================================================== *)
(* Section 1: modular polynomial arithmetic (list Z, low-to-high)      *)
(* ================================================================== *)

(* Coefficient-wise negation mod p. *)
Definition pnegZ (p : Z) (q : list Z) : list Z := map (fun x => negmodZ p x) q.

(* Polynomial subtraction mod p (vaddZ tolerates unequal lengths). *)
Definition psubZ (p : Z) (a b : list Z) : list Z := vaddZ p a (pnegZ p b).

(* Multiply a polynomial by the linear factor (x - a), mod p:
   (x - a) * q = (x * q) - a * q, where x * q is the shift `0 :: q`. *)
Definition pmulXsub (p a : Z) (q : list Z) : list Z :=
  vaddZ p (0 :: q) (vscaleZ p (negmodZ p a) q).

(* ================================================================== *)
(* Section 2: the Hessenberg characteristic-polynomial recurrence      *)
(* ================================================================== *)

(* Entry accessor for the concrete list-of-list-Z matrix. *)
Definition getH (H : mat) (i j : nat) : Z := nth_Z (nth i H []) j.

(* Right fold computing the subtracted sum of the recurrence for one k.

   Input: the list of triples (H[i][col], sub_i, p_i) for i = 0..k-2,
   with sub_i = H[i+1][i] the subdiagonal entry aligned to index i.
   It returns the pair
     (prod_{j=0}^{k-2} sub_j ,  sum_{i=0}^{k-2} H[i][col]
                                  * (prod_{j=i}^{k-2} sub_j) * p_i),
   the first component being the suffix product threaded leftwards. *)
Fixpoint hess_fold (p : Z) (l : list (Z * Z * list Z)) : Z * list Z :=
  match l with
  | [] => (1 mod p, [])
  | (h, sub, pi) :: rest =>
      let res := hess_fold p rest in
      let prest := fst res in
      let srest := snd res in
      let prod_i := mulmodZ p sub prest in
      let coef := mulmodZ p h prod_i in
      (prod_i, vaddZ p (vscaleZ p coef pi) srest)
  end.

(* Compute p_k from ps = [p_0; ...; p_{k-1}] (length k), col = k - 1:
     p_k = (x - H[col][col]) * p_{k-1}  -  (sum produced by hess_fold). *)
Definition hess_pk (p : Z) (H : mat) (k : nat) (ps : list (list Z)) : list Z :=
  let col := (k - 1)%nat in
  let term1 := pmulXsub p (getH H col col) (nth col ps []) in
  let triples := map (fun i => (getH H i col, getH H (i + 1) i, nth i ps []))
                     (List.seq 0 col) in
  psubZ p term1 (snd (hess_fold p triples)).

(* Build the list [p_0; p_1; ...; p_steps], starting from ps = [p_0]. *)
Fixpoint hess_build (p : Z) (H : mat) (steps : nat) (ps : list (list Z))
  : list (list Z) :=
  match steps with
  | O => ps
  | S s => hess_build p H s (ps ++ [hess_pk p H (length ps) ps])
  end.

(* The char-poly of the (upper-Hessenberg, already reduced) matrix H,
   as the degree-n polynomial p_n (monic, low-to-high, length n+1). *)
Definition hess_charpoly (p : Z) (H : mat) (n : nat) : list Z :=
  nth n (hess_build p H n [[1 mod p]]) [].

(* ================================================================== *)
(* Section 3: upper-Hessenberg reduction mod p (elementary similarity) *)
(* ================================================================== *)

(* In-place positional update of the i-th element by f. *)
Fixpoint upd {A : Type} (l : list A) (i : nat) (f : A -> A) : list A :=
  match l, i with
  | [], _ => []
  | x :: xs, O => f x :: xs
  | x :: xs, S i' => x :: upd xs i' f
  end.

(* Row-vector subtraction mod p. *)
Definition vsubZ (p : Z) (a b : list Z) : list Z := vaddZ p a (pnegZ p b).

(* One elimination, conjugating by E_{i,k1}(m) with k1 = k+1:
     row op  Row_i      := Row_i - m * Row_{k1}   (zeroes the (i,k) entry)
     col op  Col_{k1}   := Col_{k1} + m * Col_i. *)
Definition hess_elim_step (p : Z) (M : mat) (k1 i : nat) (m : Z) : mat :=
  let rowi := nth i M [] in
  let rowk1 := nth k1 M [] in
  let newrowi := vsubZ p rowi (vscaleZ p m rowk1) in
  let M1 := upd M i (fun _ => newrowi) in
  map (fun row => upd row k1 (fun old => addmodZ p old (mulmodZ p m (nth_Z row i)))) M1.

(* Process column k: eliminate all entries below the subdiagonal
   (rows i = k+2 .. n-1) using the fixed pivot H[k+1][k]. *)
Definition hess_inner (p : Z) (M : mat) (k : nat) (pinv : Z) (is : list nat) : mat :=
  fold_left
    (fun Mc i => hess_elim_step p Mc (S k) i (mulmodZ p (getH Mc i k) pinv))
    is M.

(* Sweep columns k = 0 .. n-3.  Abort (None) on a non-invertible pivot. *)
Fixpoint hess_outer (p : Z) (M : mat) (n : nat) (ks : list nat) : option mat :=
  match ks with
  | [] => Some M
  | k :: ks' =>
      let piv := getH M (S k) k in
      if Z.eqb (piv mod p) 0 then None
      else hess_outer p
             (hess_inner p M k (invmodZ p piv) (List.seq (k + 2) (n - (k + 2))))
             n ks'
  end.

Definition hess_reduce (p : Z) (M : mat) : option mat :=
  let n := mat_dim M in
  hess_outer p (reduceZ p M) n (List.seq 0 (n - 2)).

(* ================================================================== *)
(* Section 4: the O(n^3) modular characteristic polynomial             *)
(* ================================================================== *)

(* Fast path: reduce to Hessenberg, then the recurrence.  If a pivot
   fails, fall back to the (proven) O(n^4) FL pass so the result is
   total and the soundness theorem needs no good-pivot hypothesis. *)
Definition char_poly_hess (p : Z) (M : mat) : list Z :=
  let n := mat_dim M in
  match hess_reduce p M with
  | Some H => hess_charpoly p H n
  | None => char_poly_modZ p M
  end.

(* ================================================================== *)
(* Section 5: machine-checked validation against char_poly_int         *)
(*                                                                     *)
(* These reduce char_poly_hess on concrete integer matrices and check  *)
(* equality with char_poly_int mod p by vm_compute -- a computational  *)
(* correctness witness independent of the two TODO-BRIDGE lemmas.      *)
(* ================================================================== *)

Example hess_validate_4 :
  char_poly_hess 101 [[2;1;3;5];[4;5;6;1];[7;1;8;2];[3;2;1;9]]
  = map (fun c => c mod 101)
        (char_poly_int [[2;1;3;5];[4;5;6;1];[7;1;8;2];[3;2;1;9]]).
Proof. vm_compute. reflexivity. Qed.

Example hess_validate_5 :
  char_poly_hess 211 [[2;1;3;5;1];[4;5;6;1;2];[7;1;8;2;3];[3;2;1;9;4];[1;1;1;1;6]]
  = map (fun c => c mod 211)
        (char_poly_int [[2;1;3;5;1];[4;5;6;1;2];[7;1;8;2;3];[3;2;1;9;4];[1;1;1;1;6]]).
Proof. vm_compute. reflexivity. Qed.

Example hess_validate_6 :
  char_poly_hess 307
    [[2;1;3;5;1;0];[4;5;6;1;2;1];[7;1;8;2;3;2];
     [3;2;1;9;4;1];[1;1;1;1;6;3];[2;0;1;2;1;7]]
  = map (fun c => c mod 307)
        (char_poly_int
          [[2;1;3;5;1;0];[4;5;6;1;2;1];[7;1;8;2;3;2];
           [3;2;1;9;4;1];[1;1;1;1;6;3];[2;0;1;2;1;7]]).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 5b: MathComp scaffolding for the similarity bridge          *)
(*                                                                     *)
(* From here on we bring MathComp into scope to reason about the       *)
(* abstract characteristic polynomial.  We re-import Stdlib's `List`   *)
(* afterwards so that the unqualified `map` / `nth` in the statements  *)
(* below keep their Stdlib meaning (matching the downstream chain),    *)
(* and restore `%Z` = `Z_scope`.  All helpers are `Local`.            *)
(* ================================================================== *)

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.
From mathcomp.algebra_tactics Require Import ring.

(* ================================================================== *)
(* Section 5a: abstract upper-Hessenberg determinant recurrence        *)
(*                                                                     *)
(* For an upper-Hessenberg matrix A over any comNzRingType (A i j = 0  *)
(* whenever j+1 < i), the leading principal minor Dlead m = det of the *)
(* top-left m x m block satisfies the Hyman recurrence Dlead_rec, and  *)
(* Dlead n = det A (Dlead_full).  Instantiated at the polynomial ring  *)
(* {poly 'F_p} with A := char_poly_mx (MXFp p n H) this is exactly the *)
(* recurrence computed by hess_pk / hess_fold.  (VERIFIED standalone.) *)
(* ================================================================== *)

Section HessDet.
Local Open Scope ring_scope.
Variable R : comNzRingType.
Variable N : nat.
Local Notation n := N.+1.
Variable A : 'M[R]_n.
Hypothesis Ahess : forall i j : 'I_n, (j.+1 < i)%N -> A i j = 0.

Definition Block (m:nat) : 'M[R]_m := \matrix_(a < m, b < m) A (inord a) (inord b).
Definition Dlead (m:nat) : R := \det (Block m).
Definition Mmat (i m:nat) : 'M[R]_(m.-1) :=
  \matrix_(a < m.-1, b < m.-1) A (inord (bump i a)) (inord b).
Definition Mmin (i m:nat) : R := \det (Mmat i m).

Lemma reshape_row (i m:nat) :
  row' ord_max (col' ord_max (Mmat i (m.+2))) = Mmat i (m.+1).
Proof.
apply/matrixP => a b.
rewrite !mxE.
by rewrite !lift_max.
Qed.

Lemma bumple (i m:nat) : (i<=m)%N -> bump i m = m.+1.
Proof. by move=> H; rewrite /bump H add1n. Qed.

Lemma Mmin_peel (i m:nat) :
  (i <= m)%N -> (m.+1 < n)%N ->
  Mmin i (m.+2) = A (inord (m.+1)) (inord m) * Mmin i (m.+1).
Proof.
move=> Him Hmn.
rewrite /Mmin (expand_det_row _ ord_max) (bigD1 ord_max) //=.
rewrite mxE [nat_of_ord (@ord_max m)]/= bumple //.
rewrite /cofactor reshape_row.
have Hsgn : (-1:R)^+(nat_of_ord (@ord_max m) + nat_of_ord (@ord_max m)) = 1.
  by rewrite addnn -muln2 exprM sqrr_sign.
rewrite Hsgn mul1r big1 ?addr0 //.
move=> i0 Hi0.
rewrite mxE [nat_of_ord (@ord_max m)]/= bumple //.
suff -> : A (inord (m.+1)) (inord (nat_of_ord i0)) = 0 by rewrite mul0r.
apply: Ahess.
have Hi0n : (i0 < n)%N by apply: (ltn_trans (ltn_ord i0)).
rewrite (inordK Hmn) (inordK Hi0n).
rewrite ltnS ltn_neqAle -ltnS ltn_ord andbT.
by rewrite -val_eqE in Hi0.
Qed.

Lemma Mmin_base (i:nat) : Mmin i (i.+1) = Dlead i.
Proof.
rewrite /Mmin /Dlead /=.
congr (\det _); apply/matrixP => a b; rewrite !mxE.
congr (A (inord _) (inord b)).
rewrite /bump.
have -> : (i <= a)%N = false by apply/negbTE; rewrite -ltnNge; exact: ltn_ord.
by rewrite add0n.
Qed.

Lemma Mmin_prod (i m:nat) : (i <= m)%N -> (m < n)%N ->
  Mmin i (m.+1) = (\prod_(i <= j < m) A (inord j.+1) (inord j)) * Dlead i.
Proof.
elim: m => [|m IH].
- move=> Hi0 _. move: Hi0; rewrite leqn0 => /eqP ->.
  by rewrite big_geq // mul1r Mmin_base.
- move=> Him Hmn.
  rewrite leq_eqVlt in Him.
  case/orP: Him => [/eqP Heq | Hlt].
  + rewrite Heq big_geq // mul1r. exact: Mmin_base.
  + have Him' : (i <= m)%N by rewrite -ltnS.
    have Hmn' : (m < n)%N by apply: (ltn_trans (ltnSn m)).
    rewrite (Mmin_peel i m Him' Hmn) (IH Him' Hmn').
    rewrite big_nat_recr //=.
    by rewrite mulrCA mulrA.
Qed.

Lemma reshape_col (m:nat) (i0:'I_(m.+1)) :
  row' i0 (col' ord_max (Block (m.+1))) = Mmat (nat_of_ord i0) (m.+1).
Proof.
apply/matrixP => a b; rewrite !mxE lift_max /=.
by congr (A (inord _) (inord b)).
Qed.

Lemma Dlead_rec (m:nat) : (m < n)%N ->
  Dlead (m.+1) = A (inord m) (inord m) * Dlead m
   + \sum_(i < m) (A (inord (nat_of_ord i)) (inord m) * (-1)^+(nat_of_ord i + m)
        * (\prod_(nat_of_ord i <= j < m) A (inord j.+1) (inord j)) * Dlead (nat_of_ord i)).
Proof.
move=> Hmn.
rewrite [Dlead (m.+1)]/Dlead (expand_det_col _ ord_max) big_ord_recr /= addrC.
congr (_ + _).
- rewrite mxE /cofactor reshape_col [nat_of_ord (@ord_max m)]/=.
  rewrite -/(Mmin m (m.+1)) Mmin_base.
  have ->: (-1:R)^+(m+m) = 1 by rewrite addnn -muln2 exprM sqrr_sign.
  by rewrite mul1r.
- apply: eq_bigr => i _.
  rewrite mxE /cofactor reshape_col -/(Mmin (nat_of_ord i) (m.+1)).
  rewrite (Mmin_prod (nat_of_ord i) m _ Hmn); last by rewrite ltnW // ltn_ord.
  by rewrite !mulrA.
Qed.

Lemma Dlead_full : Dlead n = \det A.
Proof.
rewrite /Dlead /Block; congr (\det _).
by apply/matrixP => a b; rewrite mxE !inord_val.
Qed.

End HessDet.

From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.
Delimit Scope Z_scope with Z.

(* ---- scalar bridge Z -> 'F_p (p prime) ---- *)

Local Definition Z_to_Fp (p:Z) (z:Z) : 'F_(Z.to_nat p) := (Z_to_int z)%:~R.

Local Lemma Z_to_Fp_add p a b :
  Z_to_Fp p (a+b) = (Z_to_Fp p a + Z_to_Fp p b)%R.
Proof. by rewrite /Z_to_Fp Z_to_int_add intrD. Qed.

Local Lemma Z_to_Fp_mul p a b :
  Z_to_Fp p (a*b) = (Z_to_Fp p a * Z_to_Fp p b)%R.
Proof. by rewrite /Z_to_Fp Z_to_int_mul intrM. Qed.

Local Lemma Z_to_Fp_opp p a : Z_to_Fp p (- a) = (- Z_to_Fp p a)%R.
Proof. by rewrite /Z_to_Fp Z_to_int_opp rmorphN. Qed.

Local Lemma Z_to_Fp_sub p a b :
  Z_to_Fp p (a - b) = (Z_to_Fp p a - Z_to_Fp p b)%R.
Proof. by rewrite /Z.sub Z_to_Fp_add Z_to_Fp_opp. Qed.

Local Lemma Z_to_int_pos (p:Z) : (0 <= p)%Z -> Z_to_int p = Posz (Z.to_nat p).
Proof. destruct p as [|q|q]; simpl; try reflexivity. lia. Qed.

Local Lemma Z_to_Fp_p (p:Z) : Znumtheory.prime p -> Z_to_Fp p p = 0%R.
Proof.
move=> Hp.
have Hp1 : (1 < p)%Z by destruct Hp.
have Hpr : prime (Z.to_nat p) by apply Zprime_to_ssrprime; [lia | exact Hp].
rewrite /Z_to_Fp Z_to_int_pos; [|lia].
by rewrite -natz rmorph_nat pchar_Fp_0.
Qed.

Local Lemma Z_to_Fp_mod (p:Z) : Znumtheory.prime p ->
  forall z, Z_to_Fp p (z mod p) = Z_to_Fp p z.
Proof.
move=> Hp z.
have Hp0 : (p <> 0)%Z by destruct Hp; lia.
rewrite (Z.mod_eq z p Hp0) Z_to_Fp_sub Z_to_Fp_mul Z_to_Fp_p //.
by rewrite mul0r subr0.
Qed.

Local Lemma Z_to_Fp_val (p:Z) : Znumtheory.prime p ->
  forall z, nat_of_ord (Z_to_Fp p z) = Z.to_nat (z mod p).
Proof.
move=> Hp z.
have Hp1 : (1 < p)%Z by destruct Hp; lia.
have Hpr : prime (Z.to_nat p) by apply Zprime_to_ssrprime; [lia | exact Hp].
have Hb := Z.mod_pos_bound z p ltac:(lia).
rewrite -(Z_to_Fp_mod p Hp) /Z_to_Fp Z_to_int_pos; [|lia].
rewrite -natz rmorph_nat val_Fp_nat // modn_small //.
apply/ltP. apply Z2Nat.inj_lt; lia.
Qed.

Local Lemma Z_to_Fp_eqmod (p:Z) : Znumtheory.prime p ->
  forall a b, Z_to_Fp p a = Z_to_Fp p b -> (a mod p = b mod p)%Z.
Proof.
move=> Hp a b H.
have Hp1 : (1 < p)%Z by destruct Hp; lia.
have Ha := Z_to_Fp_val p Hp a.
have Hb := Z_to_Fp_val p Hp b.
have HHa := Z.mod_pos_bound a p ltac:(lia).
have HHb := Z.mod_pos_bound b p ltac:(lia).
have Hnat : Z.to_nat (a mod p) = Z.to_nat (b mod p) by rewrite -Ha -Hb H.
apply Z2Nat.inj; [lia | lia | exact Hnat].
Qed.

(* ---- char_poly is invariant under conjugation by P, Q with P Q = 1 ---- *)

Local Lemma char_poly_conj (R : comNzRingType) (n:nat) (P Q A : 'M[R]_n) :
  P *m Q = 1%:M -> char_poly (P *m A *m Q) = char_poly A.
Proof.
move=> HPQ.
have key : map_mx (@polyC R) P *m 'X%:M *m map_mx (@polyC R) Q = 'X%:M.
{ by rewrite scalar_mxC -mulmxA -map_mxM HPQ map_mx1 mulmx1. }
have Hcm : char_poly_mx (P *m A *m Q)
         = map_mx (@polyC R) P *m char_poly_mx A *m map_mx (@polyC R) Q.
{ rewrite /char_poly_mx mulmxBr mulmxBl key.
  by rewrite !map_mxM. }
have Hdet : (\det (map_mx (@polyC R) P) * \det (map_mx (@polyC R) Q) = 1)%R.
{ by rewrite -det_mulmx -map_mxM HPQ map_mx1 det1. }
by rewrite /char_poly Hcm !det_mulmx mulrAC Hdet mul1r.
Qed.

(* ---- Z_to_Fp on the modular scalar ops ---- *)

Local Lemma Z_to_Fp_0 p : Z_to_Fp p 0 = 0%R.
Proof. by rewrite /Z_to_Fp. Qed.

Local Lemma Z_to_Fp_addmod p : Znumtheory.prime p ->
  forall a b, Z_to_Fp p (addmodZ p a b) = (Z_to_Fp p a + Z_to_Fp p b)%R.
Proof. by move=> Hp a b; rewrite /addmodZ Z_to_Fp_mod // Z_to_Fp_add. Qed.

Local Lemma Z_to_Fp_mulmod p : Znumtheory.prime p ->
  forall a b, Z_to_Fp p (mulmodZ p a b) = (Z_to_Fp p a * Z_to_Fp p b)%R.
Proof. by move=> Hp a b; rewrite /mulmodZ Z_to_Fp_mod // Z_to_Fp_mul. Qed.

Local Lemma Z_to_Fp_negmod p : Znumtheory.prime p ->
  forall a, Z_to_Fp p (negmodZ p a) = (- Z_to_Fp p a)%R.
Proof. by move=> Hp a; rewrite /negmodZ Z_to_Fp_mod // Z_to_Fp_opp. Qed.

(* ---- Z_to_Fp commutes with nth_Z of the vector operations ---- *)

Local Lemma nth_Z_nil b : nth_Z [] b = 0%Z.
Proof. by case: b. Qed.

Local Lemma ZF_nth_vscaleZ p : Znumtheory.prime p ->
  forall m r b, Z_to_Fp p (nth_Z (vscaleZ p m r) b)
              = (Z_to_Fp p m * Z_to_Fp p (nth_Z r b))%R.
Proof.
move=> Hp m; elim => [|x r' IH] [|b].
- by rewrite /vscaleZ /= !nth_Z_nil Z_to_Fp_0 mulr0.
- by rewrite /vscaleZ /= !nth_Z_nil Z_to_Fp_0 mulr0.
- by rewrite /vscaleZ /= Z_to_Fp_mulmod.
- by rewrite /vscaleZ /= -/(vscaleZ p m r') IH.
Qed.

Local Lemma ZF_nth_pnegZ p : Znumtheory.prime p ->
  forall r b, Z_to_Fp p (nth_Z (pnegZ p r) b)
            = (- Z_to_Fp p (nth_Z r b))%R.
Proof.
move=> Hp; elim => [|x r' IH] [|b].
- by rewrite /pnegZ /= !nth_Z_nil Z_to_Fp_0 oppr0.
- by rewrite /pnegZ /= !nth_Z_nil Z_to_Fp_0 oppr0.
- by rewrite /pnegZ /= Z_to_Fp_negmod.
- by rewrite /pnegZ /= -/(pnegZ p r') IH.
Qed.

Local Lemma ZF_nth_vaddZ p : Znumtheory.prime p ->
  forall xs ys b, Z_to_Fp p (nth_Z (vaddZ p xs ys) b)
                = (Z_to_Fp p (nth_Z xs b) + Z_to_Fp p (nth_Z ys b))%R.
Proof.
move=> Hp; elim => [|x xs' IH] ys b.
- by rewrite /= nth_Z_nil Z_to_Fp_0 add0r.
- case: ys => [|y ys'].
  + by rewrite /= nth_Z_nil Z_to_Fp_0 addr0.
  + case: b => [|b'].
    * by rewrite /= Z_to_Fp_addmod.
    * by rewrite /= IH.
Qed.

Local Lemma ZF_nth_vsubZ p : Znumtheory.prime p ->
  forall xs ys b, Z_to_Fp p (nth_Z (vsubZ p xs ys) b)
                = (Z_to_Fp p (nth_Z xs b) - Z_to_Fp p (nth_Z ys b))%R.
Proof. by move=> Hp xs ys b; rewrite /vsubZ ZF_nth_vaddZ // ZF_nth_pnegZ. Qed.

(* ---- structural facts about upd and the vector lengths ---- *)

Local Lemma length_upd {A} (l:list A) i f : length (upd l i f) = length l.
Proof. elim: l i => [|x xs IH] [|i] //=. by rewrite IH. Qed.

Local Lemma nth_upd_same {A} (l:list A) i f (d:A) :
  (i < length l)%coq_nat -> nth i (upd l i f) d = f (nth i l d).
Proof.
elim: l i => [|x xs IH] [|i] /= H.
- lia.
- lia.
- by [].
- by apply IH; lia.
Qed.

Local Lemma nth_upd_other {A} (l:list A) i j f (d:A) :
  i <> j -> nth i (upd l j f) d = nth i l d.
Proof.
elim: l i j => [|x xs IH] [|i] [|j] /= H //.
by apply IH => E; apply H; rewrite E.
Qed.

Local Lemma nth_Z_upd_same r j f :
  (j < length r)%coq_nat -> nth_Z (upd r j f) j = f (nth_Z r j).
Proof. by move=> H; rewrite /nth_Z nth_upd_same. Qed.

Local Lemma nth_Z_upd_other r j f b :
  b <> j -> nth_Z (upd r j f) b = nth_Z r b.
Proof. by move=> H; rewrite /nth_Z nth_upd_other. Qed.

Local Lemma length_vaddZ_eq p xs ys :
  length xs = length ys -> length (vaddZ p xs ys) = length xs.
Proof. elim: xs ys => [|x xs' IH] [|y ys'] //= [] Hlen. by rewrite IH. Qed.

Local Lemma length_vscaleZ p m r : length (vscaleZ p m r) = length r.
Proof. by rewrite /vscaleZ length_map. Qed.

Local Lemma length_pnegZ p r : length (pnegZ p r) = length r.
Proof. by rewrite /pnegZ length_map. Qed.

Local Lemma length_vsubZ_eq p xs ys :
  length xs = length ys -> length (vsubZ p xs ys) = length xs.
Proof. by move=> H; rewrite /vsubZ length_vaddZ_eq // length_pnegZ. Qed.

(* ---- the matrix over 'F_p read off from a `mat` ---- *)

Local Definition MXFp (p:Z) (n:nat) (A:mat) : 'M['F_(Z.to_nat p)]_n :=
  \matrix_(i, j) Z_to_Fp p (getH A i j).

Local Lemma nth_map_eq {A} (F:A->A) (l:list A) (d:A) (a:nat) :
  F d = d -> nth a (map F l) d = F (nth a l d).
Proof. move=> Hd; elim: l a => [|x xs IH] [|a] //=. Qed.

(* ---- delta-matrix products and the conjugation-entry expansion ---- *)

Local Lemma deltaL_mul (R:nzRingType) n (oi ok:'I_n) (B:'M[R]_n) a b :
  (delta_mx oi ok *m B) a b = ((a==oi)%:R * B ok b)%R.
Proof.
rewrite mxE (bigD1 ok) //= mxE eqxx andbT big1 ?addr0 //.
by move=> j /negbTE Hj; rewrite mxE Hj andbF mul0r.
Qed.

Local Lemma deltaR_mul (R:nzRingType) n (oi ok:'I_n) (B:'M[R]_n) a b :
  (B *m delta_mx oi ok) a b = (B a oi * (b==ok)%:R)%R.
Proof.
rewrite mxE (bigD1 oi) //= mxE eqxx andTb big1 ?addr0 //.
by move=> j /negbTE Hj; rewrite mxE Hj andFb mulr0.
Qed.

Local Lemma sumdeltaL (R:nzRingType) n (oi ok:'I_n) (g:'I_n -> R) a :
  (\sum_(j < n) delta_mx oi ok a j * g j = (a==oi)%:R * g ok)%R.
Proof.
rewrite (bigD1 ok) //= mxE eqxx andbT big1 ?addr0 //.
by move=> j /negbTE Hj; rewrite mxE Hj andbF mul0r.
Qed.

Local Lemma sumdeltaR (R:nzRingType) n (oi ok:'I_n) (g:'I_n -> R) b :
  (\sum_(j < n) g j * delta_mx oi ok j b = g oi * (b==ok)%:R)%R.
Proof.
rewrite (bigD1 oi) //= mxE eqxx andTb big1 ?addr0 //.
by move=> j /negbTE Hj; rewrite mxE Hj andFb mulr0.
Qed.

Local Lemma conj_entry (R:comNzRingType) n (oi ok:'I_n) (mu:R) (B:'M[R]_n) a b :
  ((1%:M - mu *: delta_mx oi ok) *m B *m (1%:M + mu *: delta_mx oi ok)) a b
  = (B a b - (a==oi)%:R * mu * B ok b + (b==ok)%:R * mu * B a oi
     - (a==oi)%:R * (b==ok)%:R * mu * mu * B ok oi)%R.
Proof.
rewrite mulmxBl mul1mx -scalemxAl.
rewrite mulmxDr mulmx1 -scalemxAr.
rewrite mulmxBl -scalemxAl.
set P1 := delta_mx oi ok *m B.
rewrite !mxE.
rewrite sumdeltaL sumdeltaR sumdeltaR /P1 deltaL_mul.
ring.
Qed.

(* ---- the (i,j) entry of one elimination step over 'F_p ---- *)

Local Lemma ZF_getH_M1 p (Hp:Znumtheory.prime p) M k1 i m a b :
  (i < length M)%coq_nat ->
  Z_to_Fp p (getH (upd M i (fun _ => vsubZ p (nth i M [])
                                           (vscaleZ p m (nth k1 M [])))) a b)
  = (Z_to_Fp p (getH M a b)
     - (a==i)%:R * Z_to_Fp p m * Z_to_Fp p (getH M k1 b))%R.
Proof.
move=> Hi; rewrite /getH.
case: (@eqP _ a i) => [->|Hai].
- rewrite nth_upd_same //=.
  rewrite ZF_nth_vsubZ // ZF_nth_vscaleZ //.
  by rewrite mul1r.
- rewrite nth_upd_other //.
  by rewrite mul0r mul0r subr0.
Qed.

Local Lemma length_M1row p M k1 i m a :
  (i < length M)%coq_nat -> (k1 < length M)%coq_nat -> (a < length M)%coq_nat ->
  (forall c, (c < length M)%coq_nat -> length (nth c M []) = length M) ->
  length (nth a (upd M i (fun _ => vsubZ p (nth i M [])
                              (vscaleZ p m (nth k1 M [])))) []) = length M.
Proof.
move=> Hi Hk1 Ha Hrows.
case: (@eqP _ a i) => [->|Hai].
- rewrite nth_upd_same // length_vsubZ_eq.
  + by apply: Hrows.
  + by rewrite length_vscaleZ (Hrows i Hi) (Hrows k1 Hk1).
- by rewrite nth_upd_other //; apply: Hrows.
Qed.

Local Lemma ZF_nthZ_M1 p (Hp:Znumtheory.prime p) M k1 i m a c :
  (i < length M)%coq_nat ->
  Z_to_Fp p (nth_Z (nth a (upd M i (fun _ => vsubZ p (nth i M [])
                                           (vscaleZ p m (nth k1 M [])))) []) c)
  = (Z_to_Fp p (getH M a c)
     - (a==i)%:R * Z_to_Fp p m * Z_to_Fp p (getH M k1 c))%R.
Proof. exact: (ZF_getH_M1 p Hp M k1 i m a c). Qed.

Local Lemma ZF_getH_elim p (Hp:Znumtheory.prime p) M k1 i m a b :
  (i < length M)%coq_nat -> (k1 < length M)%coq_nat -> (a < length M)%coq_nat ->
  (forall c, (c < length M)%coq_nat -> length (nth c M []) = length M) ->
  Z_to_Fp p (getH (hess_elim_step p M k1 i m) a b)
  = (Z_to_Fp p (getH M a b)
     - (a==i)%:R * Z_to_Fp p m * Z_to_Fp p (getH M k1 b)
     + (b==k1)%:R * Z_to_Fp p m * Z_to_Fp p (getH M a i)
     - (a==i)%:R * (b==k1)%:R * Z_to_Fp p m * Z_to_Fp p m
       * Z_to_Fp p (getH M k1 i))%R.
Proof.
move=> Hi Hk1 Ha Hrows.
rewrite {1}/getH /hess_elim_step.
rewrite nth_map_eq //.
have Hra := length_M1row p M k1 i m a Hi Hk1 Ha Hrows.
case: (@eqP _ b k1) => [->|Hbk].
- rewrite nth_Z_upd_same; last by rewrite Hra.
  rewrite Z_to_Fp_addmod // Z_to_Fp_mulmod // !ZF_nthZ_M1 // !mulr1n.
  ring.
- rewrite nth_Z_upd_other // ZF_nthZ_M1 // !mulr0n.
  ring.
Qed.

(* ---- one elimination step is conjugation by a unit elementary matrix ---- *)

Local Lemma delta_sq0 (R:comNzRingType) n (oi ok:'I_n) : oi != ok ->
  (delta_mx oi ok *m delta_mx oi ok = 0 :> 'M[R]_n)%R.
Proof.
move=> Hne.
rewrite mul_delta_mx_cond.
have -> : (ok == oi) = false by rewrite eq_sym; apply/negbTE.
by rewrite mulr0n.
Qed.

Local Lemma ELER (R:comNzRingType) n (oi ok:'I_n) (mu:R) : oi != ok ->
  ((1%:M - mu *: delta_mx oi ok) *m (1%:M + mu *: delta_mx oi ok) = 1%:M)%R.
Proof.
move=> Hne.
rewrite mulmxDr mulmx1 mulmxBl mul1mx.
rewrite -scalemxAl -scalemxAr scalerA delta_sq0 // scaler0.
by rewrite subr0 subrK.
Qed.

Local Lemma MXFp_elim_step p (Hp:Znumtheory.prime p) n A (oi ok:'I_n) m :
  (forall c, (c < n)%coq_nat -> length (nth c A []) = n) ->
  length A = n ->
  MXFp p n (hess_elim_step p A (nat_of_ord ok) (nat_of_ord oi) m)
  = ((1%:M - Z_to_Fp p m *: delta_mx oi ok)
       *m MXFp p n A
       *m (1%:M + Z_to_Fp p m *: delta_mx oi ok))%R.
Proof.
move=> Hrows HlenA.
have Hoi : (nat_of_ord oi < length A)%coq_nat
  by apply/ltP; rewrite HlenA; exact: ltn_ord.
have Hok : (nat_of_ord ok < length A)%coq_nat
  by apply/ltP; rewrite HlenA; exact: ltn_ord.
have HrowsA : forall c, (c < length A)%coq_nat -> length (nth c A []) = length A
  by rewrite HlenA.
apply/matrixP => a b.
have Ha : (nat_of_ord a < length A)%coq_nat
  by apply/ltP; rewrite HlenA; exact: ltn_ord.
rewrite mxE conj_entry.
rewrite (ZF_getH_elim p Hp A (nat_of_ord ok) (nat_of_ord oi) m a b
           Hoi Hok Ha HrowsA).
rewrite !mxE !val_eqE.
ring.
Qed.

(* ---- folds of elimination steps preserve shape and char_poly ---- *)

Local Definition goodA (n:nat) (A:mat) : Prop :=
  length A = n /\ (forall c, (c < n)%coq_nat -> length (nth c A []) = n).

Local Lemma good_elim_step p n A k1 i m :
  (i < n)%coq_nat -> (k1 < n)%coq_nat ->
  goodA n A -> goodA n (hess_elim_step p A k1 i m).
Proof.
move=> Hi Hk1 [HlenA Hrows].
have HiA : (i < length A)%coq_nat by rewrite HlenA.
have Hk1A : (k1 < length A)%coq_nat by rewrite HlenA.
have HrowsA : forall c, (c < length A)%coq_nat -> length (nth c A []) = length A
  by rewrite HlenA.
split.
- by rewrite /hess_elim_step length_map length_upd HlenA.
- move=> c Hc.
  have HcA : (c < length A)%coq_nat by rewrite HlenA.
  rewrite /hess_elim_step nth_map_eq // length_upd.
  rewrite (length_M1row p A k1 i m c HiA Hk1A HcA HrowsA).
  exact HlenA.
Qed.

Local Lemma elim_step_charpoly p (Hp:Znumtheory.prime p) n A k1 i m :
  goodA n A -> (i < n)%coq_nat -> (k1 < n)%coq_nat -> i <> k1 ->
  char_poly (MXFp p n (hess_elim_step p A k1 i m)) = char_poly (MXFp p n A).
Proof.
move=> [HlenA Hrows] Hi Hk1 Hik.
have Hi' : (i < n)%N by apply/ltP.
have Hk1' : (k1 < n)%N by apply/ltP.
pose oi := Ordinal Hi'. pose ok := Ordinal Hk1'.
have Hne : oi != ok by apply/eqP => H; apply: Hik; exact: (congr1 val H).
transitivity (char_poly ((1%:M - Z_to_Fp p m *: delta_mx oi ok)
                          *m MXFp p n A
                          *m (1%:M + Z_to_Fp p m *: delta_mx oi ok))).
- congr char_poly.
  exact: (MXFp_elim_step p Hp n A oi ok m Hrows HlenA).
- apply: char_poly_conj. exact: (ELER _ n oi ok (Z_to_Fp p m) Hne).
Qed.

Local Lemma hess_inner_ok p (Hp:Znumtheory.prime p) n k pinv il :
  (S k < n)%coq_nat ->
  (forall i, In i il -> (i < n)%coq_nat /\ i <> S k) ->
  forall A, goodA n A ->
    goodA n (hess_inner p A k pinv il)
    /\ char_poly (MXFp p n (hess_inner p A k pinv il))
       = char_poly (MXFp p n A).
Proof.
move=> Hk; rewrite /hess_inner.
elim: il => [|i0 is' IH] Hin A HA /=.
- by split.
- have Hi0 : (i0 < n)%coq_nat /\ i0 <> S k by apply: Hin; left.
  have HA' : goodA n (hess_elim_step p A (S k) i0
                        (mulmodZ p (getH A i0 k) pinv)).
  { apply: good_elim_step; [exact (proj1 Hi0) | exact Hk | exact HA]. }
  have Hin' : forall i, In i is' -> (i < n)%coq_nat /\ i <> S k.
  { move=> j Hj; apply: Hin; right; exact Hj. }
  have [Hg Hc] := IH Hin' _ HA'.
  split; first exact Hg.
  rewrite Hc.
  apply: (elim_step_charpoly p Hp n A (S k) i0);
    [exact HA | exact (proj1 Hi0) | exact Hk | exact (proj2 Hi0)].
Qed.

Local Lemma seq_inner_cond k n :
  forall i, In i (List.seq (k+2) (n-(k+2))) -> (i < n)%coq_nat /\ i <> S k.
Proof. move=> i /in_seq Hi. lia. Qed.

Local Lemma hess_outer_ok p (Hp:Znumtheory.prime p) n ks :
  (forall k, In k ks -> (S k < n)%coq_nat) ->
  forall A H, goodA n A -> hess_outer p A n ks = Some H ->
    goodA n H /\ char_poly (MXFp p n H) = char_poly (MXFp p n A).
Proof.
elim: ks => [|k ks' IH] Hin A H HA.
- move=> /= [= <-]. by split.
- rewrite /=. case: ifP => [_|_].
  + by [].
  + move=> Hrec.
    have Hk : (S k < n)%coq_nat by apply: Hin; left.
    have [Hg' Hc'] := hess_inner_ok p Hp n k (invmodZ p (getH A (S k) k))
                        (List.seq (k+2) (n-(k+2))) Hk (seq_inner_cond k n) A HA.
    have Hin' : forall j, In j ks' -> (S j < n)%coq_nat
      by move=> j Hj; apply: Hin; right.
    have [HgH HcH] := IH Hin' _ H Hg' Hrec.
    split; first exact HgH.
    rewrite HcH; exact: Hc'.
Qed.

Local Lemma goodA_reduceZ p n M : goodA n M -> goodA n (reduceZ p M).
Proof.
move=> [HlenM Hrows]; split.
- by rewrite /reduceZ length_map.
- by move=> c Hc; rewrite /reduceZ nth_map_eq // length_map; apply: Hrows.
Qed.

Local Lemma ks_cond n : forall k, In k (List.seq 0 (n-2)) -> (S k < n)%coq_nat.
Proof. move=> k /in_seq Hk. lia. Qed.

Local Lemma MXFp_reduceZ p (Hp:Znumtheory.prime p) n M :
  MXFp p n (reduceZ p M) = MXFp p n M.
Proof.
have Hp0 : (p <> 0)%Z by destruct Hp; lia.
apply/matrixP => a b; rewrite !mxE.
have -> : getH (reduceZ p M) a b = (getH M a b) mod p.
{ rewrite /getH /reduceZ nth_map_eq // /nth_Z.
  rewrite nth_map_eq //; by rewrite Z.mod_0_l. }
by rewrite Z_to_Fp_mod.
Qed.

Local Lemma square_goodA M : square_mat (length M) M -> goodA (length M) M.
Proof. by move=> [Hdim Hrows]; split; [reflexivity | exact Hrows]. Qed.

(* char_poly(H over F_p) = char_poly(M over F_p): the similarity itself *)
Local Lemma hess_reduce_charpoly_Fp p (Hp:Znumtheory.prime p) M H :
  square_mat (length M) M -> hess_reduce p M = Some H ->
  goodA (length M) H /\
  char_poly (MXFp p (length M) H) = char_poly (MXFp p (length M) M).
Proof.
move=> Hsq Hred.
have HgM := square_goodA M Hsq.
have HgR := goodA_reduceZ p (length M) M HgM.
rewrite /hess_reduce in Hred.
have [HgH HcH] := hess_outer_ok p Hp (length M) (List.seq 0 (length M - 2))
                    (ks_cond (length M)) (reduceZ p M) H HgR Hred.
split; first exact HgH.
rewrite HcH (MXFp_reduceZ p Hp (length M) M). by [].
Qed.

(* ---- bridge: char_poly over 'F_p reads off char_poly_int mod p ---- *)

Local Definition MX_int (n:nat) (X:mat) : 'M[int]_n :=
  \matrix_(i, j) Z_to_int (getH X i j).

Local Lemma MXFp_eq_mapint p n X :
  MXFp p n X = map_mx (intr : int -> 'F_(Z.to_nat p)) (MX_int n X).
Proof. by apply/matrixP => i j; rewrite !mxE /Z_to_Fp. Qed.

Local Lemma mat_int_to_rat_eq n X :
  mat_int_to_rat X 1 n = map_mx (intr : int -> rat) (MX_int n X).
Proof. by apply/matrixP => i j; rewrite !mxE Z_to_int_1 rmorph1 divr1. Qed.

Local Lemma seqnth_listmap (l : list Z) (i : nat) :
  seq.nth (0%R : rat) (List.map (fun z => (Z_to_int z)%:~R : rat) l) i
  = ((Z_to_int (List.nth i l 0%Z))%:~R : rat).
Proof.
elim: l i => [|z l IH] i.
- by rewrite nth_nil; case: i => [|i] /=.
- by case: i => [|i] //=.
Qed.

Local Lemma cp_MXFp_coef p (Hp:Znumtheory.prime p) n X i :
  mat_dim X = n ->
  (forall j, (j < length X)%coq_nat -> length (nth j X []) = n) ->
  ((char_poly (MXFp p n X))`_i
   = Z_to_Fp p (List.nth i (char_poly_int X) 0%Z))%R.
Proof.
move=> Hdim Hwf.
have Hmap : map_poly (intr:int->rat) (char_poly (MX_int n X))
            = pol_to_polyrat (char_poly_int X).
{ by rewrite map_char_poly -mat_int_to_rat_eq
            -(@char_poly_int_correct X n Hdim Hwf). }
have Hci := congr1 (fun q : {poly rat} => q`_i) Hmap.
rewrite coef_map /pol_to_polyrat coef_Poly seqnth_listmap in Hci.
have Hint := intr_inj Hci.
rewrite MXFp_eq_mapint -map_char_poly coef_map Hint.
by rewrite /Z_to_Fp.
Qed.

Local Lemma fl_loop_length steps k A I_n M c acc :
  length (fl_loop steps k A I_n M c acc) = (steps + length acc)%coq_nat.
Proof.
elim: steps k A I_n M c acc => [|s IH] k A I_n M c acc; first by [].
rewrite [fl_loop _ _ _ _ _ _ _]/=.
rewrite IH /=. lia.
Qed.

Local Lemma char_poly_int_length X :
  length (char_poly_int X) = (mat_dim X + 1)%coq_nat.
Proof. by rewrite /char_poly_int length_app fl_loop_length /=; lia. Qed.

(* ================================================================== *)
(* Section 5c: the upper-Hessenberg shape invariant of hess_reduce    *)
(*                                                                     *)
(* hess_reduce p M = Some H makes H upper-Hessenberg mod p: every      *)
(* entry strictly below the subdiagonal is 0 mod p (hess_reduce_shape).*)
(* The argument tracks, over 'F_p, that each hess_elim_step (a) clears *)
(* its target entry via the pivot-inverse identity (Fermat), (b)       *)
(* preserves all already-created zeros, and (c) preserves the pivot    *)
(* entry; folded over hess_inner / hess_outer this zeroes columns      *)
(* 0..n-3 one at a time.                                               *)
(* ================================================================== *)

(* ---- invmodZ over 'F_p : (invmodZ p a) is the inverse of a ---- *)

Local Lemma mh_pow_xI (b : Z) (pos : positive) :
  b * (b ^ Z.pos pos * b ^ Z.pos pos) = b ^ Z.pos pos~1.
Proof.
change (Z.pos pos~1) with (2 * Z.pos pos + 1)%Z.
replace (2 * Z.pos pos + 1)%Z with (1 + Z.pos pos + Z.pos pos)%Z by lia.
rewrite Z.pow_add_r; [|lia|lia].
rewrite Z.pow_add_r; [|lia|lia].
rewrite Z.pow_1_r. ring.
Qed.

Local Lemma mh_pow_xO (b : Z) (pos : positive) :
  b ^ Z.pos pos * b ^ Z.pos pos = b ^ Z.pos pos~0.
Proof.
change (Z.pos pos~0) with (2 * Z.pos pos)%Z.
replace (2 * Z.pos pos)%Z with (Z.pos pos + Z.pos pos)%Z by lia.
rewrite Z.pow_add_r; [|lia|lia]. reflexivity.
Qed.

Local Lemma mh_powpos_spec (p base : Z) (e : positive) :
  (0 < p)%Z -> powmodZ_pos p base e = (base ^ Z.pos e) mod p.
Proof.
move=> Hp. elim: e => [e IH|e IH|].
- cbn [powmodZ_pos]. unfold mulmodZ. rewrite IH.
  rewrite <- Zmult_mod. rewrite Zmult_mod_idemp_r. rewrite mh_pow_xI. reflexivity.
- cbn [powmodZ_pos]. unfold mulmodZ. rewrite IH.
  rewrite <- Zmult_mod. rewrite mh_pow_xO. reflexivity.
- cbn [powmodZ_pos]. change (Z.pos 1) with 1%Z. rewrite Z.pow_1_r. reflexivity.
Qed.

Local Lemma mh_invmod_spec (p a : Z) :
  (2 < p)%Z -> invmodZ p a = (a ^ (p - 2)) mod p.
Proof.
move=> Hp. unfold invmodZ.
remember (p - 2)%Z as e eqn:E.
destruct e as [|q|q]; try lia.
cbn [powmodZ]. rewrite (mh_powpos_spec p a q ltac:(lia)). reflexivity.
Qed.

Local Lemma Z_to_Fp_one p : Z_to_Fp p 1 = 1%R.
Proof. by rewrite /Z_to_Fp Z_to_int_1 rmorph1. Qed.

Local Lemma Z_to_Fp_eq0 p (Hp:Znumtheory.prime p) z :
  Z_to_Fp p z = 0%R <-> (z mod p = 0)%Z.
Proof.
have Hp0 : (p <> 0)%Z by destruct Hp; lia.
split=> H.
- have E := Z_to_Fp_eqmod p Hp z 0.
  rewrite Z_to_Fp_0 in E. move: (E H). by rewrite Z.mod_0_l.
- by rewrite -(Z_to_Fp_mod p Hp z) H Z_to_Fp_0.
Qed.

Local Lemma Z_to_Fp_invmod p (Hp:Znumtheory.prime p) :
  (2 < p)%Z ->
  forall a, (a mod p <> 0)%Z ->
  (Z_to_Fp p (invmodZ p a) * Z_to_Fp p a = 1)%R.
Proof.
move=> Hp2 a Ha.
have Hp1 : (1 < p)%Z by lia.
have Hpr : prime (Z.to_nat p) by apply Zprime_to_ssrprime; [lia | exact Hp].
have Hb := Z.mod_pos_bound a p ltac:(lia).
have Hpos : (0 < a mod p < p)%Z by lia.
have HF := fermat_Z p Hp1 Hpr (a mod p) Hpos.
have Hmod1 : ((a ^ (p - 2) * a) mod p = 1)%Z.
{ rewrite Z.mul_comm Z.mul_mod; [|lia].
  rewrite -Z.mod_pow_l Z.mul_mod_idemp_r; [|lia].
  by rewrite HF Z.mod_1_l. }
rewrite (mh_invmod_spec p a Hp2) Z_to_Fp_mod // -Z_to_Fp_mul.
by rewrite -(Z_to_Fp_mod p Hp (a ^ (p-2) * a)) Hmod1 Z_to_Fp_one.
Qed.

(* ---- "columns < k are Hessenberg-clean mod p" predicate ---- *)

Local Definition FpHessUpto (p:Z) (n k:nat) (A:mat) : Prop :=
  forall a b : nat, (b < k)%coq_nat -> (S b < a)%coq_nat -> (a < n)%coq_nat ->
    Z_to_Fp p (getH A a b) = 0%R.

(* ---- one elimination step: clears its target, keeps everything else ---- *)

Local Lemma step_clears p (Hp:Znumtheory.prime p) n k i pinv A :
  goodA n A -> (S k < n)%coq_nat -> (i < n)%coq_nat ->
  (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R ->
  Z_to_Fp p (getH (hess_elim_step p A (S k) i (mulmodZ p (getH A i k) pinv)) i k)
  = 0%R.
Proof.
move=> [HlenA Hrows] Hk Hi Hpiv.
have Hrows' : forall c, (c < length A)%coq_nat -> length (nth c A []) = length A
  by rewrite HlenA.
rewrite (ZF_getH_elim p Hp A (S k) i (mulmodZ p (getH A i k) pinv) i k
  ltac:(rewrite HlenA; exact Hi) ltac:(rewrite HlenA; exact Hk)
  ltac:(rewrite HlenA; exact Hi) Hrows').
rewrite eqxx.
have -> : (k == k.+1) = false by apply/eqP; lia.
rewrite Z_to_Fp_mulmod //.
rewrite !mulrb !mul1r ?mul0r ?mulr0 ?addr0 ?subr0 -mulrA Hpiv mulr1 subrr.
reflexivity.
Qed.

Local Lemma step_keep p (Hp:Znumtheory.prime p) n k1 i m a b A :
  goodA n A -> (k1 < n)%coq_nat -> (i < n)%coq_nat -> (a < n)%coq_nat ->
  a <> i -> b <> k1 ->
  Z_to_Fp p (getH (hess_elim_step p A k1 i m) a b) = Z_to_Fp p (getH A a b).
Proof.
move=> [HlenA Hrows] Hk1 Hi Ha Hai Hbk.
have Hrows' : forall c, (c < length A)%coq_nat -> length (nth c A []) = length A
  by rewrite HlenA.
rewrite (ZF_getH_elim p Hp A k1 i m a b
  ltac:(rewrite HlenA; exact Hi) ltac:(rewrite HlenA; exact Hk1)
  ltac:(rewrite HlenA; exact Ha) Hrows').
move: Hai => /eqP/negbTE ->.
move: Hbk => /eqP/negbTE ->.
rewrite !mulr0n !mul0r ?mulr0 ?addr0 ?subr0.
reflexivity.
Qed.

Local Lemma step_FpHessUpto p (Hp:Znumtheory.prime p) n k i m A :
  goodA n A -> (S k < n)%coq_nat -> (i < n)%coq_nat ->
  FpHessUpto p n k A ->
  FpHessUpto p n k (hess_elim_step p A (S k) i m).
Proof.
move=> [HlenA Hrows] Hk Hi Hclean a b Hbk Hba Han.
have Hrows' : forall c, (c < length A)%coq_nat -> length (nth c A []) = length A
  by rewrite HlenA.
rewrite (ZF_getH_elim p Hp A (S k) i m a b
  ltac:(rewrite HlenA; exact Hi) ltac:(rewrite HlenA; exact Hk)
  ltac:(rewrite HlenA; exact Han) Hrows').
have -> : (b == k.+1) = false by apply/eqP; lia.
rewrite (Hclean a b Hbk Hba Han).
rewrite (Hclean (S k) b Hbk ltac:(lia) Hk).
rewrite !mulr0n ?mulr0 ?mul0r ?addr0 ?subr0.
reflexivity.
Qed.

(* ---- fold (hess_inner) over a column: clears it, preserves the rest ---- *)

Local Lemma hess_inner_cons p A k pinv i0 rest :
  hess_inner p A k pinv (i0 :: rest)
  = hess_inner p (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv))
      k pinv rest.
Proof. by []. Qed.

Local Lemma hess_inner_pres_colk p (Hp:Znumtheory.prime p) n k pinv :
  (S k < n)%coq_nat ->
  forall il A r,
    goodA n A ->
    (forall i, In i il -> (i < n)%coq_nat) ->
    ~ In r il ->
    (r < n)%coq_nat ->
    Z_to_Fp p (getH (hess_inner p A k pinv il) r k) = Z_to_Fp p (getH A r k).
Proof.
move=> Hk.
elim => [|i0 rest IH] A r HA Hin Hrin Hr; first by [].
rewrite hess_inner_cons.
have Hi0 : (i0 < n)%coq_nat by apply: Hin; left.
have HA' : goodA n (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv))
  by apply: good_elim_step.
have Hin' : forall i, In i rest -> (i < n)%coq_nat by move=> j Hj; apply: Hin; right.
have Hrin' : ~ In r rest by move=> Hj; apply: Hrin; right.
rewrite (IH _ r HA' Hin' Hrin' Hr).
apply: (step_keep p Hp n (S k) i0 (mulmodZ p (getH A i0 k) pinv) r k A) => //.
by move=> E; apply: Hrin; left; rewrite E.
Qed.

Local Lemma hess_inner_shape p (Hp:Znumtheory.prime p) n k pinv :
  (S k < n)%coq_nat ->
  forall il A,
    goodA n A ->
    (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R ->
    FpHessUpto p n k A ->
    (forall i, In i il -> (S k < i)%coq_nat /\ (i < n)%coq_nat) ->
    NoDup il ->
    FpHessUpto p n k (hess_inner p A k pinv il)
    /\ Z_to_Fp p (getH (hess_inner p A k pinv il) (S k) k)
       = Z_to_Fp p (getH A (S k) k)
    /\ (forall i, In i il ->
          Z_to_Fp p (getH (hess_inner p A k pinv il) i k) = 0%R).
Proof.
move=> Hk.
elim => [|i0 rest IH] A HA Hpiv Hclean Hin Hnodup.
- split; [exact Hclean | split; [reflexivity | by move=> i [] ]].
- rewrite hess_inner_cons.
  move: Hnodup => /NoDup_cons_iff [Hni0 Hndrest].
  have Hi0 : (S k < i0)%coq_nat /\ (i0 < n)%coq_nat by apply: Hin; left.
  have Hi0n : (i0 < n)%coq_nat by apply (proj2 Hi0).
  have HA1 : goodA n (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv))
    by apply: good_elim_step.
  have Hpiv1eq : Z_to_Fp p
      (getH (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) (S k) k)
      = Z_to_Fp p (getH A (S k) k).
  { apply: (step_keep p Hp n (S k) i0 (mulmodZ p (getH A i0 k) pinv) (S k) k A) => //.
    by move=> E; move: (proj1 Hi0); rewrite E; lia. }
  have Hpiv1 : (Z_to_Fp p pinv *
      Z_to_Fp p
        (getH (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) (S k) k)
      = 1)%R by rewrite Hpiv1eq.
  have HcleanA1 : FpHessUpto p n k
      (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv))
    by apply: step_FpHessUpto.
  have Hinr : forall i, In i rest -> (S k < i)%coq_nat /\ (i < n)%coq_nat
    by move=> i Hi; apply: Hin; right.
  have Hinrn : forall i, In i rest -> (i < n)%coq_nat
    by move=> i Hi; apply (proj2 (Hinr i Hi)).
  have [IHclean [IHpiv IHrows]] :=
    IH _ HA1 Hpiv1 HcleanA1 Hinr Hndrest.
  split; first exact IHclean.
  split.
  + by rewrite IHpiv Hpiv1eq.
  + move=> i [Hii0 | Hir].
    * rewrite -Hii0.
      rewrite (hess_inner_pres_colk p Hp n k pinv Hk rest
        (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) i0
        HA1 Hinrn Hni0 Hi0n).
      by apply: (step_clears p Hp n k i0 pinv A).
    * by apply: IHrows.
Qed.

(* ---- a cleared column k, atop clean columns < k, gives clean columns < k+1 ---- *)

Local Lemma extend_clean p n k A (il : list nat) :
  FpHessUpto p n k A ->
  (forall i, (S k < i)%coq_nat -> (i < n)%coq_nat -> In i il) ->
  (forall i, In i il -> Z_to_Fp p (getH A i k) = 0%R) ->
  FpHessUpto p n (k.+1) A.
Proof.
move=> Hck Hcov Hrow a b Hbk1 Hba Han.
case: (Nat.eq_dec b k) => [Heq|Hne].
- subst b. apply: Hrow; apply: Hcov; lia.
- apply: Hck; lia.
Qed.

(* ---- outer sweep: processing columns k0 .. extends the clean prefix ---- *)

Local Lemma hess_outer_cons p A n k ks' :
  hess_outer p A n (k :: ks') =
  (if Z.eqb (getH A (S k) k mod p) 0 then None
   else hess_outer p
          (hess_inner p A k (invmodZ p (getH A (S k) k))
             (List.seq (k + 2)%coq_nat (n - (k + 2))%coq_nat)) n ks').
Proof. by []. Qed.

Local Lemma hess_outer_shape p (Hp:Znumtheory.prime p) (Hp2:(2<p)%Z) n :
  forall ks k0 A H,
    ks = List.seq k0 (length ks) ->
    (forall k, In k ks -> (S k < n)%coq_nat) ->
    goodA n A ->
    FpHessUpto p n k0 A ->
    hess_outer p A n ks = Some H ->
    FpHessUpto p n (k0 + length ks)%coq_nat H.
Proof.
elim => [|k ks' IH] k0 A H Hseq Hin HA Hclean Hsome.
- move: Hsome => /= [= <-]. by rewrite Nat.add_0_r.
- move: Hseq; rewrite /= => [= Hk0 Hseq']; subst k0.
  rewrite hess_outer_cons in Hsome.
  have Hkn : (S k < n)%coq_nat by apply: Hin; left.
  destruct (Z.eqb (getH A (S k) k mod p) 0) eqn:Heqb; first by [].
  have Hpivne : (getH A (S k) k mod p <> 0)%Z by move/Z.eqb_neq: Heqb.
  set pinv := invmodZ p (getH A (S k) k) in Hsome *.
  set sq := List.seq (k + 2)%coq_nat (n - (k + 2))%coq_nat in Hsome *.
  set A' := hess_inner p A k pinv sq in Hsome *.
  have HpivR : (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R
    by apply: Z_to_Fp_invmod.
  have Hincond : forall i, In i sq -> (S k < i)%coq_nat /\ (i < n)%coq_nat.
  { move=> i; rewrite /sq in_seq => Hi. lia. }
  have Hnodupsq : NoDup sq by rewrite /sq; apply: List.seq_NoDup.
  have [Hclean' [_ Hrows']] :=
    hess_inner_shape p Hp n k pinv Hkn sq A HA HpivR Hclean Hincond Hnodupsq.
  have HcleanK1 : FpHessUpto p n (k.+1) A'.
  { apply: (extend_clean p n k A' sq Hclean').
    - move=> i Hi1 Hi2; rewrite /sq in_seq; lia.
    - exact Hrows'. }
  have [HgA' _] := hess_inner_ok p Hp n k pinv sq Hkn (seq_inner_cond k n) A HA.
  have Hin' : forall j, In j ks' -> (S j < n)%coq_nat by move=> j Hj; apply: Hin; right.
  have E : (k + length (k :: ks'))%coq_nat = (k.+1 + length ks')%coq_nat
    by rewrite /=; lia.
  rewrite E.
  exact: (IH (k.+1) A' H Hseq' Hin' HgA' HcleanK1 Hsome).
Qed.

(* ---- main shape invariant: the reduced matrix is upper-Hessenberg mod p ---- *)

Local Lemma hess_reduce_shape p (Hp:Znumtheory.prime p) (Hp2:(2<p)%Z) M H :
  square_mat (length M) M ->
  hess_reduce p M = Some H ->
  forall i j : nat, (j.+1 < i)%N -> (getH H i j mod p = 0)%Z.
Proof.
move=> Hsq Hred i j /ltP Hji.
have Hp0 : (p <> 0)%Z by destruct Hp; lia.
have HgM : goodA (length M) M by apply: square_goodA.
case: Hsq => Hdim Hrows.
have HgR : goodA (length M) (reduceZ p M) by apply: goodA_reduceZ.
move: Hred; rewrite /hess_reduce Hdim => Hred.
have Hlenks : length (List.seq 0 (length M - 2)) = (length M - 2)%coq_nat
  by apply: length_seq.
have Hseq : List.seq 0 (length M - 2)
          = List.seq 0 (length (List.seq 0 (length M - 2))) by rewrite Hlenks.
have Hclean0 : FpHessUpto p (length M) 0 (reduceZ p M) by move=> a b Hb0; lia.
have Hshape := hess_outer_shape p Hp Hp2 (length M) (List.seq 0 (length M - 2)) 0
  (reduceZ p M) H Hseq (ks_cond (length M)) HgR Hclean0 Hred.
rewrite Hlenks in Hshape.
have [HgH _] := hess_outer_ok p Hp (length M) (List.seq 0 (length M - 2))
  (ks_cond (length M)) (reduceZ p M) H HgR Hred.
case: HgH => HlenH _.
case: (le_lt_dec (length M) i) => [Hin|Hin].
- rewrite /getH.
  have Hov : nth i H [] = [] by apply: List.nth_overflow; rewrite HlenH; lia.
  rewrite Hov nth_Z_nil.
  by apply: Z.mod_0_l.
- apply: (proj1 (Z_to_Fp_eq0 p Hp (getH H i j))).
  apply: Hshape; lia.
Qed.

(* ================================================================== *)
(* Section 5d: list-Z <-> {poly 'F_p} bridge (recurrence = det)        *)
(*                                                                     *)
(* `Lpoly l` embeds a low-to-high list-Z polynomial into {poly 'F_p}   *)
(* coefficientwise via Z_to_Fp.  We show the modular list ops          *)
(* (vaddZ, vscaleZ, pnegZ, psubZ, pmulXsub) correspond to the poly     *)
(* ring ops, then relate hess_fold / hess_pk / hess_build to the       *)
(* abstract Hessenberg determinant recurrence (Dlead_rec / Dlead_full) *)
(* instantiated at char_poly_mx (MXFp p n H).                          *)
(* ================================================================== *)

(* ---- hess_build: the p_k list is prefix-stable and obeys the recurrence ---- *)

Local Lemma hess_pk_congr (p : Z) (H : mat) (k : nat) (l1 l2 : list (list Z)) :
  (0 < k)%coq_nat ->
  (forall i, (i < k)%coq_nat -> List.nth i l1 [] = List.nth i l2 []) ->
  hess_pk p H k l1 = hess_pk p H k l2.
Proof.
move=> Hk Hagree; rewrite /hess_pk.
have E1 : List.nth (k - 1) l1 [] = List.nth (k - 1) l2 []
  by apply: Hagree; lia.
have E2 :
  List.map (fun i => (getH H i (k - 1), getH H (i + 1) i, List.nth i l1 []))
           (List.seq 0 (k - 1))
  = List.map (fun i => (getH H i (k - 1), getH H (i + 1) i, List.nth i l2 []))
           (List.seq 0 (k - 1)).
{ apply: List.map_ext_in => x Hx.
  apply List.in_seq in Hx.
  by rewrite (Hagree x ltac:(lia)). }
by rewrite E1 E2.
Qed.

Local Lemma hess_build_length (p : Z) (H : mat) steps ps :
  length (hess_build p H steps ps) = (length ps + steps)%coq_nat.
Proof.
elim: steps ps => [|s IH] ps; first by rewrite /= Nat.add_0_r.
rewrite /= IH List.length_app /=; lia.
Qed.

Local Lemma hess_build_prefix (p : Z) (H : mat) steps ps k :
  (k < length ps)%coq_nat ->
  List.nth k (hess_build p H steps ps) [] = List.nth k ps [].
Proof.
elim: steps ps k => [|s IH] ps k Hk; first by [].
simpl.
rewrite (IH (ps ++ [hess_pk p H (length ps) ps]) k);
  last by rewrite List.length_app /=; lia.
by rewrite List.app_nth1.
Qed.

Local Lemma hess_build_nth_rec (p : Z) (H : mat) steps ps k :
  (0 < k)%coq_nat ->
  (length ps <= k)%coq_nat -> (k < length ps + steps)%coq_nat ->
  List.nth k (hess_build p H steps ps) []
  = hess_pk p H k (hess_build p H steps ps).
Proof.
elim: steps ps k => [|s IH] ps k Hk Hge Hlt; first by lia.
simpl.
set x := hess_pk p H (length ps) ps.
have Hps' : length (ps ++ [x]) = (length ps + 1)%coq_nat
  by rewrite List.length_app /=.
case: (Nat.eq_dec k (length ps)) => [Heq | Hne].
- rewrite Heq.
  rewrite hess_build_prefix; last by rewrite Hps'; lia.
  rewrite List.app_nth2; last by lia.
  rewrite Nat.sub_diag /= /x.
  apply: hess_pk_congr; first by lia.
  move=> i Hi.
  rewrite hess_build_prefix; last by rewrite Hps'; lia.
  by rewrite List.app_nth1 //; lia.
- rewrite (IH (ps ++ [x]) k Hk);
    [ by [] | rewrite Hps'; lia | rewrite Hps'; lia ].
Qed.

Section DetCore.
Local Open Scope ring_scope.
Variable p : Z.
Hypothesis Hp : Znumtheory.prime p.

Local Notation FF := 'F_(Z.to_nat p).
Local Notation RR := {poly FF}.

Local Definition Lpoly (l : list Z) : RR := Poly (List.map (Z_to_Fp p) l).

Local Lemma Lpoly_coef l i : (Lpoly l)`_i = Z_to_Fp p (nth_Z l i).
Proof.
rewrite coef_Poly /nth_Z.
elim: l i => [|z l IH] [|i] /=.
- by rewrite Z_to_Fp_0.
- by rewrite Z_to_Fp_0.
- by [].
- exact: IH.
Qed.

Local Lemma Lpoly_vaddZ a b : Lpoly (vaddZ p a b) = Lpoly a + Lpoly b.
Proof. by apply/polyP => i; rewrite coefD !Lpoly_coef (ZF_nth_vaddZ p Hp). Qed.

Local Lemma Lpoly_pnegZ a : Lpoly (pnegZ p a) = - Lpoly a.
Proof. by apply/polyP => i; rewrite coefN !Lpoly_coef (ZF_nth_pnegZ p Hp). Qed.

Local Lemma Lpoly_psubZ a b : Lpoly (psubZ p a b) = Lpoly a - Lpoly b.
Proof. by rewrite /psubZ Lpoly_vaddZ Lpoly_pnegZ. Qed.

Local Lemma Lpoly_vscaleZ c a :
  Lpoly (vscaleZ p c a) = (Z_to_Fp p c)%:P * Lpoly a.
Proof.
by apply/polyP => i; rewrite coefCM !Lpoly_coef (ZF_nth_vscaleZ p Hp).
Qed.

Local Lemma Lpoly_cons0 q : Lpoly (0%Z :: q) = Lpoly q * 'X.
Proof.
apply/polyP => i; rewrite coefMX Lpoly_coef.
case: i => [|i] /=; first by rewrite Z_to_Fp_0.
by rewrite Lpoly_coef.
Qed.

Local Lemma Lpoly_pmulXsub a q :
  Lpoly (pmulXsub p a q) = ('X - (Z_to_Fp p a)%:P) * Lpoly q.
Proof.
rewrite /pmulXsub Lpoly_vaddZ Lpoly_cons0 Lpoly_vscaleZ (Z_to_Fp_negmod p Hp).
by rewrite polyCN mulNr mulrBl [Lpoly q * 'X]mulrC.
Qed.

(* ---- hess_fold: suffix-product / sum accumulators ---- *)

Local Notation dft := (0%Z, 0%Z, @nil Z).

Local Lemma hess_fold_cons h sub pi L :
  hess_fold p ((h, sub, pi) :: L)
  = (mulmodZ p sub (fst (hess_fold p L)),
     vaddZ p (vscaleZ p (mulmodZ p h (mulmodZ p sub (fst (hess_fold p L)))) pi)
             (snd (hess_fold p L))).
Proof. by []. Qed.

Local Lemma hess_fold_fst L :
  Z_to_Fp p (fst (hess_fold p L)) = \prod_(t <- L) Z_to_Fp p t.1.2.
Proof.
elim: L => [|[[h sub] pi] L IH].
- by rewrite big_nil /= (Z_to_Fp_mod p Hp) Z_to_Fp_one.
- by rewrite hess_fold_cons big_cons /= (Z_to_Fp_mulmod p Hp) IH.
Qed.

Local Lemma hess_fold_snd L :
  Lpoly (snd (hess_fold p L))
  = \sum_(k < size L)
      (Z_to_Fp p (seq.nth dft L k).1.1)%:P
      * (\prod_(k <= j < size L) Z_to_Fp p (seq.nth dft L j).1.2)%:P
      * Lpoly (seq.nth dft L k).2.
Proof.
elim: L => [|[[h sub] pi] L IH].
- by rewrite /= big_ord0.
- rewrite hess_fold_cons /= Lpoly_vaddZ Lpoly_vscaleZ IH.
  rewrite big_ord_recl /=.
  congr (_ + _).
  + rewrite (Z_to_Fp_mulmod p Hp) (Z_to_Fp_mulmod p Hp).
    rewrite hess_fold_fst (big_nth dft).
    rewrite big_nat_recl //=.
    by rewrite polyCM.
  + apply: eq_bigr => k _.
    by rewrite big_add1.
Qed.

End DetCore.

(* ================================================================== *)
(* Section 5e: the recurrence-vs-determinant bridge                    *)
(*                                                                     *)
(* For an upper-Hessenberg-mod-p matrix H (read off entrywise via      *)
(* getH / MXFp, so NO well-formedness is needed), the Hessenberg       *)
(* recurrence `hess_charpoly p H N.+1`, embedded coefficientwise into  *)
(* {poly 'F_p}, equals char_poly (MXFp p N.+1 H).  The proof inducts   *)
(* on the leading-principal index, matching hess_pk / hess_fold to the *)
(* abstract recurrence Dlead_rec term-for-term (RB_term), and ties     *)
(* p_{N.+1} to det via Dlead_full (RB_core).                           *)
(* ================================================================== *)

Section RecBridge.
Local Open Scope ring_scope.
Variable p : Z.
Hypothesis Hp : Znumtheory.prime p.
Variable H : mat.
Variable N : nat.
Local Notation n := N.+1.
Local Notation MH := (MXFp p n H).
Local Notation AA := (char_poly_mx MH).
Hypothesis Hshape : forall i j : nat, (j.+1 < i)%N -> Z_to_Fp p (getH H i j) = 0%R.

Lemma RB_Ahess : forall i j : 'I_n, (j.+1 < i)%N -> AA i j = 0.
Proof.
move=> i j Hji.
rewrite /char_poly_mx !mxE.
have Hij : (i == j) = false.
  apply/negbTE; rewrite neq_ltn; apply/orP; right.
  exact: ltn_trans (ltnSn j) Hji.
by rewrite Hij mulr0n (Hshape i j Hji) raddf0 add0r.
Qed.

Lemma RB_inordK (k:nat) : (k < n)%N -> nat_of_ord (inord k : 'I_n) = k.
Proof. by move=> Hk; rewrite inordK. Qed.

Lemma RB_diag (m:nat) : (m < n)%N ->
  AA (inord m) (inord m) = 'X - (Z_to_Fp p (getH H m m))%:P.
Proof.
move=> Hm.
rewrite /char_poly_mx !mxE eqxx mulr1n.
by rewrite !RB_inordK.
Qed.

Lemma RB_off (a b:nat) : a <> b -> (a<n)%N -> (b<n)%N ->
  AA (inord a) (inord b) = - (Z_to_Fp p (getH H a b))%:P.
Proof.
move=> Hab Ha Hb.
rewrite /char_poly_mx !mxE.
have Hne : (inord a == inord b :> 'I_n) = false.
  apply/negbTE/eqP => E; apply: Hab.
  by rewrite -(RB_inordK a Ha) -(RB_inordK b Hb) E.
rewrite Hne mulr0n !RB_inordK // sub0r.
by [].
Qed.

Lemma RB_size_map_seq {T} (f:nat->T) (a c:nat) :
  size (List.map f (List.seq a c)) = c.
Proof. elim: c a => [|c IH] a //=. by rewrite IH. Qed.

Lemma RB_seqnth_map_seq (f:nat -> Z*Z*list Z) (a c idx:nat) :
  (idx < c)%N ->
  seq.nth (0%Z,0%Z,@nil Z) (List.map f (List.seq a c)) idx = f (a + idx)%nat.
Proof.
elim: c a idx => [|c IH] a idx; first by rewrite ltn0.
case: idx => [|idx]; rewrite /= => Hidx.
- by rewrite addn0.
- rewrite IH; last by move: Hidx; rewrite ltnS.
  by rewrite addSnnS.
Qed.

Lemma RB_Lpoly_one : Lpoly p [:: (1 mod p)%Z] = 1%R.
Proof.
apply/polyP => i; rewrite Lpoly_coef coef1.
case: i => [|i].
- by rewrite /nth_Z /= (Z_to_Fp_mod p Hp) Z_to_Fp_one.
- by rewrite /nth_Z /=; case: i => [|i] /=; rewrite Z_to_Fp_0.
Qed.

Lemma RB_Dlead0 :
  Dlead [the comNzRingType of {poly 'F_(Z.to_nat p)}] N AA 0 = 1%R.
Proof. by rewrite /Dlead det_mx00. Qed.

Lemma RB_prodN (i0 b0:nat) (F:nat -> {poly 'F_(Z.to_nat p)}) :
  (\prod_(i0 <= j < b0) (- F j) = (-1)^+(b0 - i0) * \prod_(i0 <= j < b0) F j)%R.
Proof.
transitivity (\prod_(i0 <= j < b0) ((-1 : {poly 'F_(Z.to_nat p)}) * F j))%R.
  by apply: eq_bigr => j _; rewrite mulN1r.
by rewrite big_split prodr_const_nat.
Qed.

Local Notation DL := (Dlead [the comNzRingType of {poly 'F_(Z.to_nat p)}] N AA).

Lemma RB_term (i b:nat) : (i < b)%N -> (b < n)%N ->
  (AA (inord i) (inord b) * (-1)^+(i+b)%N
     * (\prod_(i <= j < b) AA (inord j.+1) (inord j)) * DL i
   = - ((Z_to_Fp p (getH H i b))%:P
        * (\prod_(i <= j < b) Z_to_Fp p (getH H j.+1 j))%:P * DL i))%R.
Proof.
move=> Hib Hbn.
have Hin : (i < n)%N by apply: (ltn_trans Hib Hbn).
have Hibne : i <> b by move=> E; move: Hib; rewrite E ltnn.
rewrite (RB_off i b Hibne Hin Hbn).
under eq_big_nat => j /andP[_ Hjb].
  have Hjn : (j < n)%N by apply: (ltn_trans Hjb Hbn).
  have Hj1n : (j.+1 < n)%N by apply: (leq_ltn_trans Hjb Hbn).
  have Hne : j.+1 <> j by lia.
  rewrite (RB_off j.+1 j Hne Hj1n Hjn).
  over.
rewrite RB_prodN -rmorph_prod.
have Hsg : ((-1:{poly 'F_(Z.to_nat p)})^+(i+b) * (-1)^+(b-i) = 1)%R.
  rewrite -exprD (addnC i b) -addnA subnKC ?(ltnW Hib) //.
  by rewrite addnn -muln2 exprM sqrr_sign.
rewrite !mulNr; congr (- _).
rewrite -!mulrA; congr (_ * _).
by rewrite mulrA Hsg mul1r.
Qed.

Local Notation PB := (hess_build p H N.+1 [:: [:: (1 mod p)%Z]]).

Lemma RB_main_aux : forall c k, (k <= c)%N -> (k <= n)%N ->
  Lpoly p (nth k PB []) = DL k.
Proof.
elim => [|c IH] k.
- rewrite leqn0 => /eqP -> _.
  rewrite (hess_build_prefix p H n [:: [:: (1 mod p)%Z]] 0); last by (simpl; lia).
  by rewrite /= RB_Lpoly_one RB_Dlead0.
- move=> Hkc Hkn; move: Hkc; rewrite leq_eqVlt => /orP[/eqP Hk | Hk]; last first.
  + rewrite ltnS in Hk. by apply: IH.
  + subst k.
    have Hcn' : (c.+1 <= n)%coq_nat by apply/leP.
    have Hcn : (c < n)%N by rewrite -ltnS.
    rewrite (hess_build_nth_rec p H n [:: [:: (1 mod p)%Z]] c.+1);
      [|lia|simpl;lia|simpl;lia].
    rewrite /hess_pk.
    have Hcol : (c.+1 - 1)%coq_nat = c by lia.
    rewrite !Hcol.
    rewrite Lpoly_psubZ // Lpoly_pmulXsub // hess_fold_snd // RB_size_map_seq.
    under eq_bigr => k0 _.
      rewrite (RB_seqnth_map_seq _ 0 c k0 (ltn_ord k0)) add0n.
      cbn [fst snd].
      rewrite (IH k0 (ltnW (ltn_ord k0)) (ltnW (ltn_trans (ltn_ord k0) Hcn))).
      under eq_big_nat => j /andP[_ Hhi].
        rewrite (RB_seqnth_map_seq _ 0 c j Hhi) add0n Nat.add_1_r.
        cbn [fst snd].
        over.
      over.
    rewrite (Dlead_rec [the comNzRingType of {poly 'F_(Z.to_nat p)}]
                       N AA RB_Ahess c Hcn).
    rewrite (RB_diag c Hcn).
    rewrite (IH c (leqnn c) (ltnW Hcn)).
    under [X in _ = _ + X] eq_bigr => i _.
      rewrite (RB_term i c (ltn_ord i) Hcn).
      over.
    rewrite sumrN.
    by [].
Qed.

Lemma RB_core : Lpoly p (hess_charpoly p H N.+1) = char_poly MH.
Proof.
rewrite /hess_charpoly.
rewrite (RB_main_aux N.+1 N.+1 (leqnn N.+1) (leqnn N.+1)).
by rewrite Dlead_full.
Qed.

End RecBridge.

(* ================================================================== *)
(* Section 5f: ragged-tolerant upper-Hessenberg shape invariant        *)
(*                                                                     *)
(* The shape invariant of hess_reduce holds WITHOUT any squareness     *)
(* hypothesis on M: every entry strictly below the subdiagonal of the  *)
(* returned H is 0 mod p.  The argument only ever touches entries in    *)
(* columns b <> k+1, where the column elimination-op is a no-op, so the *)
(* single fact `i < length A` (number of rows, preserved throughout)    *)
(* suffices in place of full well-formedness.                          *)
(* ================================================================== *)

Local Lemma ZF_getH_elim_ne p (Hp:Znumtheory.prime p) M k1 i m a b :
  b <> k1 -> (i < length M)%coq_nat ->
  Z_to_Fp p (getH (hess_elim_step p M k1 i m) a b)
  = (Z_to_Fp p (getH M a b)
     - (a==i)%:R * Z_to_Fp p m * Z_to_Fp p (getH M k1 b))%R.
Proof.
move=> Hbk Hi.
rewrite {1}/getH /hess_elim_step nth_map_eq // nth_Z_upd_other //.
exact: (ZF_nthZ_M1 p Hp M k1 i m a b Hi).
Qed.

Local Lemma length_elim_step p M k1 i m :
  length (hess_elim_step p M k1 i m) = length M.
Proof. by rewrite /hess_elim_step length_map length_upd. Qed.

Local Lemma step_clears_r p (Hp:Znumtheory.prime p) n k i pinv A :
  length A = n -> (S k < n)%coq_nat -> (i < n)%coq_nat ->
  (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R ->
  Z_to_Fp p (getH (hess_elim_step p A (S k) i (mulmodZ p (getH A i k) pinv)) i k)
  = 0%R.
Proof.
move=> HlenA Hk Hi Hpiv.
rewrite (ZF_getH_elim_ne p Hp A (S k) i (mulmodZ p (getH A i k) pinv) i k
  ltac:(lia) ltac:(rewrite HlenA; exact Hi)).
rewrite eqxx mul1r Z_to_Fp_mulmod // -mulrA Hpiv mulr1 subrr.
reflexivity.
Qed.

Local Lemma step_keep_r p (Hp:Znumtheory.prime p) n k1 i m a b A :
  length A = n -> (i < n)%coq_nat -> a <> i -> b <> k1 ->
  Z_to_Fp p (getH (hess_elim_step p A k1 i m) a b) = Z_to_Fp p (getH A a b).
Proof.
move=> HlenA Hi Hai Hbk.
rewrite (ZF_getH_elim_ne p Hp A k1 i m a b Hbk ltac:(rewrite HlenA; exact Hi)).
move: Hai => /eqP/negbTE ->.
by rewrite mul0r mul0r subr0.
Qed.

Local Lemma step_FpHessUpto_r p (Hp:Znumtheory.prime p) n k i m A :
  length A = n -> (S k < n)%coq_nat -> (i < n)%coq_nat ->
  FpHessUpto p n k A ->
  FpHessUpto p n k (hess_elim_step p A (S k) i m).
Proof.
move=> HlenA Hk Hi Hclean a b Hbk Hba Han.
rewrite (ZF_getH_elim_ne p Hp A (S k) i m a b ltac:(lia) ltac:(rewrite HlenA; exact Hi)).
rewrite (Hclean a b Hbk Hba Han).
rewrite (Hclean (S k) b Hbk ltac:(lia) Hk).
by rewrite mulr0 subr0.
Qed.

Local Lemma hess_inner_pres_colk_r p (Hp:Znumtheory.prime p) n k pinv :
  (S k < n)%coq_nat ->
  forall il A r,
    length A = n ->
    (forall i, In i il -> (i < n)%coq_nat) ->
    ~ In r il ->
    (r < n)%coq_nat ->
    Z_to_Fp p (getH (hess_inner p A k pinv il) r k) = Z_to_Fp p (getH A r k).
Proof.
move=> Hk.
elim => [|i0 rest IH] A r HlenA Hin Hrin Hr; first by [].
rewrite hess_inner_cons.
have Hi0 : (i0 < n)%coq_nat by apply: Hin; left.
have HlenA' : length (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) = n
  by rewrite length_elim_step.
have Hin' : forall i, In i rest -> (i < n)%coq_nat by move=> j Hj; apply: Hin; right.
have Hrin' : ~ In r rest by move=> Hj; apply: Hrin; right.
rewrite (IH _ r HlenA' Hin' Hrin' Hr).
apply: (step_keep_r p Hp n (S k) i0 (mulmodZ p (getH A i0 k) pinv) r k A HlenA Hi0).
- by move=> E; apply: Hrin; left; rewrite E.
- lia.
Qed.

Local Lemma hess_inner_shape_r p (Hp:Znumtheory.prime p) n k pinv :
  (S k < n)%coq_nat ->
  forall il A,
    length A = n ->
    (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R ->
    FpHessUpto p n k A ->
    (forall i, In i il -> (S k < i)%coq_nat /\ (i < n)%coq_nat) ->
    NoDup il ->
    FpHessUpto p n k (hess_inner p A k pinv il)
    /\ Z_to_Fp p (getH (hess_inner p A k pinv il) (S k) k)
       = Z_to_Fp p (getH A (S k) k)
    /\ (forall i, In i il ->
          Z_to_Fp p (getH (hess_inner p A k pinv il) i k) = 0%R).
Proof.
move=> Hk.
elim => [|i0 rest IH] A HlenA Hpiv Hclean Hin Hnodup.
- split; [exact Hclean | split; [reflexivity | by move=> i [] ]].
- rewrite hess_inner_cons.
  move: Hnodup => /NoDup_cons_iff [Hni0 Hndrest].
  have Hi0 : (S k < i0)%coq_nat /\ (i0 < n)%coq_nat by apply: Hin; left.
  have Hi0n : (i0 < n)%coq_nat by apply (proj2 Hi0).
  have HlenA1 : length (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) = n
    by rewrite length_elim_step.
  have Hpiv1eq : Z_to_Fp p
      (getH (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) (S k) k)
      = Z_to_Fp p (getH A (S k) k).
  { apply: (step_keep_r p Hp n (S k) i0 (mulmodZ p (getH A i0 k) pinv) (S k) k A
              HlenA Hi0n).
    - by move=> E; move: (proj1 Hi0); rewrite E; lia.
    - lia. }
  have Hpiv1 : (Z_to_Fp p pinv *
      Z_to_Fp p
        (getH (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) (S k) k)
      = 1)%R by rewrite Hpiv1eq.
  have HcleanA1 : FpHessUpto p n k
      (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv))
    by apply: (step_FpHessUpto_r p Hp n k i0 (mulmodZ p (getH A i0 k) pinv) A
                 HlenA Hk Hi0n Hclean).
  have Hinr : forall i, In i rest -> (S k < i)%coq_nat /\ (i < n)%coq_nat
    by move=> i Hi; apply: Hin; right.
  have Hinrn : forall i, In i rest -> (i < n)%coq_nat
    by move=> i Hi; apply (proj2 (Hinr i Hi)).
  have [IHclean [IHpiv IHrows]] := IH _ HlenA1 Hpiv1 HcleanA1 Hinr Hndrest.
  split; first exact IHclean.
  split.
  + by rewrite IHpiv Hpiv1eq.
  + move=> i [Hii0 | Hir].
    * rewrite -Hii0.
      rewrite (hess_inner_pres_colk_r p Hp n k pinv Hk rest
        (hess_elim_step p A (S k) i0 (mulmodZ p (getH A i0 k) pinv)) i0
        HlenA1 Hinrn Hni0 Hi0n).
      by apply: (step_clears_r p Hp n k i0 pinv A HlenA Hk Hi0n Hpiv).
    * by apply: IHrows.
Qed.

Local Lemma hess_inner_length p A k pinv il :
  length (hess_inner p A k pinv il) = length A.
Proof.
rewrite /hess_inner. elim: il A => [|i0 rest IH] A //=.
by rewrite IH length_elim_step.
Qed.

Local Lemma hess_outer_length p n ks :
  forall A H, hess_outer p A n ks = Some H -> length H = length A.
Proof.
elim: ks => [|k ks' IH] A H.
- by move=> /= [= <-].
- rewrite hess_outer_cons. case: ifP => [_ // | _ Hrec].
  by rewrite (IH _ H Hrec) hess_inner_length.
Qed.

Local Lemma hess_outer_shape_r p (Hp:Znumtheory.prime p) (Hp2:(2<p)%Z) n :
  forall ks k0 A H,
    ks = List.seq k0 (length ks) ->
    (forall k, In k ks -> (S k < n)%coq_nat) ->
    length A = n ->
    FpHessUpto p n k0 A ->
    hess_outer p A n ks = Some H ->
    FpHessUpto p n (k0 + length ks)%coq_nat H.
Proof.
elim => [|k ks' IH] k0 A H Hseq Hin HlenA Hclean Hsome.
- move: Hsome => /= [= <-]. by rewrite Nat.add_0_r.
- move: Hseq; rewrite /= => [= Hk0 Hseq']; subst k0.
  rewrite hess_outer_cons in Hsome.
  have Hkn : (S k < n)%coq_nat by apply: Hin; left.
  destruct (Z.eqb (getH A (S k) k mod p) 0) eqn:Heqb; first by [].
  have Hpivne : (getH A (S k) k mod p <> 0)%Z by move/Z.eqb_neq: Heqb.
  set pinv := invmodZ p (getH A (S k) k) in Hsome *.
  set sq := List.seq (k + 2)%coq_nat (n - (k + 2))%coq_nat in Hsome *.
  set A' := hess_inner p A k pinv sq in Hsome *.
  have HpivR : (Z_to_Fp p pinv * Z_to_Fp p (getH A (S k) k) = 1)%R
    by apply: Z_to_Fp_invmod.
  have Hincond : forall i, In i sq -> (S k < i)%coq_nat /\ (i < n)%coq_nat.
  { move=> i; rewrite /sq in_seq => Hi. lia. }
  have Hnodupsq : NoDup sq by rewrite /sq; apply: List.seq_NoDup.
  have [Hclean' [_ Hrows']] :=
    hess_inner_shape_r p Hp n k pinv Hkn sq A HlenA HpivR Hclean Hincond Hnodupsq.
  have HcleanK1 : FpHessUpto p n (k.+1) A'.
  { apply: (extend_clean p n k A' sq Hclean').
    - move=> i Hi1 Hi2; rewrite /sq in_seq; lia.
    - exact Hrows'. }
  have HlenA' : length A' = n by rewrite /A' hess_inner_length.
  have Hin' : forall j, In j ks' -> (S j < n)%coq_nat by move=> j Hj; apply: Hin; right.
  have E : (k + length (k :: ks'))%coq_nat = (k.+1 + length ks')%coq_nat
    by rewrite /=; lia.
  rewrite E.
  exact: (IH (k.+1) A' H Hseq' Hin' HlenA' HcleanK1 Hsome).
Qed.

Local Lemma hess_reduce_shape_r p (Hp:Znumtheory.prime p) (Hp2:(2<p)%Z) M H :
  hess_reduce p M = Some H ->
  forall i j : nat, (j.+1 < i)%N -> (getH H i j mod p = 0)%Z.
Proof.
move=> Hred i j /ltP Hji.
have Hp0 : (p <> 0)%Z by destruct Hp; lia.
set n := mat_dim M.
have HlenR : length (reduceZ p M) = n by rewrite /n /mat_dim /reduceZ length_map.
move: Hred; rewrite /hess_reduce -/n => Hred.
have Hlenks : length (List.seq 0 (n - 2)) = (n - 2)%coq_nat by apply: length_seq.
have Hseq : List.seq 0 (n - 2)
          = List.seq 0 (length (List.seq 0 (n - 2))) by rewrite Hlenks.
have Hclean0 : FpHessUpto p n 0 (reduceZ p M) by move=> a b Hb0; lia.
have Hshape := hess_outer_shape_r p Hp Hp2 n (List.seq 0 (n - 2)) 0
  (reduceZ p M) H Hseq (ks_cond n) HlenR Hclean0 Hred.
rewrite Hlenks in Hshape.
have HlenH : length H = n
  by rewrite (hess_outer_length p n (List.seq 0 (n-2)) (reduceZ p M) H Hred).
case: (le_lt_dec n i) => [Hin|Hin].
- rewrite /getH.
  have Hov : nth i H [] = [] by apply: List.nth_overflow; rewrite HlenH; lia.
  rewrite Hov nth_Z_nil. by apply: Z.mod_0_l.
- apply: (proj1 (Z_to_Fp_eq0 p Hp (getH H i j))).
  apply: Hshape; lia.
Qed.

(* ================================================================== *)
(* Section 5g: list-Z normalization + char_poly_int transport          *)
(*                                                                     *)
(* The returned H need not be well-formed (its rows may be ragged), so *)
(* cp_MXFp_coef cannot be applied to it directly.  We normalize H to   *)
(* nzmat (length H) H -- the well-formed matrix with the same getH on  *)
(* the index square [0,n) x [0,n) -- and show that char_poly_int and   *)
(* MXFp are insensitive to this normalization.  Since char_poly_int    *)
(* reads H only through dot products against well-formed (n x n)        *)
(* intermediate matrices, dot_int agreement on the first n entries     *)
(* propagates through the whole Faddeev-LeVerrier loop.                *)
(* ================================================================== *)

Local Lemma nth_map_seq {T} (g:nat->T) (d:T) (a c idx:nat) :
  (idx < c)%coq_nat ->
  List.nth idx (List.map g (List.seq a c)) d = g (a+idx)%coq_nat.
Proof.
elim: c a idx => [|c IH] a idx Hidx; first by lia.
case: idx Hidx => [|idx] Hidx /=.
- by rewrite Nat.add_0_r.
- rewrite IH; last lia. congr g. lia.
Qed.

Local Definition nzrow (n:nat) (r:list Z) : list Z :=
  List.map (fun j => nth_Z r j) (List.seq 0 n).
Local Definition nzmat (n:nat) (Hm:mat) : mat := List.map (nzrow n) Hm.

Local Lemma length_nzrow n r : length (nzrow n r) = n.
Proof. by rewrite /nzrow length_map length_seq. Qed.

Local Lemma nth_Z_nzrow n r j : (j < n)%coq_nat -> nth_Z (nzrow n r) j = nth_Z r j.
Proof.
move=> Hj.
rewrite /nzrow /nth_Z (nth_map_seq (fun j0 => List.nth j0 r 0%Z) 0%Z 0 n j Hj).
by rewrite Nat.add_0_l.
Qed.

Local Lemma getH_nzmat n Hm i j :
  (i < length Hm)%coq_nat -> (j < n)%coq_nat -> getH (nzmat n Hm) i j = getH Hm i j.
Proof.
move=> Hi Hj.
rewrite /getH /nzmat.
rewrite (nth_indep _ [] (nzrow n [])); last by rewrite length_map.
rewrite List.map_nth nth_Z_nzrow //.
Qed.

Local Lemma length_nzmat n Hm : length (nzmat n Hm) = length Hm.
Proof. by rewrite /nzmat length_map. Qed.

Local Lemma square_nzmat n Hm : length Hm = n -> square_mat n (nzmat n Hm).
Proof.
move=> Hlen. split.
- by rewrite /mat_dim length_nzmat.
- move=> i Hi. rewrite /nzmat.
  rewrite (nth_indep _ [] (nzrow n [])); last by rewrite length_map Hlen.
  by rewrite List.map_nth length_nzrow.
Qed.

Local Lemma nth_Z_behead r j : nth_Z (behead r) j = nth_Z r (S j).
Proof. by case: r => [|x r'] /=; rewrite ?nth_Z_nil. Qed.

Local Lemma dot_int_nil r : dot_int r [] = 0%Z.
Proof. by case: r. Qed.

Local Lemma dot_int_cons r y col' :
  dot_int r (y :: col') = (nth_Z r 0 * y + dot_int (behead r) col')%Z.
Proof. by case: r => [|x r'] /=; rewrite /nth_Z /= ?Z.mul_0_l ?Z.add_0_l. Qed.

Local Lemma dot_int_congr r1 r2 col :
  (forall j, (j < length col)%coq_nat -> nth_Z r1 j = nth_Z r2 j) ->
  dot_int r1 col = dot_int r2 col.
Proof.
elim: col r1 r2 => [|y col' IH] r1 r2 Hagree.
- by rewrite !dot_int_nil.
- rewrite !dot_int_cons.
  rewrite (Hagree O ltac:(simpl; lia)).
  rewrite (IH (behead r1) (behead r2)); last first.
  + move=> j Hj. rewrite !nth_Z_behead. apply: Hagree. simpl; lia.
  + by [].
Qed.

Local Lemma length_mmul A B : length (mmul A B) = length A.
Proof. by rewrite /mmul length_map. Qed.

Local Lemma sq_to_arl n0 B : square_mat n0 B -> all_rows_len n0 B.
Proof. move=> [Hd Hr] i Hi. apply: Hr. rewrite /mat_dim in Hd. lia. Qed.

Local Lemma arl_to_sq n0 M : mat_dim M = n0 -> all_rows_len n0 M -> square_mat n0 M.
Proof. move=> Hd Hr; split=> // i Hi; apply: Hr; rewrite /mat_dim in Hd; lia. Qed.

Local Lemma meye_sq n0 : square_mat n0 (meye n0).
Proof. by apply: arl_to_sq; [exact: mat_dim_meye | exact: all_rows_len_meye]. Qed.

Local Lemma mmul_sq Hm B n0 :
  length Hm = n0 -> square_mat n0 B -> square_mat n0 (mmul Hm B).
Proof.
move=> Hd Hsq; split.
- by rewrite /mat_dim length_mmul.
- move=> i Hi.
  have HB : (i < length (mmul Hm B))%coq_nat by rewrite length_mmul Hd.
  exact (all_rows_len_mmul (proj1 Hsq) (sq_to_arl n0 B Hsq) HB).
Qed.

Local Lemma mtrans_col_length B n0 :
  length B = n0 -> all_rows_len n0 B ->
  forall col, In col (mtrans B) -> length col = n0.
Proof.
move=> Hlen Hwf col Hin.
have [idx [Hidx Hnth]] := List.In_nth (mtrans B) col [] Hin.
rewrite (length_mtrans_sq B n0 Hlen Hwf) in Hidx.
by rewrite -Hnth (nth_mtrans_length_sq B n0 idx Hlen Hwf ltac:(lia)) Hlen.
Qed.

Local Lemma mmul_nzmat n0 Hm B :
  length Hm = n0 -> length B = n0 -> all_rows_len n0 B ->
  mmul Hm B = mmul (nzmat n0 Hm) B.
Proof.
move=> HlenHm Hlen Hwf.
rewrite /mmul /nzmat List.map_map.
apply: List.map_ext_in => r Hr.
apply: List.map_ext_in => col Hcol.
apply: dot_int_congr => j Hj.
have Hcoln : length col = n0 by apply: (mtrans_col_length B n0 Hlen Hwf).
rewrite Hcoln in Hj.
by rewrite nth_Z_nzrow.
Qed.

Local Lemma fl_loop_nzmat n0 Hm :
  length Hm = n0 ->
  forall steps k Mp c acc,
    square_mat n0 Mp ->
    fl_loop steps k Hm (meye n0) Mp c acc
    = fl_loop steps k (nzmat n0 Hm) (meye n0) Mp c acc.
Proof.
move=> HlenHm.
elim => [|s IH] k Mp c acc Hsq //.
have HlenMp : length Mp = n0 := proj1 Hsq.
have E1 : mmul Hm Mp = mmul (nzmat n0 Hm) Mp
  by apply: mmul_nzmat => //; exact: sq_to_arl.
set Mk := madd (mmul (nzmat n0 Hm) Mp) (mscale c (meye n0)).
have HMksq : square_mat n0 Mk.
{ apply: square_mat_madd.
  - apply: (mmul_sq (nzmat n0 Hm) Mp n0); [by rewrite length_nzmat | exact Hsq].
  - apply: square_mat_mscale; exact: meye_sq. }
have HlenMk : length Mk = n0 := proj1 HMksq.
have E2 : mmul Hm Mk = mmul (nzmat n0 Hm) Mk
  by apply: mmul_nzmat => //; exact: sq_to_arl.
cbn [fl_loop].
rewrite E1 -/Mk E2.
exact: (IH (k+1)%Z Mk _ _ HMksq).
Qed.

Local Lemma char_poly_int_nzmat Hm :
  char_poly_int Hm = char_poly_int (nzmat (length Hm) Hm).
Proof.
rewrite /char_poly_int /mat_dim length_nzmat.
have Hmzsq : square_mat (length Hm) (mzero (length Hm))
  by apply: arl_to_sq; [exact: mat_dim_mzero | exact: all_rows_len_mzero].
by rewrite (fl_loop_nzmat (length Hm) Hm erefl (length Hm) 1%Z
              (mzero (length Hm)) 1%Z [] Hmzsq).
Qed.

Local Lemma cp_MXFp_coef_r (p:Z) (Hp:Znumtheory.prime p) (n:nat) (X:mat) (i:nat) :
  mat_dim X = n ->
  ((char_poly (MXFp p n X))`_i = Z_to_Fp p (nth i (char_poly_int X) 0%Z))%R.
Proof.
move=> Hdim.
have HlenX : length X = n by rewrite -Hdim.
have Hsq : square_mat n (nzmat n X) by apply: square_nzmat.
have Hwf : forall j, (j < length (nzmat n X))%coq_nat ->
             length (nth j (nzmat n X) []) = n.
{ move=> j Hj. apply: (proj2 Hsq). move: Hj. by rewrite length_nzmat HlenX. }
have HX : MXFp p n X = MXFp p n (nzmat n X).
{ apply/matrixP => a b; rewrite !mxE; congr (Z_to_Fp p _).
  have Ha : (nat_of_ord a < length X)%coq_nat
    by rewrite HlenX; apply/ltP; exact: ltn_ord.
  have Hb : (nat_of_ord b < n)%coq_nat by apply/ltP; exact: ltn_ord.
  by rewrite (getH_nzmat n X a b Ha Hb). }
rewrite HX (cp_MXFp_coef p Hp n (nzmat n X) i (proj1 Hsq) Hwf).
by rewrite (char_poly_int_nzmat X) -HlenX.
Qed.

(* ================================================================== *)
(* Section 5h: length and reduced-mod-p of the recurrence output       *)
(* ================================================================== *)

Local Lemma length_vaddZ_max p a b :
  length (vaddZ p a b) = Nat.max (length a) (length b).
Proof.
elim: a b => [|x a' IH] b.
- by rewrite /=.
- case: b => [|y b'].
  + by rewrite /=.
  + rewrite /= IH; lia.
Qed.

Local Lemma length_pmulXsub p a q :
  length (pmulXsub p a q) = (length q).+1.
Proof.
rewrite /pmulXsub length_vaddZ_max length_vscaleZ.
have -> : length (0%Z :: q) = (length q).+1 by [].
lia.
Qed.

Local Lemma hess_fold_len_bound p L b :
  (forall t, In t L -> (length t.2 <= b)%coq_nat) ->
  (length (snd (hess_fold p L)) <= b)%coq_nat.
Proof.
elim: L => [|[[h sub] pi] L' IH] Hb /=; first by lia.
rewrite length_vaddZ_max length_vscaleZ.
have Hpi : (length pi <= b)%coq_nat by apply: (Hb (h,sub,pi)); left.
have Hrest : (length (snd (hess_fold p L')) <= b)%coq_nat
  by apply: IH => t Ht; apply: Hb; right.
lia.
Qed.

Local Lemma hess_pk_len p H k ps :
  (0 < k)%coq_nat ->
  length (nth (k-1) ps []) = k ->
  (forall i, (i < k-1)%coq_nat -> (length (nth i ps []) <= k-1)%coq_nat) ->
  length (hess_pk p H k ps) = (k+1)%coq_nat.
Proof.
move=> Hk Hcol Hrest.
rewrite /hess_pk /psubZ length_vaddZ_max length_pnegZ length_pmulXsub Hcol.
have Hfold :
  (length (snd (hess_fold p (List.map
      (fun i => (getH H i (k-1)%coq_nat, getH H (i+1)%coq_nat i, nth i ps []))
      (List.seq 0 (k-1))))) <= k-1)%coq_nat.
{ apply: hess_fold_len_bound => t Ht.
  apply List.in_map_iff in Ht.
  have [i [Hfi Hin]] := Ht.
  apply List.in_seq in Hin.
  rewrite -Hfi /=. apply: Hrest. lia. }
move: Hfold; set F := length _ => Hfold; lia.
Qed.

Local Lemma hess_build_coef_len p H steps :
  forall b k, (k <= b)%coq_nat -> (k <= steps)%coq_nat ->
    length (nth k (hess_build p H steps [:: [:: (1 mod p)%Z]]) []) = (k+1)%coq_nat.
Proof.
elim => [|b IH] k Hkb Hks.
- have Hk0 : k = O by lia. subst k.
  rewrite (hess_build_prefix p H steps [:: [:: (1 mod p)%Z]] 0); last by (simpl; lia).
  by [].
- case: (Nat.eq_dec k b.+1) => [Hk | Hne]; last by (apply: IH; lia).
  subst k.
  rewrite (hess_build_nth_rec p H steps [:: [:: (1 mod p)%Z]] b.+1);
    [|lia|(simpl;lia)|(simpl;lia)].
  apply: hess_pk_len; first lia.
  + rewrite (IH (b.+1-1)%coq_nat ltac:(lia) ltac:(lia)). lia.
  + move=> i Hi. rewrite (IH i ltac:(lia) ltac:(lia)). lia.
Qed.

Local Lemma Forall_vscaleZ p c r :
  List.Forall (fun x => (x mod p = x)%Z) (vscaleZ p c r).
Proof.
apply List.Forall_forall => y Hy.
apply List.in_map_iff in Hy. have [x [Hx _]] := Hy.
by rewrite -Hx /mulmodZ Zmod_mod.
Qed.

Local Lemma Forall_pnegZ p r :
  List.Forall (fun x => (x mod p = x)%Z) (pnegZ p r).
Proof.
apply List.Forall_forall => y Hy.
apply List.in_map_iff in Hy. have [x [Hx _]] := Hy.
by rewrite -Hx /negmodZ Zmod_mod.
Qed.

Local Lemma Forall_vaddZ p a b :
  List.Forall (fun x => (x mod p = x)%Z) a ->
  List.Forall (fun x => (x mod p = x)%Z) b ->
  List.Forall (fun x => (x mod p = x)%Z) (vaddZ p a b).
Proof.
elim: a b => [|x a' IH] b Ha Hb.
- exact: Hb.
- case: b Hb => [|y b'] Hb.
  + exact: Ha.
  + simpl. constructor.
    * by rewrite /addmodZ Zmod_mod.
    * apply: IH; [exact: (List.Forall_inv_tail Ha) | exact: (List.Forall_inv_tail Hb)].
Qed.

Local Lemma Forall_pmulXsub p a q : (0<p)%Z ->
  List.Forall (fun x => (x mod p = x)%Z) q ->
  List.Forall (fun x => (x mod p = x)%Z) (pmulXsub p a q).
Proof.
move=> Hp Hq. rewrite /pmulXsub. apply: Forall_vaddZ.
- constructor; [by rewrite Z.mod_0_l; lia | exact Hq].
- exact: Forall_vscaleZ.
Qed.

Local Lemma Forall_psubZ p a b :
  List.Forall (fun x => (x mod p = x)%Z) a ->
  List.Forall (fun x => (x mod p = x)%Z) (psubZ p a b).
Proof.
move=> Ha. rewrite /psubZ. apply: Forall_vaddZ; [exact Ha | exact: Forall_pnegZ].
Qed.

Local Lemma Forall_hess_pk p H k ps : (0<p)%Z ->
  List.Forall (fun x => (x mod p = x)%Z) (nth (k-1) ps []) ->
  List.Forall (fun x => (x mod p = x)%Z) (hess_pk p H k ps).
Proof.
move=> Hp Hcol. rewrite /hess_pk. apply: Forall_psubZ.
apply: Forall_pmulXsub => //.
Qed.

Local Lemma redZ_of_Forall p l : (0<p)%Z ->
  List.Forall (fun x => (x mod p = x)%Z) l ->
  forall i, ((List.nth i l 0%Z) mod p = List.nth i l 0%Z)%Z.
Proof.
move=> Hp HF i.
case: (Nat.lt_ge_cases i (length l)) => [Hi|Hi].
- exact: (proj1 (List.Forall_nth _ l) HF i 0%Z Hi).
- rewrite List.nth_overflow; last lia. by apply: Z.mod_0_l; lia.
Qed.

Local Lemma hess_build_Forall p H steps : (0<p)%Z ->
  forall k, (k <= steps)%coq_nat ->
    List.Forall (fun x => (x mod p = x)%Z)
      (nth k (hess_build p H steps [:: [:: (1 mod p)%Z]]) []).
Proof.
move=> Hp. elim => [|k IH] Hks.
- rewrite (hess_build_prefix p H steps [:: [:: (1 mod p)%Z]] 0); last by (simpl; lia).
  constructor; [by rewrite Zmod_mod | by []].
- rewrite (hess_build_nth_rec p H steps [:: [:: (1 mod p)%Z]] k.+1);
    [|lia|(simpl;lia)|(simpl;lia)].
  apply: (Forall_hess_pk _ _ _ _ Hp).
  rewrite subSS subn0. apply: IH; lia.
Qed.

Local Lemma hess_charpoly_redmod p H n :
  (0 < p)%Z -> (n <= mat_dim H)%coq_nat ->
  forall i, ((List.nth i (hess_charpoly p H n) 0%Z) mod p
             = List.nth i (hess_charpoly p H n) 0%Z)%Z.
Proof.
move=> Hp Hn i.
rewrite /hess_charpoly.
apply: redZ_of_Forall => //.
apply: hess_build_Forall => //.
Qed.

(* ================================================================== *)
(* Section 6: the two linear-algebra bridges                          *)
(* ================================================================== *)

(* hess_recurrence_sound: the Hessenberg recurrence computes the
   characteristic polynomial mod p of the reduced matrix H.  PROVED
   (axiom-free), without any squareness hypothesis on M.

   (a) [recurrence = determinant]  Section 5e (RB_core) maps H into the
       polynomial ring {poly 'F_p} entrywise via getH / MXFp (so NO
       well-formedness is needed) and shows the embedded recurrence
       hess_charpoly p H N.+1 equals char_poly (MXFp p N.+1 H), by
       inducting on the leading-principal index and matching hess_pk /
       hess_fold to the abstract Hessenberg recurrence Dlead_rec
       term-for-term (RB_term), closing with Dlead_full.

   (b) [Hessenberg shape, ragged-tolerant]  Section 5f
       (hess_reduce_shape_r) establishes that H is upper-Hessenberg mod p
       using only `length A = n` (the elimination only ever touches
       columns b <> k+1, where the column op is a no-op), so square_mat M
       is NOT required.

   (c) [integer bridge]  Section 5g normalizes the (possibly ragged) H to
       the well-formed nzmat (length H) H -- same getH on [0,n) x [0,n) --
       and transports char_poly_int across this normalization
       (char_poly_int reads H only through dot products against
       well-formed n x n matrices), giving a wf-free cp_MXFp_coef_r.
       Section 5h supplies the length (n+1) and reduced-mod-p facts of the
       recurrence output, and the coefficientwise comparison is closed
       through Z_to_Fp_eqmod, exactly as in ModularFL.char_poly_modZ_sound. *)
Lemma hess_recurrence_sound (p : Z) (M H : mat) :
  Znumtheory.prime p ->
  (Z.of_nat (length M) + 1 < p)%Z ->
  hess_reduce p M = Some H ->
  hess_charpoly p H (mat_dim M) = map (fun c => c mod p) (char_poly_int H).
Proof.
move=> Hp Hbound Hred.
have Hp0 : (0 < p)%Z by destruct Hp; lia.
have Hmod0 : (0 mod p = 0)%Z by apply: Z.mod_0_l; lia.
have Hout : hess_outer p (reduceZ p M) (mat_dim M) (List.seq 0 (mat_dim M - 2))
            = Some H by move: Hred; rewrite /hess_reduce.
have HlenH : length H = length M.
{ rewrite (hess_outer_length p (mat_dim M) (List.seq 0 (mat_dim M - 2))
            (reduceZ p M) H Hout).
  by rewrite /reduceZ length_map. }
have HdimH : mat_dim H = mat_dim M by rewrite /mat_dim HlenH.
case: (Nat.eq_dec (length M) 0) => [Hlen0 | Hlen0].
- have Hdm0 : mat_dim M = 0%N by rewrite /mat_dim Hlen0.
  have HdmH0 : mat_dim H = 0%N by rewrite HdimH Hdm0.
  rewrite Hdm0 /hess_charpoly /char_poly_int /= HdmH0 /=.
  by [].
- have Hp2 : (2 < p)%Z.
  { have H1 : (1 <= Z.of_nat (length M))%Z
      by (apply: (proj1 (Nat2Z.inj_le 1 (length M))); lia).
    lia. }
  have [N HN] : exists N, mat_dim M = N.+1.
  { exists ((mat_dim M).-1). rewrite /mat_dim.
    case E: (length M) => [|m]; [lia | by []]. }
  have HdimH' : mat_dim H = N.+1 by rewrite HdimH HN.
  have Hshape : forall i j : nat, (j.+1 < i)%N -> Z_to_Fp p (getH H i j) = 0%R.
  { move=> i j Hji. apply/(Z_to_Fp_eq0 p Hp).
    exact: (hess_reduce_shape_r p Hp Hp2 M H Hred i j Hji). }
  have Hcoef : forall i, Z_to_Fp p (List.nth i (hess_charpoly p H N.+1) 0%Z)
                       = Z_to_Fp p (List.nth i (char_poly_int H) 0%Z).
  { move=> i.
    have <- : (Lpoly p (hess_charpoly p H N.+1))`_i
              = Z_to_Fp p (List.nth i (hess_charpoly p H N.+1) 0%Z)
      by rewrite Lpoly_coef.
    rewrite (RB_core p Hp H N Hshape).
    by rewrite (cp_MXFp_coef_r p Hp N.+1 H i HdimH'). }
  rewrite HN.
  apply: (List.nth_ext _ _ 0%Z 0%Z).
  + rewrite length_map char_poly_int_length HdimH' /hess_charpoly.
    by rewrite (hess_build_coef_len p H N.+1 N.+1 N.+1 (le_n _) (le_n _)).
  + move=> i Hi.
    rewrite (nth_map_eq (fun c => c mod p) (char_poly_int H) 0%Z i Hmod0).
    rewrite -(hess_charpoly_redmod p H N.+1 Hp0 ltac:(rewrite HdimH'; lia) i).
    apply: (Z_to_Fp_eqmod p Hp). exact: (Hcoef i).
Qed.

(* hess_reduce_similar: the Hessenberg reduction preserves the
   characteristic polynomial mod p.  PROVED (axiom-free), via the
   infrastructure of Section 5b.

   Proof (MathComp).  Over the field 'F_p, each hess_elim_step is the
   conjugation (1 - m *: delta_{i,k1}) *m A *m (1 + m *: delta_{i,k1})
   of the matrix mapped into 'F_p (MXFp_elim_step); the two elementary
   factors multiply to 1%:M (ELER, since i <> k1), so char_poly_conj
   gives char_poly invariance per step (elim_step_charpoly).  Folding
   over hess_inner / hess_outer (hess_inner_ok / hess_outer_ok) and
   reduceZ (MXFp_reduceZ) yields char_poly(H) = char_poly(M) over 'F_p
   (hess_reduce_charpoly_Fp).  This is transported to the list-Z
   statement coefficientwise through the ring hom Z -> 'F_p
   (cp_MXFp_coef, built on map_char_poly and
   CharPoly.char_poly_int_correct) and Z_to_Fp injectivity mod p
   (Z_to_Fp_eqmod), exactly as in ModularFL.char_poly_modZ_sound. *)
Lemma hess_reduce_similar (p : Z) (M H : mat) :
  Znumtheory.prime p ->
  square_mat (length M) M ->
  (Z.of_nat (length M) + 1 < p)%Z ->
  hess_reduce p M = Some H ->
  map (fun c => c mod p) (char_poly_int H) = map (fun c => c mod p) (char_poly_int M).
Proof.
move=> Hp Hsq Hbound Hred.
have Hmod0 : (0 mod p = 0)%Z by apply Z.mod_0_l; destruct Hp; lia.
have [HgH HcF] := hess_reduce_charpoly_Fp p Hp M H Hsq Hred.
set n := length M in HgH HcF *.
case: HgH => HlenH HrowH.
case: Hsq => HdimM HwfM.
have HdimH : mat_dim H = n by rewrite /mat_dim HlenH.
have HwfH : forall j, (j < length H)%coq_nat -> length (nth j H []) = n
  by rewrite HlenH => j Hj; apply HrowH.
have Hlen : length (char_poly_int H) = length (char_poly_int M)
  by rewrite !char_poly_int_length HdimH HdimM.
apply: (List.nth_ext _ _ 0%Z 0%Z).
- by rewrite !length_map Hlen.
- move=> i Hi; rewrite length_map in Hi.
  rewrite (nth_map_eq (fun c => c mod p) (char_poly_int H) 0%Z i Hmod0).
  rewrite (nth_map_eq (fun c => c mod p) (char_poly_int M) 0%Z i Hmod0).
  apply: (Z_to_Fp_eqmod p Hp).
  rewrite -(cp_MXFp_coef p Hp n H i HdimH HwfH).
  rewrite -(cp_MXFp_coef p Hp n M i HdimM HwfM).
  by rewrite HcF.
Qed.

(* ================================================================== *)
(* Section 7: main theorem                                             *)
(* ================================================================== *)

Theorem char_poly_hess_sound (p : Z) (M : mat) :
  Znumtheory.prime p ->
  square_mat (length M) M ->
  (Z.of_nat (length M) + 1 < p)%Z ->
  fl_all_divisible (length M) 1 M (meye (length M)) (mzero (length M)) 1 ->
  char_poly_hess p M = map (fun c => c mod p) (char_poly_int M).
Proof.
  intros Hp Hsq Hb Hfl.
  unfold char_poly_hess.
  destruct (hess_reduce p M) as [H|] eqn:Hred.
  - (* Hessenberg path: recurrence soundness then similarity. *)
    transitivity (map (fun c => c mod p) (char_poly_int H)).
    + apply (hess_recurrence_sound p M H); assumption.
    + apply (hess_reduce_similar p M H); assumption.
  - (* Bad-pivot fallback: the proven FL pass. *)
    apply char_poly_modZ_sound; assumption.
Qed.

Print Assumptions char_poly_hess_sound.
