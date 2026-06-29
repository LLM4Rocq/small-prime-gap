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
(* Section 6: the two linear-algebra bridges                          *)
(* ================================================================== *)

(* TODO-BRIDGE.

   hess_recurrence_sound: the Hessenberg recurrence computes the
   characteristic polynomial mod p of the reduced matrix H.

   Proof strategy (MathComp).  Let H be the matrix returned by
   hess_reduce; it is square (length M x length M) and upper-Hessenberg
   (H[i][j] reduced mod p, and H[i][j] = 0 for i > j+1, established from
   the structure of hess_outer/hess_inner).  Two steps:

   (a) [recurrence = determinant over a field]  Map H into 'F_p and show
       hess_charpoly p H n, embedded into 'F_p coefficientwise, equals
       the coefficient list of char_poly (H : 'M['F_p]_n) = det(xI - H).
       For an upper-Hessenberg matrix the last ROW has nonzeros only in
       the last two columns, so `expand_det_row` along the last row gives
       det H_k = H[k-1][k-1] det H_{k-1}
                 + H[k-1][k-2] * (-1)^... * det(minor),
       and the minor's block structure yields the product-of-subdiagonals
       factor.  Induct on the leading principal size; this matches the
       recurrence implemented by hess_fold / hess_pk.

   (b) [mod-p commutation + integer bridge]  As in
       ModularFL.char_poly_modZ_sound, the list-Z recurrence mirrors the
       'F_p computation under the ring hom Z -> 'F_p (each op is addmodZ
       / mulmodZ / negmodZ); combine with `map_char_poly` (char_poly
       commutes with ring morphisms) and CharPoly.char_poly_int_correct
       to get hess_charpoly p H n = map (.mod p) (char_poly_int H).

   Equivalent shortcut for (b): prove the bare identity
   `hess_charpoly p H (mat_dim M) = char_poly_modZ p H` (recurrence = FL
   on the SAME Hessenberg matrix) and then rewrite by
   char_poly_modZ_sound applied to H (H is square via a structural
   shape lemma, FL-divisible via FLDiv.fl_all_divisible_from_L2, and
   inside the bound since length H = length M). *)
Lemma hess_recurrence_sound (p : Z) (M H : mat) :
  Znumtheory.prime p ->
  (Z.of_nat (length M) + 1 < p)%Z ->
  hess_reduce p M = Some H ->
  hess_charpoly p H (mat_dim M) = map (fun c => c mod p) (char_poly_int H).
Proof.
  (* TODO-BRIDGE: Hessenberg recurrence = char_poly mod p (Laplace
     expansion along the last row of an upper-Hessenberg matrix). *)
Admitted.

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
