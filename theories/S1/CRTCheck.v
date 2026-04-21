(* ============================================================== *)
(*  CRTCheck.v                                                      *)
(*                                                                  *)
(*  Machine-verify ALL 42 steps of the Maynard PRS chain using      *)
(*  CRT (Chinese Remainder Theorem) over Uint63 primes.             *)
(*                                                                  *)
(*  Strategy: reduce every polynomial coefficient modulo each of    *)
(*  several primes p < 2^31, then check the PRS identity            *)
(*    lc(B)^d * A = Q * B + beta * C                                *)
(*  in Uint63 arithmetic modulo p.  Since each residue < 2^31,      *)
(*  products fit in 2^62 < 2^63, so Uint63.mul does not overflow.   *)
(*                                                                  *)
(*  If the identity holds mod enough primes whose product exceeds   *)
(*  twice the max coefficient magnitude, the identity holds over Z  *)
(*  by CRT.                                                         *)
(* ============================================================== *)

From Stdlib Require Import Uint63 ZArith List Bool Lia Znumtheory.
From Bignums Require Import BigZ.
Import ListNotations.
From PrimeGapS1 Require Import IntPoly WitnessChain.

(* ============================================================== *)
(*  Section 1: BigZ -> Uint63 modular reduction                     *)
(* ============================================================== *)

(* Reduce a BigZ integer modulo a Uint63 prime, returning a Uint63.
   Works by: BigZ.modulo (fast, stays in bignum land) then convert
   the small result to int via BigZ.to_Z + of_Z. *)
Definition bigZ_to_mod (p : int) (x : BigZ.t_) : int :=
  let p_bigZ := BigZ.of_Z (Uint63.to_Z p) in
  Uint63.of_Z (BigZ.to_Z (BigZ.modulo x p_bigZ)).

(* Reduce a list of BigZ coefficients modulo p. *)
Definition reduce_poly (p : int) (cs : list BigZ.t_) : list int :=
  List.map (bigZ_to_mod p) cs.

(* ============================================================== *)
(*  Section 2: Modular polynomial arithmetic over Uint63            *)
(*                                                                  *)
(*  All operations take a prime p and work modulo p.                *)
(*  Convention: polynomials are list int, low-to-high, coefficients *)
(*  in [0, p).  The empty list is zero.                             *)
(* ============================================================== *)

Definition addmod (p a b : int) : int := (a + b) mod p.
Definition mulmod (p a b : int) : int := (a * b) mod p.
Definition submod (p a b : int) : int := ((a + p) - b) mod p.

(* Modular polynomial addition *)
Fixpoint mpadd (p : int) (a b : list int) : list int :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: xs, y :: ys => addmod p x y :: mpadd p xs ys
  end.

(* Modular polynomial scaling by a scalar *)
Definition mpscale (p : int) (c : int) (poly : list int) : list int :=
  List.map (mulmod p c) poly.

(* Modular polynomial multiplication (convolution) *)
Fixpoint mpmul (p : int) (a b : list int) : list int :=
  match a with
  | [] => []
  | x :: xs => mpadd p (mpscale p x b) (0%uint63 :: mpmul p xs b)
  end.

(* Strip trailing zeros from a modular polynomial *)
Fixpoint mpdrop_zeros (l : list int) : list int :=
  match l with
  | [] => []
  | x :: xs =>
      let rest := mpdrop_zeros xs in
      if Uint63.eqb x 0%uint63 then rest else x :: xs
  end.

Definition mpnorm (p : list int) : list int :=
  List.rev (mpdrop_zeros (List.rev p)).

(* Leading coefficient of a modular polynomial *)
Fixpoint mplead_aux (poly : list int) (acc : int) : int :=
  match poly with
  | [] => acc
  | x :: xs =>
      if Uint63.eqb x 0%uint63 then mplead_aux xs acc
      else mplead_aux xs x
  end.

Definition mplead (poly : list int) : int := mplead_aux poly 0%uint63.

(* Length after normalization *)
Definition mpsize (poly : list int) : nat := List.length (mpnorm poly).

(* Modular exponentiation: compute base^exp mod p *)
Fixpoint powmod (p base : int) (exp : nat) : int :=
  match exp with
  | O => 1%uint63 mod p
  | S n => mulmod p base (powmod p base n)
  end.

(* Polynomial equality check modulo p:
   Two polynomials are equal mod p iff their normalized forms match. *)
Fixpoint mp_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Uint63.eqb x y && mp_eqb xs ys
  | _, _ => false
  end.

(* ============================================================== *)
(*  Section 3: Single PRS step checker modulo one prime             *)
(*                                                                  *)
(*  check_prs_step_mod p A B Q beta C:                              *)
(*    Checks lc(B)^d * A == Q*B + beta*C  (mod p)                  *)
(*    where d = deg(A) - deg(B) + 1 = psize(A) - psize(B) + 1      *)
(*    (Knuth pseudo-division convention, matching WitnessChain).    *)
(* ============================================================== *)

Definition check_prs_step_mod (p : int)
    (A B Q : list int) (beta : int) (C : list int) : bool :=
  let lc_B := mplead B in
  let d := S (Nat.sub (mpsize A) (mpsize B)) in
  let lc_pow := powmod p lc_B d in
  let lhs := mpscale p lc_pow A in
  let rhs := mpadd p (mpmul p Q B) (mpscale p beta C) in
  mp_eqb (mpnorm lhs) (mpnorm rhs).

(* ============================================================== *)
(*  Section 4: Check one PRS step against ALL primes                *)
(* ============================================================== *)

(* For one step, reduce all polynomials mod p, then check. *)
Definition check_step_one_prime (p : int)
    (A_bigZ B_bigZ Q_bigZ : list BigZ.t_) (beta_bigZ : BigZ.t_)
    (C_bigZ : list BigZ.t_) : bool :=
  let A := reduce_poly p A_bigZ in
  let B := reduce_poly p B_bigZ in
  let Q := reduce_poly p Q_bigZ in
  let beta := bigZ_to_mod p beta_bigZ in
  let C := reduce_poly p C_bigZ in
  check_prs_step_mod p A B Q beta C.

Definition check_step_all_primes (primes : list int)
    (A_bigZ B_bigZ Q_bigZ : list BigZ.t_) (beta_bigZ : BigZ.t_)
    (C_bigZ : list BigZ.t_) : bool :=
  List.forallb (fun p =>
    check_step_one_prime p A_bigZ B_bigZ Q_bigZ beta_bigZ C_bigZ
  ) primes.

(* ============================================================== *)
(*  Section 5: Iterate over all 42 PRS steps                        *)
(*                                                                  *)
(*  The chain has 43 entries (chain_0 .. chain_42).                 *)
(*  There are 41 quotients (prs_quot_1 .. prs_quot_41) and          *)
(*  41 betas (sturm_betas_bigZ).                                    *)
(*  Step i (1-indexed): lc(chain_i)^d * chain_{i-1}                 *)
(*                      = Q_i * chain_i + beta_i * chain_{i+1}      *)
(* ============================================================== *)

Fixpoint check_all_steps_mod (primes : list int)
    (chain : list (list BigZ.t_))
    (quotients : list (list BigZ.t_))
    (betas : list BigZ.t_) : bool :=
  match chain, quotients, betas with
  | A :: ((B :: rest_chain) as BC), Q :: rest_Q, beta :: rest_B =>
      let C := match rest_chain with c :: _ => c | [] => [] end in
      check_step_all_primes primes A B Q beta C
      && check_all_steps_mod primes BC rest_Q rest_B
  | _, _, _ => true
  end.

(* ============================================================== *)
(*  Section 6: Prime list and primality verification                *)
(*                                                                  *)
(*  We use primes just above 2^30 = 1073741824.  With primes this  *)
(*  size, residues fit in 31 bits, products in 62 bits < 63 bits.   *)
(*                                                                  *)
(*  10 primes give ~300-bit CRT coverage — a strong probabilistic   *)
(*  check but not a full CRT proof.  Full coverage of the 293 kbit  *)
(*  max coefficient requires ~9776 primes; this would take ~6 hours *)
(*  under vm_compute due to BigZ.modulo cost on 100 kbit chain      *)
(*  entries.  Scaling options for future work: rebuild Rocq with     *)
(*  native_compute, or precompute modular reductions externally and  *)
(*  ship as Uint63 arrays (verified in Rocq by re-checking the      *)
(*  reduction identity).                                            *)
(*                                                                  *)
(*  TRUST: the primality of these 10 values is verified IN Rocq by  *)
(*  Uint63 trial division below — no external script needed.        *)
(* ============================================================== *)

Definition crt_primes : list int :=
  [ 1073741827%uint63
  ; 1073741831%uint63
  ; 1073741833%uint63
  ; 1073741839%uint63
  ; 1073741843%uint63
  ; 1073741857%uint63
  ; 1073741891%uint63
  ; 1073741909%uint63
  ; 1073741939%uint63
  ; 1073741953%uint63
  ].

(* --- Primality verification via Uint63 trial division ----------- *)

(* Trial division: check that n has no factor in [2, k]. *)
Fixpoint no_factor_upto (n k : int) (fuel : nat) : bool :=
  match fuel with
  | O => true  (* ran out of fuel — vacuously true *)
  | S f =>
    if Uint63.ltb k 2 then true  (* checked all candidates *)
    else if Uint63.eqb (Uint63.mod n k) 0 then false  (* k divides n *)
    else no_factor_upto n (Uint63.sub k 1) f
  end.

(* Primality test: n > 1 and no factor in [2, floor(sqrt(n))].
   46340 > sqrt(2^31 - 1) ≈ 46340.95, so this covers all primes < 2^31. *)
Definition is_prime_uint63 (n : int) : bool :=
  Uint63.ltb 1 n && no_factor_upto n 46340 46340%nat.

(* Machine-verified: every entry in crt_primes is prime. *)
Lemma crt_primes_all_prime :
  List.forallb is_prime_uint63 crt_primes = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  Section 7: The main check and its verification                  *)
(* ============================================================== *)

Definition check_full_prs_chain_mod : bool :=
  check_all_steps_mod crt_primes
    sturm_chain_bigZ prs_quotients_bigZ sturm_betas_bigZ.

(* THE BIG LEMMA: the full chain is verified modulo our primes. *)
Lemma full_prs_chain_verified :
  check_full_prs_chain_mod = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  Section 8: CRT correctness (mathematical justification)         *)
(*                                                                  *)
(*  If a polynomial identity f(X) = 0 holds modulo k primes         *)
(*  p_1, ..., p_k, and the absolute value of every coefficient of   *)
(*  f is less than (p_1 * ... * p_k) / 2, then f(X) = 0 over Z.   *)
(*                                                                  *)
(*  This is a standard consequence of the Chinese Remainder Theorem.*)
(*  Proof: each coefficient c satisfies c ≡ 0 (mod p_i) for all i,  *)
(*  so c ≡ 0 (mod p_1*...*p_k), and |c| < p_1*...*p_k/2 forces c=0.*)
(* ============================================================== *)

(* --- Convert BigZ polynomial data to IntPoly's list Z ---------- *)

Definition bigZ_to_Z_poly (p : list BigZ.t_) : pol :=
  List.map BigZ.to_Z p.

(* --- Maximum absolute coefficient of a list Z polynomial ------- *)

Definition max_abs_coeff (p : pol) : Z :=
  List.fold_left (fun acc c => Z.max acc (Z.abs c)) p 0%Z.

(* --- PRS identity residual for one step over Z ------------------ *)
(*  Given A, B, Q, beta, C, the residual polynomial is:             *)
(*    lc(B)^d * A - (Q * B + beta * C)                              *)
(*  where d = psize(A) - psize(B) + 1 (Knuth pseudo-division).     *)

Definition prs_residual_Z (A B Q : pol) (beta : Z) (C : pol) : pol :=
  let lc_B := plead B in
  let d := S (Nat.sub (psize A) (psize B)) in
  let lc_pow := Z.pow lc_B (Z.of_nat d) in
  psub (pscale lc_pow A) (padd (pmul Q B) (pscale beta C)).

(* --- Check that all PRS steps yield zero residual over Z -------- *)

Fixpoint all_prs_residuals_zero (chain : list pol)
    (quotients : list pol) (betas : list Z) : Prop :=
  match chain, quotients, betas with
  | A :: ((B :: rest_chain) as BC), Q :: rest_Q, beta :: rest_B =>
      let C := match rest_chain with c :: _ => c | [] => [] end in
      pnorm (prs_residual_Z A B Q beta C) = []
      /\ all_prs_residuals_zero BC rest_Q rest_B
  | _, _, _ => True
  end.

(* --- Product of CRT primes as a Z value ------------------------- *)

Definition crt_primes_Z : list Z :=
  List.map Uint63.to_Z crt_primes.

Definition crt_product : Z :=
  List.fold_left Z.mul crt_primes_Z 1%Z.

(* --- Concrete product bound ------------------------------------- *)
(*  The product of our 10 primes (each ~2^30) exceeds 2^299.        *)
(*  This is the threshold: if every coefficient of the residual     *)
(*  has absolute value < crt_product / 2, then the residual is 0.   *)

Definition primes_product_bound : Prop :=
  (crt_product > 2 ^ 299)%Z.

(* Machine-verify the product bound. *)
Lemma primes_product_bound_verified : primes_product_bound.
Proof. vm_compute. reflexivity. Qed.

(* --- Max coefficient bound assumption --------------------------- *)
(*  For CRT to apply, we need: for every PRS step, the max absolute *)
(*  coefficient of the residual polynomial (over Z) is less than    *)
(*  crt_product / 2.  This is an external assumption that depends   *)
(*  on the actual coefficient sizes in the Maynard chain.           *)

Fixpoint max_coeff_below_half_product
    (chain : list pol) (quotients : list pol) (betas : list Z) : Prop :=
  match chain, quotients, betas with
  | A :: ((B :: rest_chain) as BC), Q :: rest_Q, beta :: rest_B =>
      let C := match rest_chain with c :: _ => c | [] => [] end in
      (2 * max_abs_coeff (prs_residual_Z A B Q beta C) < crt_product)%Z
      /\ max_coeff_below_half_product BC rest_Q rest_B
  | _, _, _ => True
  end.

(* ============================================================== *)
(*  Section 9: CRT helper lemmas                                    *)
(* ============================================================== *)

Open Scope Z_scope.

(* --- Arithmetic helpers ---------------------------------------- *)

(* A multiple of P that is smaller than P/2 in absolute value
   must be zero. *)
Lemma small_multiple_zero : forall c P : Z,
  (P | c)%Z -> (0 < P)%Z -> (2 * Z.abs c < P)%Z -> c = 0%Z.
Proof.
  intros c P [k Hk] HP Hlt. subst c.
  rewrite Z.abs_mul in Hlt.
  assert (Z.abs k = 0)%Z by nia. lia.
Qed.

(* If a | n and b | n and gcd(a,b) = 1, then a*b | n. *)
Lemma coprime_div_mul : forall a b n : Z,
  (a | n)%Z -> (b | n)%Z -> rel_prime a b -> (a * b | n)%Z.
Proof.
  intros a b n [j Hj] Hb Hrel. subst n.
  assert (Hbj : (b | j)%Z).
  { apply Gauss with (b := a).
    rewrite Z.mul_comm. exact Hb.
    exact (rel_prime_sym _ _ Hrel). }
  destruct Hbj as [m Hm]. subst j.
  exists m. ring.
Qed.

(* --- Polynomial helpers ---------------------------------------- *)

(* If every element of a list is 0, drop_leading_zeros returns []. *)
Lemma drop_leading_zeros_all_zero : forall l : list Z,
  (forall c, In c l -> c = 0%Z) -> drop_leading_zeros l = [].
Proof.
  induction l; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)). simpl.
  apply IHl. intros c Hc. apply H. right. exact Hc.
Qed.

(* If every coefficient of a polynomial is 0, its normal form is []. *)
Lemma all_zero_pnorm_nil : forall p : pol,
  (forall c, In c p -> c = 0%Z) -> pnorm p = [].
Proof.
  intros p H. unfold pnorm.
  rewrite drop_leading_zeros_all_zero.
  - reflexivity.
  - intros c Hc. apply H. apply in_rev. exact Hc.
Qed.

(* --- max_abs_coeff properties ---------------------------------- *)

(* The fold computing max_abs_coeff is monotone in the accumulator. *)
Lemma fold_left_Zmax_abs_mono : forall (l : list Z) (a1 a2 : Z),
  (a1 <= a2)%Z ->
  (fold_left (fun a c => Z.max a (Z.abs c)) l a1 <=
   fold_left (fun a c => Z.max a (Z.abs c)) l a2)%Z.
Proof.
  induction l; intros a1 a2 Hle; simpl.
  - exact Hle.
  - apply IHl. lia.
Qed.

Lemma fold_left_Zmax_abs_ge : forall (l : list Z) (acc : Z),
  (acc <= fold_left (fun a c => Z.max a (Z.abs c)) l acc)%Z.
Proof.
  induction l; intros acc; simpl.
  - lia.
  - apply Z.le_trans with (Z.max acc (Z.abs a)).
    + lia.
    + apply IHl.
Qed.

(* max_abs_coeff bounds the absolute value of every element. *)
Lemma max_abs_coeff_bound : forall (p : pol) (c : Z),
  In c p -> (Z.abs c <= max_abs_coeff p)%Z.
Proof.
  unfold max_abs_coeff. induction p as [|a p IHp]; intros c Hc.
  - destruct Hc.
  - simpl. destruct Hc as [-> | Hc].
    + apply Z.le_trans with (Z.max 0 (Z.abs c)).
      * lia.
      * apply fold_left_Zmax_abs_ge.
    + apply Z.le_trans with
        (fold_left (fun acc c0 => Z.max acc (Z.abs c0)) p 0%Z).
      * apply IHp. exact Hc.
      * apply fold_left_Zmax_abs_mono. lia.
Qed.

(* --- CRT product helpers --------------------------------------- *)

(* fold_left Z.mul can be factored: fold(l, a) = a * fold(l, 1). *)
Lemma fold_left_mul_assoc : forall (l : list Z) (a : Z),
  fold_left Z.mul l a = (a * fold_left Z.mul l 1)%Z.
Proof.
  induction l as [|x l IHl]; intros a.
  - simpl. lia.
  - change (fold_left Z.mul (x :: l) a) with (fold_left Z.mul l (Z.mul a x)).
    change (fold_left Z.mul (x :: l) 1%Z) with (fold_left Z.mul l (Z.mul 1 x)).
    rewrite IHl. rewrite (IHl (Z.mul 1 x)). nia.
Qed.

(* A prime p cannot divide a different prime q. *)
Lemma prime_not_divide_other_prime : forall p q : Z,
  prime p -> prime q -> p <> q -> ~ (p | q)%Z.
Proof.
  intros p q Hp Hq Hneq Hdiv.
  assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
  assert (Hq1 : (1 < q)%Z) by (destruct Hq; lia).
  destruct Hdiv as [k Hk].
  assert (Hk_pos : (0 < k)%Z) by nia.
  assert (Hlt : (p < q)%Z \/ p = q) by nia.
  destruct Hlt as [Hlt | Hlt]; [| lia].
  assert (Hrange : (1 <= p < q)%Z) by lia.
  destruct Hq as [_ Hq2]. specialize (Hq2 _ Hrange).
  destruct Hq2 as [_ _ Hgcd].
  assert (Hdivpq : (p | q)%Z) by (exists k; lia).
  assert (Hdivpp : (p | p)%Z) by (exists 1%Z; lia).
  specialize (Hgcd _ Hdivpp Hdivpq).
  destruct Hgcd as [m Hm].
  assert (m = 0 \/ m >= 1 \/ m <= -1)%Z by lia.
  destruct H as [H|[H|H]]; nia.
Qed.

(* A prime p that does not appear in a list of primes qs cannot
   divide the product of qs. *)
Lemma prime_not_divide_prime_product : forall (p : Z) (qs : list Z),
  prime p ->
  (forall q, In q qs -> prime q) ->
  ~ In p qs ->
  ~ (p | fold_left Z.mul qs 1)%Z.
Proof.
  induction qs as [|q qs IHqs]; intros Hp Hprimes Hnotin Hdiv.
  - simpl in Hdiv. destruct Hdiv as [k Hk].
    assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
    assert (k = 0 \/ k >= 1 \/ k <= -1)%Z by lia.
    destruct H as [H|[H|H]]; nia.
  - simpl in Hdiv. rewrite fold_left_mul_assoc in Hdiv.
    assert (Hpq : p <> q) by (intro; subst; apply Hnotin; left; reflexivity).
    assert (Hprime_q : prime q) by (apply Hprimes; left; reflexivity).
    apply prime_mult in Hdiv; [| exact Hp].
    destruct Hdiv as [Hdiv | Hdiv].
    + replace (match q with 0 => 0 | Z.pos y' => Z.pos y'
               | Z.neg y' => Z.neg y' end) with q in Hdiv
        by (destruct q; reflexivity).
      exact (prime_not_divide_other_prime p q Hp Hprime_q Hpq Hdiv).
    + apply IHqs; auto.
      * intros r Hr. apply Hprimes. right. exact Hr.
      * intro. apply Hnotin. right. exact H.
Qed.

(* If all primes in a NoDup list divide c, then their product divides c. *)
Lemma all_primes_divide_product : forall (ps : list Z) (c : Z),
  NoDup ps ->
  (forall p, In p ps -> prime p) ->
  (forall p, In p ps -> (p | c)%Z) ->
  (fold_left Z.mul ps 1 | c)%Z.
Proof.
  induction ps as [|p ps IHps]; intros c Hnd Hprimes Hdivs.
  - simpl. exists c. lia.
  - simpl. rewrite fold_left_mul_assoc.
    replace (match p with 0 => 0 | Z.pos y' => Z.pos y'
             | Z.neg y' => Z.neg y' end) with p
      by (destruct p; reflexivity).
    apply coprime_div_mul.
    + apply Hdivs. left. reflexivity.
    + apply IHps.
      * inversion Hnd; assumption.
      * intros q Hq. apply Hprimes. right. exact Hq.
      * intros q Hq. apply Hdivs. right. exact Hq.
    + apply prime_rel_prime.
      * apply Hprimes. left. reflexivity.
      * apply prime_not_divide_prime_product.
        -- apply Hprimes. left. reflexivity.
        -- intros q Hq. apply Hprimes. right. exact Hq.
        -- inversion Hnd; assumption.
Qed.

(* crt_product is positive (follows from primes_product_bound). *)
Lemma crt_product_pos : (0 < crt_product)%Z.
Proof.
  assert (H := primes_product_bound_verified).
  unfold primes_product_bound in H. lia.
Qed.
