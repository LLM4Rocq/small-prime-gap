From Stdlib Require Import ZArith List.
From mathcomp Require Import all_boot all_algebra.
From PrimeGapS1 Require Import MaynardFactQ MaynardBasis.

(**md*************************************************************************)
(** # MaynardSpec — Maynard's closed-form specification of M1, M2

Transcribes the Python helpers `Poly_at_k`, `Cff_rat`, `enumerate_bounds`,
`const_gram`, `prime_gram` from flint_probe.py (Maynard 2013 §7-8,
arXiv:1311.4600).  The analytic closed forms for the Dirichlet-type
integrals are taken as rational *definitions* here; the analytic
identification is not proved in this project.

Two parallel representations are provided:

- a `rat`-valued specification `M1_spec_ij, M2_spec_ij` that matches the
  textbook formulas verbatim, and

- an integer (Z, Z) num/den pair `m1_num_den, m2_num_den` that is used by
  `MaynardVerify.v` to cross-multiply with the shipped integer matrices —
  purely in Z, so vm_compute does not hit `rat`'s canonical-form
  normalisation at scale.

The two representations are bridged by Qed lemmas `M{1,2}_spec_rat_eq` in
`MaynardSpecBridge.v` (no axioms, "Closed under the global context").
`MaynardVerify.v` consumes the (num, den) pair directly for the Z-level
cross-multiplication check, and `Cert.maynard_M105_certified` conjoins both
the Z-level bool match and the rat-level paper-form bridge so a single
`Print Assumptions` covers the full FLINT-matrix → Z-spec → rat-paper-form
→ eigenvalue chain.  See SPEC_TO_PAPER.md for the line-level paper
mapping. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import GRing.Theory.

(* ------------------------------------------------------------------
   PART A — rat-level closed form.

   This is the definition that a mathematician reads and compares
   against Maynard's paper.  It uses factQ / binQ from MaynardFactQ.
   ------------------------------------------------------------------ *)

Local Open Scope ring_scope.

(* `compositions r n` is the set of length-`r` compositions of `n` with
   parts >= 1: every (b_1, ..., b_r) : seq nat with b_i >= 1 and
   \sum b_i = n.  This is the index set of the inner sum in Maynard's
   G_{n,2}(k) (Lemma 8.1 / v1 Lemma 7.1).  The recursion is:
     - r = 0: the only length-0 composition is the empty one, and it
              is a composition of 0 (and only 0).
     - r > 0: for each first part a in [1, remaining], recursively
              enumerate length-(r-1) compositions of remaining-a. *)
Fixpoint compositions_aux (r remaining : nat) : seq (seq nat) :=
  match r with
  | 0 => if (remaining == 0)%N then [:: [::] ] else [::]
  | S r' =>
      flatten
        [seq [seq (a :: tl) | tl <- compositions_aux r' (remaining - a)%N]
           | a <- iota 1 remaining]
  end.

Definition compositions (r n : nat) : seq (seq nat) := compositions_aux r n.

(* `cff a` is the per-composition inner factor of Lemma 8.1,
   character-for-character:
     cff(a) = \prod_(x <- a) (2x)! / x!.
   This is exactly Maynard's `\prod_i (2 b_i)! / b_i!` for the
   composition a = (b_1, ..., b_r). *)
Definition cff (a : seq nat) : rat :=
  \prod_(x <- a) (factQ (2 * x) / factQ x).

(* G_{n,2}(k) per Maynard Lemma 8.1 (= Lemma 7.1 in v1):
     G_{n,2}(k) = n! * \sum_{r=1}^{n} C(k, r)
                     * \sum_{a in compositions(r, n)} cff(a).
   The factQ n prefactor is exactly the paper's global  n!  factor in
   front of the double sum.  For n = 0 the convention is
   G_{0,2}(k) = 1 (the empty product). *)
Definition G_2 (n k : nat) : rat :=
  if (n == 0)%N then 1
  else
    factQ n
    * \sum_(r <- iota 1 n) binQ k r * \sum_(a <- compositions r n) cff a.

Definition K1 : nat := 105.
Definition K2 : nat := 104.

Definition M1_entry (bi ci bj cj : nat) : rat :=
  let b := (bi + bj)%N in
  let c := (ci + cj)%N in
  factQ b / factQ (K1 + b + 2 * c)%N * G_2 c K1.

Definition alpha (b c cp : nat) : rat :=
  binQ c cp * factQ b * factQ (2 * c - 2 * cp)%N
    / factQ (b + 2 * c - 2 * cp + 1)%N.

Definition M2_entry (bi ci bj cj : nat) : rat :=
  \sum_(cp1 <- iota 0 ci.+1)
    \sum_(cp2 <- iota 0 cj.+1)
      let bp1 := (bi + 2 * ci - 2 * cp1 + 1)%N in
      let bp2 := (bj + 2 * cj - 2 * cp2 + 1)%N in
      let bsum := (bp1 + bp2)%N in
      let csum := (cp1 + cp2)%N in
      alpha bi ci cp1 * alpha bj cj cp2
        * factQ bsum / factQ (K2 + bsum + 2 * csum)%N
        * G_2 csum K2.

Definition M1_spec_ij (i j : nat) : rat :=
  let bci := List.nth i maynard_basis (0%N, 0%N) in
  let bcj := List.nth j maynard_basis (0%N, 0%N) in
  M1_entry bci.1 bci.2 bcj.1 bcj.2.

Definition M2_spec_ij (i j : nat) : rat :=
  let bci := List.nth i maynard_basis (0%N, 0%N) in
  let bcj := List.nth j maynard_basis (0%N, 0%N) in
  M2_entry bci.1 bci.2 bcj.1 bcj.2.

(* ------------------------------------------------------------------
   PART B — Z-level closed form (num, den).

   All factorials are Z integers; the denominator is a factorial
   (for M1) or a product of factorials (for M2).  All intermediate
   divisions are exact.  This form avoids the costly rat-level gcd
   normalisation and is the form consumed by `MaynardVerify.v`.
   ------------------------------------------------------------------ *)

Local Close Scope ring_scope.
Local Open Scope Z_scope.

Fixpoint factZ (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * factZ k
  end.

(* Integer (2x)! / x!  — equals x! * C(2x, x), always divisible. *)
Definition dblratZ (x : nat) : Z := factZ (2 * x)%N / factZ x.

Fixpoint prod_dblratZ (xs : list nat) : Z :=
  match xs with
  | nil => 1
  | x :: r => dblratZ x * prod_dblratZ r
  end.

(* Z-level mirror of PART A's `compositions_aux` / `compositions`.
   Enumerates length-r compositions of n with parts >= 1. *)
Fixpoint compositions_auxZ (r remaining : nat) : list (list nat) :=
  match r with
  | O => if Nat.eqb remaining 0 then [nil] else nil
  | S r' =>
      List.flat_map
        (fun a =>
           List.map (fun tl => a :: tl)
                    (compositions_auxZ r' (remaining - a)%N))
        (List.seq 1 remaining)
  end.

Definition compositionsZ (r n : nat) : list (list nat) :=
  compositions_auxZ r n.

(* Z-level mirror of PART A's `cff`: just the product of (2x)!/x!. *)
Definition cffZ (a : list nat) : Z := prod_dblratZ a.

(* C(n, k) as Z, integer-valued. *)
Definition binZ (n k : nat) : Z :=
  if Nat.leb k n then factZ n / (factZ k * factZ (n - k)%N) else 0.

(* G_{n,2}(k) as Z, mirroring PART A's `G_2`:
     G_{n,2}(k) = n! * sum_{r=1..n} C(k, r)
                     * sum_{a in compositionsZ(r, n)} cffZ(a).
   The factZ n prefactor is the paper's global  n!  factor. *)
Definition G2Z (n k : nat) : Z :=
  if Nat.eqb n O then 1
  else
    factZ n
    * List.fold_left Z.add
        (List.map
           (fun r =>
              binZ k r
              * List.fold_left Z.add
                  (List.map cffZ (compositionsZ r n)) 0)
           (List.seq 1 n)) 0.

(* M1 as (num, den) in lowest common form built from factorials.
   num / den = b! / (K1 + b + 2c)! * G_{c,2}(K1).
   Choose num := b! * G2Z c K1, den := (K1 + b + 2c)!. *)

Definition K1n : nat := 105.
Definition K2n : nat := 104.

Definition m1_num_den (bi ci bj cj : nat) : Z * Z :=
  let b := (bi + bj)%N in
  let c := (ci + cj)%N in
  (factZ b * G2Z c K1n, factZ (K1n + b + 2 * c)%N).

(* M2 is a double sum.  Each term has shape
     alpha(bi,ci,cp1) * alpha(bj,cj,cp2)
       * (bsum)! / (K2n + bsum + 2 csum)!
       * G_{csum,2}(K2n)
   We sum with a common denominator per-term and cross-multiply into
   a single fraction with denom = prod (term denoms).  That is
   wasteful in bits but fine for vm_compute in Z.

   A simpler implementation: compute each term as (n_t, d_t) and sum
   using (a/b) + (c/d) = (ad + bc)/(bd), carrying state (N, D). *)

(* Rational addition in (Z * Z). *)
Definition qplus (p q : Z * Z) : Z * Z :=
  let '(a, b) := p in
  let '(c, d) := q in
  (a * d + c * b, b * d).

Definition qmul (p q : Z * Z) : Z * Z :=
  let '(a, b) := p in
  let '(c, d) := q in
  (a * c, b * d).

(* alpha as (num, den).  alpha = C(c,cp) * b! * (2c-2cp)! / (b+2c-2cp+1)!.
   C(c,cp) is an integer — so numerator is that integer times b! times
   (2c-2cp)!, and denominator is (b+2c-2cp+1)!. *)
Definition alphaZ (b c cp : nat) : Z * Z :=
  (binZ c cp * factZ b * factZ (2 * c - 2 * cp)%N,
   factZ (b + 2 * c - 2 * cp + 1)%N).

Definition m2_term_num_den (bi ci bj cj cp1 cp2 : nat) : Z * Z :=
  let bp1 := (bi + 2 * ci - 2 * cp1 + 1)%N in
  let bp2 := (bj + 2 * cj - 2 * cp2 + 1)%N in
  let bsum := (bp1 + bp2)%N in
  let csum := (cp1 + cp2)%N in
  qmul (qmul (alphaZ bi ci cp1) (alphaZ bj cj cp2))
       (factZ bsum * G2Z csum K2n, factZ (K2n + bsum + 2 * csum)%N).

Definition m2_num_den (bi ci bj cj : nat) : Z * Z :=
  List.fold_left
    (fun acc cp1 =>
       List.fold_left
         (fun acc2 cp2 => qplus acc2 (m2_term_num_den bi ci bj cj cp1 cp2))
         (List.seq 0 (S cj)) acc)
    (List.seq 0 (S ci)) (0, 1).

(* Index-based Z lookups. *)

Definition m1_num_den_at (i j : nat) : Z * Z :=
  let bci := List.nth i maynard_basis (0%N, 0%N) in
  let bcj := List.nth j maynard_basis (0%N, 0%N) in
  m1_num_den bci.1 bci.2 bcj.1 bcj.2.

Definition m2_num_den_at (i j : nat) : Z * Z :=
  let bci := List.nth i maynard_basis (0%N, 0%N) in
  let bcj := List.nth j maynard_basis (0%N, 0%N) in
  m2_num_den bci.1 bci.2 bcj.1 bcj.2.
