(* ==================================================================
   AbstractPencilHelper.v

   `abstract_pencil_scale`: the K-scaled rearrangement identity used
   by `CertPencil.pencil_rat_eq_int_scaled`.  Pure rational-field
   algebra over 'M[rat]_n; isolated into its own file so that
   `CertPencil.v` doesn't have to load `mathcomp.algebra_tactics`
   (~ adds several GB of RSS to CertPencil's compile via the `field`
   tactic on concrete 'M[rat]_42 matrices).
   ================================================================== *)

From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.algebra_tactics Require Import ring.
From PrimeGapS1 Require Import CharPoly Bridge.   (* Z_to_int + Z_to_int_mul *)

Import GRing.Theory.
Local Open Scope ring_scope.

(* Universally-quantified scalar identities, proved here so that
   ssreflect's `rewrite intrM` walks ONLY the abstract `a, b, c : Z`
   pattern — not the concrete 42×42 'M[rat]_42 cells in downstream
   `CertPencil.v` goals (each `%:~R` match would branch combinatorially
   through every matrix entry → >16 GB RSS / OOM). *)

Lemma Z_to_int_mul_mul_intrM_three (a b c : Z) :
  ((Z_to_int (Z.mul (Z.mul a b) c))%:~R : rat) =
  (Z_to_int a)%:~R * (Z_to_int b)%:~R * (Z_to_int c)%:~R.
Proof. by rewrite !Z_to_int_mul !intrM. Qed.

Lemma Z_to_int_mul_intrM_two (a b : Z) :
  ((Z_to_int (Z.mul a b))%:~R : rat) =
  (Z_to_int a)%:~R * (Z_to_int b)%:~R.
Proof. by rewrite Z_to_int_mul intrM. Qed.

(* Z_to_int distributes over Z.opp.  Proved here (outside the heavy
   matrix context of CertPencil.v) to avoid the `case: ... => /=; first
   by [].` timing out when goal context contains 'M[rat]_42 cells. *)
Lemma Z_to_int_opp (z : Z) : Z_to_int (Z.opp z) = - Z_to_int z.
Proof.
  Transparent Z_to_int.
  case: z => [|p|p] /=; first by rewrite oppr0.
  - by rewrite NegzE;
      congr (- _)%R;
      case E: (Pos.to_nat p) => [|n];
        [have := Pos2Nat.is_pos p; rewrite E => /Nat.nlt_0_r []
        |rewrite subn1].
  - by rewrite NegzE opprK;
      case E: (Pos.to_nat p) => [|n];
        [have := Pos2Nat.is_pos p; rewrite E => /Nat.nlt_0_r []
        |rewrite subn1].
Qed.

(* Negation form: (Z_to_int (-(a * b)))%:~R = - ((Z_to_int a)%:~R * (Z_to_int b)%:~R) *)
Lemma Z_to_int_opp_mul_intrM (a b : Z) :
  ((Z_to_int (Z.opp (Z.mul a b)))%:~R : rat) =
  - ((Z_to_int a)%:~R * (Z_to_int b)%:~R).
Proof. by rewrite Z_to_int_opp intrN Z_to_int_mul_intrM_two. Qed.

Section AbstractPencilBridge.
Variables (n : nat) (M1' M2' : 'M[rat]_n).
Variables (cM1 cM2 c105 c4 : rat).
Hypothesis HcM1 : cM1 != 0.
Hypothesis HcM2 : cM2 != 0.
Hypothesis Hc105 : c105 != 0.

Let K_abs : rat := c105 * cM1 * cM2.

Lemma abstract_pencil_scale :
  K_abs *: ((c4 / c105) *: (cM1^-1 *: M1') - cM2^-1 *: M2') =
  (c4 * cM2) *: M1' - (c105 * cM1) *: M2'.
Proof.
  rewrite /K_abs scalerBr !scalerA.
  have E1 : c105 * cM1 * cM2 * (c4 / c105) * cM1^-1 = c4 * cM2.
  { by field; rewrite Hc105 HcM1. }
  have E2 : c105 * cM1 * cM2 * cM2^-1 = c105 * cM1.
  { by field; exact HcM2. }
  by rewrite E1 E2.
Qed.

End AbstractPencilBridge.
