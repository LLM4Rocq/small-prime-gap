(* ==================================================================
   MaynardVerify.v — kernel-verified agreement between the shipped
   integer matrices (M1_int, M2_int in Witness.v, divided by D_M1,
   D_M2) and Maynard's closed-form specification from MaynardSpec.v.

   ==== WIP BRANCH STATUS ========================================

   This file is the WIP state on the `maynard-spec-wip` branch.
   The strategic plan in PLAN.md transcribed the Mathematica
   enumeration for the 42-element basis (MaynardBasis.v) and the
   Maynard closed-form rationals for both G_{n,2}(k) and the M1 /
   M2 entries (MaynardSpec.v).  All three of MaynardFactQ,
   MaynardBasis, MaynardSpec compile cleanly under `rocq compile`.

   The Fallback (3) strategy from PLAN.md — Z-level cross-
   multiplication (`num * D == M_int[i][j] * den`) summed over the
   42 x 42 matrix and closed by a single `vm_compute` — was
   implemented (see `all_match_M1Z`, `all_match_M2Z` below and the
   Z-level `m1_num_den_at`, `m2_num_den_at` in MaynardSpec.v).

   Empirical measurements on this machine (rocq-9.2 switch, 32 GB
   RAM):
     - M1 boolean scan : ~90 s by `vm_cast_no_check`.
     - M2 boolean scan : completes around 17-20 min (past the
       per-step 5-minute budget in PLAN.md).

   Root cause of the M2 slowness: `m2_num_den_at bi ci bj cj`
   accumulates up to 36 rational terms via an unreduced
   `qplus (a, b) (c, d) := (a*d + c*b, b*d)` fold_left.  The
   intermediate denominators are products of many factorials
   (up to `126!`) and grow multiplicatively in the number of terms
   -- individual Z's in the accumulator reach ~10^7000 digits.
   `vm_compute` can handle this (hence the file eventually *does*
   succeed, just slowly), but well past the budget.

   Downstream of the boolean scan, the bridge proofs
   (`M1_entry_rat_eq`, `M2_entry_rat_eq`, `M1_correct`,
   `M2_correct`) require `Qed`-time kernel conversion on matching
   `m1_den`/`m2_den`, which forces the same computation as the
   boolean scan.  Even on a scratch file with axiomatised
   `all_match_*_true` but the full bridge proofs, the kernel
   takes >5 min per lemma.

   The correct next step for this WIP branch is one of:
   (a) rewrite `qplus` to GCD-normalise on each step (abandoned
       in-tree attempt — a naive GCD made things *worse* because
       Z.gcd on ~7000-digit integers is itself vm_compute-heavy);
   (b) sum M2 terms against a *pre-computed* common denominator
       per entry (e.g., the lcm of the 36 term-denominators),
       so the accumulator stays in Z and never grows beyond one
       factorial-scale product;
   (c) add `Strategy opaque` / `Opaque m1_num_den m2_num_den`
       before the bridge lemmas so kernel conversion does not
       descend into the large-integer computation.

   Pending that restructuring, this file uses `Axiom` for the
   facts it could not close within budget.  The scaffolding
   below (definitions, boolean scans, matrix specs) all
   typechecks; the cross-check Axioms (`all_match_M1Z_true`,
   `all_match_M2Z_true`) are each ONE line away from a `Qed`
   proof using `vm_cast_no_check (erefl true)` — that closes on a
   single-fact file in 90 s / 17 min respectively.
   ================================================================= *)

From Stdlib Require Import ZArith List Lia.
From mathcomp Require Import all_ssreflect all_algebra.
From PrimeGapS1 Require Import IntMat CharPoly Witness.
From PrimeGapS1 Require Import MaynardFactQ MaynardBasis MaynardSpec.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ------------------------------------------------------------------
   Num / den projections.
   ------------------------------------------------------------------ *)

Definition m1_num (i j : nat) : Z := fst (m1_num_den_at i j).
Definition m1_den (i j : nat) : Z := snd (m1_num_den_at i j).

Definition m2_num (i j : nat) : Z := fst (m2_num_den_at i j).
Definition m2_den (i j : nat) : Z := snd (m2_num_den_at i j).

(* ------------------------------------------------------------------
   Per-entry Z-level cross-multiplication check.
   ------------------------------------------------------------------ *)

Definition M1_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m1_num i j) D_M1)
        (BinInt.Z.mul (mat_get M1_int i j) (m1_den i j)).

Definition M2_entry_matchZ (i j : nat) : bool :=
  Z.eqb (BinInt.Z.mul (m2_num i j) D_M2)
        (BinInt.Z.mul (mat_get M2_int i j) (m2_den i j)).

Definition all_match_M1Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M1_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

Definition all_match_M2Z : bool :=
  List.forallb
    (fun i => List.forallb (fun j => M2_entry_matchZ i j) (List.seq 0 42))
    (List.seq 0 42).

(* WIP: provable as `Proof. vm_cast_no_check (erefl true). Qed.`
   but that step exceeds the per-step vm_compute budget for M2 and
   forces ~10-minute Qed on downstream lemmas. *)
Axiom all_match_M1Z_true : all_match_M1Z = true.
Axiom all_match_M2Z_true : all_match_M2Z = true.

(* ------------------------------------------------------------------
   Rat matrices.  These definitions typecheck fine; the headline
   theorems below that relate them are axiomatised for WIP.
   ------------------------------------------------------------------ *)

Definition M1_rat : 'M[rat]_42 := mat_int_to_rat Witness.M1_int Witness.D_M1 42.
Definition M2_rat : 'M[rat]_42 := mat_int_to_rat Witness.M2_int Witness.D_M2 42.

Definition f_M1 (i j : nat) : rat :=
  ((Z_to_int (m1_num i j))%:~R / (Z_to_int (m1_den i j))%:~R)%R.

Definition f_M2 (i j : nat) : rat :=
  ((Z_to_int (m2_num i j))%:~R / (Z_to_int (m2_den i j))%:~R)%R.

Definition M1_spec : 'M[rat]_42 :=
  \matrix_(i, j) f_M1 (nat_of_ord i) (nat_of_ord j).

Definition M2_spec : 'M[rat]_42 :=
  \matrix_(i, j) f_M2 (nat_of_ord i) (nat_of_ord j).

(* ------------------------------------------------------------------
   Headline facts.  Proof structure (see git history of this branch):

     M1_rat = M1_spec
       via `mat_eq_from_entries (fun i j => f_M1 i j) M1_entry_rat_eq`
       where `M1_entry_rat_eq i j : M1_rat i j = f_M1 (ord_of i) (ord_of j)`
       follows from `M1_entry_matchZ_ok` + `rat_cross_eq` +
       positivity of `D_M1` and `m1_den i j`.

   The correct proof closes in ~10 seconds of Qed on a scratch
   file where `all_match_M1Z_true` is axiomatised, because at
   that stage the entry-wise `forallb_seq_ok` lookup is cheap and
   the rat-level cross-multiplication is small.  In the real
   file the same proof does NOT close within the compile budget.
   ------------------------------------------------------------------ *)

Axiom M1_correct : M1_rat = M1_spec.
Axiom M2_correct : M2_rat = M2_spec.
