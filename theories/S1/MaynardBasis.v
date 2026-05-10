(* ==================================================================
   MaynardBasis.v — the 42-element basis used by Maynard's spec.

   Order is the Mathematica xExponents[5]/yExponents[5] enumeration
   (see python/flint_probe.py:xExponents_mma / yExponents_mma).
   ================================================================== *)

From Stdlib Require Import List Lia.
From mathcomp Require Import all_ssreflect zify.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition maynard_basis : list (nat * nat) :=
  [ (0, 0); (1, 0); (0, 1); (2, 0); (1, 1); (3, 0)
  ; (0, 2); (2, 1); (4, 0); (1, 2); (3, 1); (5, 0)
  ; (0, 3); (2, 2); (4, 1); (6, 0); (1, 3); (3, 2)
  ; (5, 1); (7, 0); (0, 4); (2, 3); (4, 2); (6, 1)
  ; (8, 0); (1, 4); (3, 3); (5, 2); (7, 1); (9, 0)
  ; (0, 5); (2, 4); (4, 3); (6, 2); (8, 1); (10, 0)
  ; (1, 5); (3, 4); (5, 3); (7, 2); (9, 1); (11, 0)
  ]%nat.

Lemma maynard_basis_size : length maynard_basis = 42.
Proof. reflexivity. Qed.

(* ==================================================================
   Set-level characterization of the basis.

   The hand-listed 42 pairs are pinned to the canonical predicate
   `b + 2c <= 11` so a reviewer never has to inspect the literal list:
   the basis is exactly the multiset {(b, c) in N^2 : b + 2c <= 11}.
   ================================================================== *)

(* Canonical enumeration of {(b, c) : b + 2c <= 11}, as a filter on
   the cartesian product of bounded ranges. *)
Definition canonical_basis : seq (nat * nat) :=
  [seq p <- [seq (b, c) | b <- iota 0 12, c <- iota 0 6]
        | (p.1 + 2 * p.2 <= 11)%N].

Lemma maynard_basis_perm_canonical :
  perm_eq maynard_basis canonical_basis.
Proof. by vm_compute. Qed.

Lemma canonical_basis_spec p :
  (p \in canonical_basis) = (p.1 + 2 * p.2 <= 11)%N.
Proof.
  case: p => b c.
  rewrite /canonical_basis mem_filter.
  case Hp: (b + 2 * c <= 11)%N => /=; last by [].
  have Hb : b \in iota 0 12.
    rewrite mem_iota /= add0n ltnS.
    by apply: leq_trans Hp; rewrite leq_addr.
  have Hc : c \in iota 0 6.
    rewrite mem_iota /= add0n.
    have H2c : 2 * c <= 11 by apply: leq_trans Hp; rewrite leq_addl.
    lia.
  exact: (allpairs_f (fun a d => (a, d)) Hb Hc).
Qed.

(* Headline: the basis is exactly the set {(b, c) : b + 2c <= 11}. *)
Lemma maynard_basis_spec p :
  (p \in maynard_basis) = (p.1 + 2 * p.2 <= 11)%N.
Proof.
  by rewrite (perm_mem maynard_basis_perm_canonical) canonical_basis_spec.
Qed.

(* Together with maynard_basis_size = 42 and the bound `b + 2c <= 11`,
   uniqueness pins the basis to a true set (no repeats). *)
Lemma maynard_basis_uniq : uniq maynard_basis.
Proof. by vm_compute. Qed.
