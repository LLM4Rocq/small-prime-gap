(* CertL2.v -- structural lemmas surfaced by the pencil-determinant
   route on the `quad` branch.

   Exports:
   - Dimension / well-formedness facts on M1_int (`M1_int_dim'`,
     `M1_int_wf'`, `M1_int_rows_42`) used by the M1-determinant /
     pencil-determinant Hadamard chains.
   - Rational-form M1 inverse witness (`A_rat`, `M1_1_unit`,
     `M1_charpoly_hd_neq0`) used by `CertPencil.v` to lift the
     integer-pencil determinant identity into a `char_poly A_rat`
     statement.
   - Small `pol_to_polyrat` helper (`pol_to_polyrat_coef0`) used by
     the same lift. *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness ModularArith.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import Fermat CRTBridge PrimeCheck CRTCheck CRTLift.

Open Scope ring_scope.

(* ================================================================ *)
(*  Structural lemmas on M1_int                                       *)
(* ================================================================ *)

Lemma M1_int_dim' : mat_dim M1_int = 42%nat. Proof. vm_compute. reflexivity. Qed.
Lemma M1_int_rows_42 : forallb (fun row => Nat.eqb (List.length row) 42) M1_int = true.
Proof. vm_compute. reflexivity. Qed.
Lemma M1_int_wf' : all_rows_len 42 M1_int.
Proof. by move=> i Hi; move: M1_int_rows_42; rewrite List.forallb_forall =>
  /(_ _ (List.nth_In _ _ Hi)) /Nat.eqb_eq. Qed.

(* ================================================================ *)
(*  Helpers                                                            *)
(* ================================================================ *)

Opaque Z_to_int.

Lemma pol_to_polyrat_coef0 (l : list Z) :
  l <> @nil Z -> (pol_to_polyrat l)`_0 = (Z_to_int (head Z0 l))%:~R :> rat.
Proof. by case: l => [//|z l'] _; rewrite /pol_to_polyrat coef_Poly. Qed.

Lemma mat_int_to_rat_scale_inv' (M : list (list BinInt.Z)) (D : BinInt.Z) (n : nat) :
  mat_int_to_rat M D n = (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n.
Proof. apply/matrixP => i j. rewrite /mat_int_to_rat !mxE GRing.mulr1. by rewrite GRing.mulrC. Qed.

Lemma Z_to_int_neq0' (D : BinInt.Z) : D <> BinInt.Z0 -> Z_to_int D != 0 :> int.
Proof. Transparent Z_to_int. move=> HD; apply/eqP => Hz. apply HD.
  destruct D as [|p|p]; [reflexivity|exfalso|exfalso];
  (revert Hz; change (Z_to_int _) with (Posz (Pos.to_nat p)) ||
              change (Z_to_int _) with (Negz (Pos.to_nat p - 1)); intro Hz).
  - injection Hz => Hz'. have := Pos2Nat.is_pos p; rewrite Hz'; exact (Nat.lt_irrefl 0).
  - discriminate Hz. Qed.

Lemma intr_rat_eq0 (D : BinInt.Z) : (Z_to_int D)%:~R = 0 :> rat -> D = Z0.
Proof. Transparent Z_to_int. move/eqP. rewrite intr_eq0 => /eqP H.
  destruct D as [|p|p]; [reflexivity|exfalso|exfalso].
  - simpl Z_to_int in H. injection H => H'. have := Pos2Nat.is_pos p; rewrite H'; exact (Nat.lt_irrefl 0).
  - discriminate H. Opaque Z_to_int. Qed.

(* ================================================================ *)
(*  M1 invertibility                                                   *)
(* ================================================================ *)

(* check_no_divisor / check_prime_Z / check_prime_Z_mc imported from PrimeCheck.v *)

Lemma M1_charpoly_hd_neq0 : head Z0 (char_poly_int M1_int) <> Z0.
Proof.
  set p := List.hd 0%uint63 crt_primes_all.
  (* 1. valid_prime p *)
  assert (Hvp : valid_prime p) by (split; vm_compute; reflexivity).
  (* 2. square_mat 42 M1_int *)
  assert (Hsq : square_mat (length M1_int) M1_int).
  { split; [exact M1_int_dim' | exact M1_int_wf']. }
  (* 3. bound: 43 < to_Z p *)
  assert (Hbound : BinInt.Z.lt (BinInt.Z.add (Z.of_nat (length M1_int)) 1) (Uint63.to_Z p))
    by (vm_compute; reflexivity).
  (* 4. FL divisibility *)
  assert (Hfl : fl_all_divisible (length M1_int) Z.one M1_int
    (meye (length M1_int)) (mzero (length M1_int)) Z.one).
  { exact (fl_all_divisible_from_L2 M1_int (length M1_int)
      (Logic.eq_refl _) M1_int_wf'). }
  (* 5. Fermat condition via primality *)
  assert (Hprime : prime (Z.to_nat (Uint63.to_Z p))).
  { apply check_prime_Z_mc. vm_compute. reflexivity. }
  assert (Hfermat : forall j : Z, BinInt.Z.lt 0 j /\ BinInt.Z.lt j (Uint63.to_Z p) ->
    BinInt.Z.eq (BinInt.Z.modulo (BinInt.Z.mul j (BinInt.Z.pow j (BinInt.Z.sub (Uint63.to_Z p) 2))) (Uint63.to_Z p))
               (BinInt.Z.modulo 1 (Uint63.to_Z p))).
  { apply fermat_Z; [|exact Hprime]. destruct Hvp as [H1 _]. exact H1. }
  (* 6. Apply char_poly_mod_sound *)
  assert (Hsound := char_poly_mod_sound p M1_int Hvp Hsq Hbound Hfl Hfermat).
  (* Hsound : map (Z_to_mod63 p) (char_poly_int M1_int) = char_poly_mod p M1_int *)
  (* 7. hd of char_poly_mod p M1_int != 0 (one-shot vm_compute on the
     first 710-prime) *)
  assert (Hnz_mod : Uint63.eqb (List.hd 0%uint63 (char_poly_mod p M1_int)) 0%uint63 = false).
  { vm_compute. reflexivity. }
  (* 8. Connect: hd of map f l = f (hd d l) for non-nil l *)
  intro Habs.
  assert (Hne : char_poly_int M1_int <> nil).
  { unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. }
  destruct (char_poly_int M1_int) as [|c cs] eqn:Hcp; [contradiction|].
  simpl in Habs. simpl in Hsound.
  assert (Hcz : Z_to_mod63 p c = 0%uint63).
  { subst c. apply Uint63.to_Z_inj. rewrite Z_to_mod63_spec; [|exact Hvp].
    rewrite Z.mod_0_l; [reflexivity | destruct Hvp; lia]. }
  assert (Hmap_hd : Z_to_mod63 p c = List.hd 0%uint63 (char_poly_mod p M1_int)).
  { rewrite -Hsound. reflexivity. }
  rewrite Hcz in Hmap_hd. rewrite -Hmap_hd in Hnz_mod.
  rewrite Uint63.eqb_refl in Hnz_mod. discriminate.
Qed.

Lemma M1_1_unit : mat_int_to_rat M1_int 1 42 \in unitmx.
Proof.
  have Hcpi := @char_poly_int_correct M1_int 42 M1_int_dim' M1_int_wf'.
  have Hne : char_poly_int M1_int <> nil.
  { unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. }
  rewrite unitmxE GRing.unitfE.
  apply/negP => /eqP Hdet0.
  apply M1_charpoly_hd_neq0; apply: intr_rat_eq0.
  rewrite -(pol_to_polyrat_coef0 _ Hne) Hcpi.
  by rewrite char_poly_det Hdet0 mulr0.
Qed.

(* ================================================================ *)
(*  A_rat                                                             *)
(* ================================================================ *)

Definition A_rat : 'M[rat]_42 :=
  ((invmx (mat_int_to_rat M1_int D_M1 42)) *m mat_int_to_rat M2_int D_M2 42)%R.
