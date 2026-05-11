(* CertL2.v -- L2 assembly: prove charpoly_int_Dq_scaled.

   All lemmas in this file are Qed; no admits, no project axioms.
   The CRT lift (fl_eq_flint, matrix_identity_Z) is proved from
   710-prime modular agreement plus the FL-recurrence-based
   coefficient bound (see max_abs_entry_mzero and
   charpoly_coeff_bound upstream in CRTLift.v). *)

From Stdlib Require Import ZArith List Lia Uint63 Bool Znumtheory.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness CharPolyScale ModularArith CharPolyAgree.
From PrimeGapS1 Require Import Fermat CRTBridge PrimeCheck CRTCheck CRTLift.

Open Scope ring_scope.

(* ================================================================ *)
(*  Structural lemmas                                                 *)
(* ================================================================ *)

Lemma A_int_dim' : mat_dim A_int = 42%nat. Proof. exact A_int_dim. Qed.
Lemma A_int_wf' : forall i, (i < length A_int)%coq_nat -> length (List.nth i A_int []) = 42%nat.
Proof. by move=> i Hi; move: A_int_rows_42; rewrite List.forallb_forall =>
  /(_ _ (List.nth_In _ _ Hi)) /Nat.eqb_eq. Qed.
Lemma M1_int_dim' : mat_dim M1_int = 42%nat. Proof. vm_compute. reflexivity. Qed.
Lemma M1_int_rows_42 : forallb (fun row => Nat.eqb (List.length row) 42) M1_int = true.
Proof. vm_compute. reflexivity. Qed.
Lemma M1_int_wf' : all_rows_len 42 M1_int.
Proof. by move=> i Hi; move: M1_int_rows_42; rewrite List.forallb_forall =>
  /(_ _ (List.nth_In _ _ Hi)) /Nat.eqb_eq. Qed.

(* ================================================================ *)
(*  CRT lift helpers                                                   *)
(* ================================================================ *)

(* The CRT lift (fl_eq_flint, matrix_identity_Z, length_char_poly_int_A)
   is proved in CRTLift.v (imported above).  CRTLift.v has no MathComp
   imports, avoiding scope issues.  The coefficient bound used there
   comes from the FL (Faddeev–LeVerrier) recurrence combined with the
   max_abs_entry bound on the input matrix; see
   charpoly_coeff_bound / max_abs_entry_mzero in CRTLift.v. *)
Definition max_abs_entry (M : list (list Z)) : Z :=
  List.fold_left (fun acc row =>
    List.fold_left (fun acc2 x => Z.max acc2 (Z.abs x)) row acc) M BinNums.Z0.

(* fl_eq_flint, matrix_identity_Z, length_char_poly_int_A
   are proved in CRTLift.v (imported above). *)

(* ================================================================ *)
(*  Helpers                                                            *)
(* ================================================================ *)

Opaque Z_to_int.

Lemma pol_to_polyrat_coef0 (l : list Z) :
  l <> @nil Z -> (pol_to_polyrat l)`_0 = (Z_to_int (head Z0 l))%:~R :> rat.
Proof. by case: l => [//|z l'] _; rewrite /pol_to_polyrat coef_Poly. Qed.

Lemma Z_to_int_neq0' (D : BinInt.Z) : D <> BinInt.Z0 -> Z_to_int D != 0 :> int.
Proof. move=> HD; apply/eqP => Hz. apply HD.
  destruct D as [|p|p]; [reflexivity|exfalso|exfalso];
  (revert Hz; change (Z_to_int _) with (Posz (Pos.to_nat p)) ||
              change (Z_to_int _) with (Negz (Pos.to_nat p - 1)); intro Hz).
  - injection Hz => Hz'. have := Pos2Nat.is_pos p; rewrite Hz'; exact (Nat.lt_irrefl 0).
  - discriminate Hz. Qed.

Lemma intr_rat_eq0 (D : BinInt.Z) : (Z_to_int D)%:~R = 0 :> rat -> D = Z0.
Proof.
  case Hd: (Z.eqb D BinInt.Z0); first by move=> _; apply Z.eqb_eq, Hd.
  move=> Hzr; exfalso.
  have HD : D <> BinInt.Z0 by apply Z.eqb_neq, Hd.
  have Hne := Z_to_int_neq0' D HD.
  move: Hne; rewrite -(@intr_eq0 rat) Hzr eqxx.
  by [].
Qed.

Lemma ListDef_nth_eq (T : Type) (d : T) (l : list T) (n : nat) :
  ListDef.nth n l d = nth d l n.
Proof. by elim: l n => [|a l' IH] [|n'] //=. Qed.

Lemma Z_to_int_Zpow_rat (z : Z) (n : nat) :
  (Z_to_int (Z.pow z (Z.of_nat n)))%:~R = (Z_to_int z)%:~R ^+ n :> rat.
Proof. Transparent Z_to_int.
  elim: n => [|m IH].
  - by rewrite Z.pow_0_r /Z_to_int /= expr0.
  - by rewrite Nat2Z.inj_succ Z.pow_succ_r ?Z_to_int_mul ?intrM ?IH ?exprS //; lia.
Opaque Z_to_int. Qed.

Lemma mat_int_to_rat_scale_inv' (M : list (list BinInt.Z)) (D : BinInt.Z) (n : nat) :
  mat_int_to_rat M D n = (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n.
Proof. apply/matrixP => i j. rewrite /mat_int_to_rat !mxE GRing.mulr1. by rewrite GRing.mulrC. Qed.

(* ================================================================ *)
(*  M1 invertibility                                                   *)
(* ================================================================ *)

(* check_prime_Z / check_no_divisor / check_prime_Z_mc are imported from
   PrimeCheck.v above; fully proved, 0 axioms. *)

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
(*  A_rat and matrix identity                                          *)
(* ================================================================ *)

Definition A_rat : 'M[rat]_42 :=
  ((invmx (mat_int_to_rat M1_int D_M1 42)) *m mat_int_to_rat M2_int D_M2 42)%R.

Lemma mat_identity_rat :
  (Z_to_int D_M2)%:~R *: (mat_int_to_rat M1_int 1 42 *m mat_int_to_rat A_int 1 42) =
  ((Z_to_int D_M1)%:~R * (Z_to_int D_A)%:~R) *: mat_int_to_rat M2_int 1 42.
Proof.
  have HZ := matrix_identity_Z.
  set LHS := mscale D_M2 (mmul M1_int A_int) in HZ.
  set RHS := mscale (Z.mul D_M1 D_A) M2_int in HZ.
  have HLHS : mat_int_to_rat LHS 1 42 =
    (Z_to_int D_M2)%:~R *: mat_int_to_rat (mmul M1_int A_int) 1 42.
  { subst LHS. exact (mat_int_to_rat_mscale D_M2 (mmul M1_int A_int) 42). }
  have HRHS : mat_int_to_rat RHS 1 42 =
    ((Z_to_int D_M1)%:~R * (Z_to_int D_A)%:~R) *: mat_int_to_rat M2_int 1 42.
  { subst RHS.
    transitivity ((Z_to_int (Z.mul D_M1 D_A))%:~R *: mat_int_to_rat M2_int 1 42).
    - exact (mat_int_to_rat_mscale _ _ _).
    - set M2r := mat_int_to_rat M2_int 1 42.
      apply (f_equal (fun x => x *: M2r)).
      rewrite Z_to_int_mul. exact: intrM. }
  have Hmmul : mat_int_to_rat (mmul M1_int A_int) 1 42 =
    mat_int_to_rat M1_int 1 42 *m mat_int_to_rat A_int 1 42.
  { exact (mat_int_to_rat_mmul M1_int A_int 42 M1_int_dim' A_int_dim' M1_int_wf' A_int_wf'). }
  by rewrite -Hmmul -HLHS -HRHS HZ.
Qed.

(* [mat_A_scale_eq_Arat]: the structural equality `A_1_int = D_A *: A_rat`.
   This replaces the old `mat_A_eq_Arat` (which stated the equivalent
   `mat_int_to_rat A_int D_A 42 = A_rat` and depended on slow algebraic
   rewrites on the CONCRETE 42x42 matrix A_rat).  We bypass the slow
   rewrite by isolating the matrix-algebra steps into `abstract_mat_scale`,
   a generic-n helper, and only specialising to 42 at the Qed step. *)

Section AbstractMatScale.
Variable (F : fieldType) (n : nat).
Variables (M1_1 A_1_int M2_1 : 'M[F]_n) (c1 c2 cA : F).

Hypothesis Hc1 : c1 != 0.
Hypothesis Hc2 : c2 != 0.
Hypothesis Hu : M1_1 \in unitmx.
Hypothesis Hid : c2 *: (M1_1 *m A_1_int) = (c1 * cA) *: M2_1.

Lemma abstract_mat_scale :
  A_1_int = cA *: (invmx (c1^-1 *: M1_1) *m (c2^-1 *: M2_1)).
Proof.
  have Hc1' : c1^-1 != 0 by rewrite invr_neq0.
  have Hu' : c1^-1 *: M1_1 \in unitmx by rewrite unitmxZ ?unitfE.
  rewrite invmxZ // invrK.
  rewrite -scalemxAl -scalemxAr !scalerA.
  apply: (can_inj (mulKmx Hu)).
  rewrite !scalemxAr mulmxA mulmxV // mul1mx.
  apply: (can_inj (scalerK Hc2)).
  rewrite scalerA Hid.
  congr (_ *: _).
  by rewrite mulrCA mulrAC divff // mulr1 mulrC.
Qed.

End AbstractMatScale.

Lemma mat_A_scale_eq_Arat :
  mat_int_to_rat A_int 1 42 = (Z_to_int D_A)%:~R *: A_rat.
Proof.
  have HDM1 : D_M1 <> Z0 by discriminate.
  have HDM2 : D_M2 <> Z0 by discriminate.
  have HDM1_ne : (Z_to_int D_M1)%:~R != (0 : rat)
    by rewrite intr_eq0; exact: Z_to_int_neq0'.
  have HDM2_ne : (Z_to_int D_M2)%:~R != (0 : rat)
    by rewrite intr_eq0; exact: Z_to_int_neq0'.
  have HM1_unit : mat_int_to_rat M1_int 1 42 \in unitmx by exact: M1_1_unit.
  have Hid := mat_identity_rat.
  have Hscale := @abstract_mat_scale rat 42%N
    (mat_int_to_rat M1_int 1 42)
    (mat_int_to_rat A_int 1 42)
    (mat_int_to_rat M2_int 1 42)
    (Z_to_int D_M1)%:~R (Z_to_int D_M2)%:~R (Z_to_int D_A)%:~R
    HDM1_ne HDM2_ne HM1_unit Hid.
  rewrite /A_rat (mat_int_to_rat_scale_inv' M1_int D_M1 42)
                 (mat_int_to_rat_scale_inv' M2_int D_M2 42).
  exact Hscale.
Qed.

(* ================================================================ *)
(*  Per-coefficient scaling                                            *)
(* ================================================================ *)

Lemma scaling_Z (k : nat) : (k < 43)%coq_nat ->
  Z.mul (List.nth k charpoly_int BinNums.Z0) (Z.pow D_A (Z.of_nat (42 - k))) =
  Z.mul D_q (List.nth k charpoly_of_A_int BinNums.Z0).
Proof. intro Hk. exact: scaling_Z_from_check. Qed.

Lemma length_charpoly_int : List.length charpoly_int = 43%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma length_charpoly_of_A_int : List.length charpoly_of_A_int = 43%nat.
Proof. unfold charpoly_of_A_int. rewrite List.length_map.
  exact charpoly_of_A_int_bigZ_length. Qed.

(* ================================================================ *)
(*  charpoly_int_Dq_scaled -- the headline L2 fact                    *)
(* ================================================================ *)

(* [charpoly_int_Dq_scaled]: per-coefficient proof via `char_poly_scale` +
   `scaling_Z` + `mat_A_scale_eq_Arat`.

   SKETCH:
   - From `scaling_Z`: for k <= 42,
       charpoly_int[k] * D_A^(42-k) = D_q * charpoly_of_A_int[k]    (in Z)
   - From `char_poly_int_correct + fl_eq_flint`:
       pol_to_polyrat charpoly_of_A_int = char_poly (mat_int_to_rat A_int 1 42)
   - From `mat_A_scale_eq_Arat`:
       mat_int_to_rat A_int 1 42 = D_A *: A_rat
     Hence char_poly (mat_int_to_rat A_int 1 42) = char_poly (D_A *: A_rat)
     and by `CharPolyScale.char_poly_scale`:
       (char_poly (D_A *: A_rat))[k] = D_A^(42-k) * (char_poly A_rat)[k]
   - Combining, for k <= 42:
       charpoly_int[k] * D_A^(42-k) = D_q * D_A^(42-k) * (char_poly A_rat)[k]
     and since D_A^(42-k) != 0, divide to conclude
       charpoly_int[k] = D_q * (char_poly A_rat)[k].
   - k > 42: both sides are 0 by nth_default + size_char_poly. *)
(* Coefficient extractor for pol_to_polyrat: (pol_to_polyrat l)`_k = embed (nth k l 0). *)
Lemma pol_to_polyrat_coef (l : list Z) (k : nat) :
  (k < List.length l)%nat ->
  (pol_to_polyrat l)`_k = (Z_to_int (List.nth k l Z0))%:~R :> rat.
Proof.
  move=> Hk. rewrite /pol_to_polyrat coef_Poly -ListDef_nth_eq.
  elim: l k Hk => [|z l' IH] [|k'] //= Hk.
  apply: IH. simpl in Hk. by apply/leP; lia.
Qed.

(* === KEY: abstract-field auxiliary lemmas to bypass the canonical-structure
       elaboration hang at concrete dim n=42.

   DIAGNOSIS: Tactics like `apply: char_poly_scale`, `exact: expf_neq0`, and
   `rewrite Hcpi` (where Hcpi mentions `char_poly (mat_int_to_rat A_int 1 42)`)
   all trigger MathComp's canonical-structure resolution to elaborate the
   `char_poly` / `char_poly_mx` / `map_mx` instances at fully-concrete dim 42.
   This resolution does not unfold any specific term quickly — instead it walks
   the HB instance graph looking for the right scalar/field structure, which
   becomes quadratic-ish in the goal term size once A_rat (a 42x42 invmx *m
   matrix over rat) appears in the goal.

   FIX: Extract the slow MathComp steps into `Lemma char_poly_scale_rat42`
   (only specialised to rat, dim 42) and `Lemma expf_neq0_rat` / `Lemma
   size_char_poly_42`. Inside these aux lemmas the context is SMALL, so
   elaboration is fast. At the call site we plug them in via term-mode
   (`:= aux_lemma _ _`), completely bypassing apply/exact tactic elaboration.

   Also: `pose c := (char_poly A_rat)`_k; change (char_poly ..)`_k with c`
   abstracts the offending term out of the goal BEFORE subsequent
   rewrite/apply tactics, so the final algebra reasoning is on pure-rat
   variables. *)

Lemma char_poly_scale_rat42 (c : rat) (M : 'M[rat]_42) (k : nat) :
  c != 0 -> (k <= 42)%N ->
  (char_poly (c *: M))`_k = c ^+ (42 - k) * (char_poly M)`_k.
Proof. exact: char_poly_scale. Qed.

Lemma expf_neq0_rat (c : rat) (n : nat) : c != 0 -> c ^+ n != 0.
Proof. exact: expf_neq0. Qed.

Lemma size_char_poly_42 (M : 'M[rat]_42) : size (char_poly M) = 43.
Proof. exact: size_char_poly. Qed.

Lemma size_pol_to_polyrat_bound (l : list Z) :
  (size (pol_to_polyrat l) <= List.length l)%nat.
Proof.
  rewrite /pol_to_polyrat.
  apply: leq_trans (size_Poly _) _.
  have : seq.size (ListDef.map (fun z => (Z_to_int z)%:~R : rat) l) = List.length l.
  { elim: l => //= a xs IH. by rewrite IH. }
  move=> ->. by [].
Qed.

(* Generic-rat cancellation: at the final step the goal is of the form
   a = e * c. We have Hb_eq : b = d * c, Hab : a * d = e * b, Hd_ne : d != 0.
   This is purely rat-level so no canonical-structure hang occurs. *)
Lemma mat_cancel_helper (a b c d e : rat)
  (Hb_eq : b = d * c) (Hab : a * d = e * b) (Hd_ne : d != 0) : a = e * c.
Proof.
  apply: (mulIf Hd_ne).
  rewrite Hab Hb_eq. by rewrite mulrCA mulrC.
Qed.

Lemma charpoly_int_Dq_scaled :
  pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat.
Proof.
  have Hcpi := @char_poly_int_correct A_int 42%nat A_int_dim' A_int_wf'.
  have Hfl := fl_eq_flint.
  have HDA : D_A <> BinInt.Z0 by discriminate.
  have HDA_ne : (Z_to_int D_A)%:~R != (0 : rat)
    by rewrite intr_eq0; exact: Z_to_int_neq0'.
  have HA1 : mat_int_to_rat A_int 1 42 = (Z_to_int D_A)%:~R *: A_rat
    by exact: mat_A_scale_eq_Arat.
  (* Build Hcda via term-mode to avoid slow `rewrite Hcpi` elaboration. *)
  have Hfl' : char_poly_int A_int = charpoly_of_A_int.
  { rewrite -charpoly_Z_A_eq. exact Hfl. }
  have Hcda : pol_to_polyrat charpoly_of_A_int = char_poly ((Z_to_int D_A)%:~R *: A_rat)
    := eq_trans (f_equal pol_to_polyrat (esym Hfl'))
         (eq_trans Hcpi (f_equal (@char_poly _ 42) HA1)).
  apply/polyP => k.
  rewrite coefZ.
  case: (leqP k 42) => [Hk|Hk]; last first.
  { (* k > 42 branch: both sides are 0 *)
    have Hlhs_z : (pol_to_polyrat charpoly_int)`_k = 0.
    { apply: nth_default. apply: leq_trans (size_pol_to_polyrat_bound _) _.
      by rewrite length_charpoly_int. }
    have Hrhs_z : (char_poly A_rat)`_k = 0.
    { apply: nth_default. by rewrite size_char_poly_42. }
    by rewrite Hlhs_z Hrhs_z mulr0. }
  (* k <= 42 branch: term-mode construction of the key facts *)
  have HdApow : (Z_to_int D_A)%:~R ^+ (42 - k) != (0 : rat)
    := expf_neq0_rat _ _ HDA_ne.
  have Hscale : (char_poly ((Z_to_int D_A)%:~R *: A_rat))`_k =
                (Z_to_int D_A)%:~R ^+ (42 - k) * (char_poly A_rat)`_k
    := char_poly_scale_rat42 _ _ _ HDA_ne Hk.
  have Hk' : (k < 43)%coq_nat by apply/ltP; rewrite ltnS.
  have Hlenint : (k < List.length charpoly_int)%nat
    by rewrite length_charpoly_int; apply/ltP; lia.
  have HlencpA : (k < List.length charpoly_of_A_int)%nat
    by rewrite length_charpoly_of_A_int; apply/ltP; lia.
  have Hpp_int_k : (pol_to_polyrat charpoly_int)`_k =
    (Z_to_int (List.nth k charpoly_int Z0))%:~R
    := pol_to_polyrat_coef _ _ Hlenint.
  have Hpp_cpA_k : (pol_to_polyrat charpoly_of_A_int)`_k =
    (Z_to_int (List.nth k charpoly_of_A_int Z0))%:~R
    := pol_to_polyrat_coef _ _ HlencpA.
  have HcpA_of_A : (Z_to_int (List.nth k charpoly_of_A_int Z0))%:~R =
    (Z_to_int D_A)%:~R ^+ (42 - k) * (char_poly A_rat)`_k :> rat.
  { rewrite -Hpp_cpA_k Hcda. exact Hscale. }
  rewrite Hpp_int_k.
  (* Lift the Z identity to rat via term-mode reasoning. *)
  have HZ := scaling_Z k Hk'.
  have HZrat : (Z_to_int (List.nth k charpoly_int Z0))%:~R *
               (Z_to_int D_A)%:~R ^+ (42 - k) =
               (Z_to_int D_q)%:~R *
               (Z_to_int (List.nth k charpoly_of_A_int Z0))%:~R :> rat.
  { have Hlift := f_equal (fun z : Z => (Z_to_int z)%:~R : rat) HZ.
    move: Hlift. rewrite !Z_to_int_mul !intrM Z_to_int_Zpow_rat. exact id. }
  (* Abstract (char_poly A_rat)`_k as `c` before the final manipulation to
     avoid repeated canonical-structure elaboration. *)
  pose c : rat := (char_poly A_rat)`_k.
  rewrite -/c in HcpA_of_A.
  change (char_poly A_rat)`_k with c.
  apply: mat_cancel_helper; [exact HcpA_of_A | exact HZrat | exact HdApow].
Qed.
