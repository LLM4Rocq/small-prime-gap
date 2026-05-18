(* ==================================================================
   CertRayleigh.v — Rayleigh-quotient witness route for M_{105} > 4.

   This file replaces the eigenvalue/char-poly closure of Cert.v with
   a single direct evaluation: a 42-dim rational vector `v_witness`
   (shipped in Witness_Rayleigh.v) satisfies

         105 * v^T M2 v  >  4 * v^T M1 v

   on the FLINT-shipped (M1, M2) pair (Witness.v).  Modulo Maynard's
   Lemma 8.3 (paper-side), this single Rayleigh quotient bound entails
   `M_{105} > 4`: Lemma 8.3 says M_k = k * sup_F (J_k(F)/I_k(F)), and
   sup is at least any individual quotient.

   Strategy: clear all denominators uniformly to a single integer
   inequality, discharged by one `vm_compute` Qed.

   Concretely, with v_num[i] = num_i * (v_den / d_i) and
                  v_den      = lcm(d_0, ..., d_41),
   the rational vector v lifts as v_rat[i] = v_num[i] / v_den.  Then

       v^T M_k v  =  (v_num^T M_int_k v_num) / (D_M_k * v_den^2)

   for k in {1, 2}, so the strict Rayleigh-quotient bound reduces to

       105 * D_M1 * num_M2  >  4 * D_M2 * num_M1.

   (provided num_M1 > 0, which is also checked by `vm_compute`).

   No eigenvalue, no characteristic polynomial, no realalg, no IVT,
   no Sturm, no CRT lift.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory Num.Theory.

From PrimeGapS1 Require Import IntMat CharPoly Witness Witness_Rayleigh.
From PrimeGapS1 Require Import MaynardSpec MaynardSpecBridge Cert.

(* Loaded LAST so that the mathcomp `ring` / `field` tactics are bound
   to the mathcomp algebra hierarchy rather than to the stdlib's
   `Stdlib.Numbers.NatInt.NZRing` machinery (which the ZArith import
   above otherwise clobbers). *)
From mathcomp.algebra_tactics Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ================================================================= *)
(*  Section 1 — integer reduction of v_witness                        *)
(* ================================================================= *)

Local Open Scope Z_scope.

(* Positive denominator: lcm of all `v_witness` denominators. *)
Definition v_den : Z :=
  List.fold_left (fun acc p => Z.lcm acc (snd p)) v_witness 1.

(* Scaled integer numerators: v_num[i] = num_i * (v_den / den_i). *)
Definition v_num : list Z :=
  List.map (fun p => fst p * (v_den / snd p)) v_witness.

(* ================================================================= *)
(*  Section 2 — integer quadratic forms                               *)
(* ================================================================= *)

(* Multiply a Z vector by a Z matrix (column on the right).
   `row_mul row v` = sum_i row[i] * v[i]. *)
Fixpoint row_dot (row v : list Z) : Z :=
  match row, v with
  | nil, _ => 0
  | _, nil => 0
  | r :: rs, x :: xs => r * x + row_dot rs xs
  end.

(* `mat_vec_mul M v` = M * v (column vector). *)
Definition mat_vec_mul (M : list (list Z)) (v : list Z) : list Z :=
  List.map (fun row => row_dot row v) M.

(* `quad M v` = v^T * M * v. *)
Definition quad (M : list (list Z)) (v : list Z) : Z :=
  row_dot v (mat_vec_mul M v).

Definition num_M1 : Z := quad M1_int v_num.
Definition num_M2 : Z := quad M2_int v_num.

(* ================================================================= *)
(*  Section 3 — integer inequalities (vm_compute Qeds)                *)
(* ================================================================= *)

Lemma v_den_pos : 0 < v_den.
Proof. vm_compute. reflexivity. Qed.

Lemma rayleigh_witness_M1_positive : 0 < num_M1.
Proof. vm_compute. reflexivity. Qed.

(* The headline integer inequality:
     105 * D_M1 * num_M2  >  4 * D_M2 * num_M1.
   Equivalent (after clearing denominators uniformly) to the strict
   Rayleigh-quotient bound  105 * v^T M2 v  >  4 * v^T M1 v. *)
Lemma rayleigh_witness_holds :
  4 * D_M2 * num_M1 < 105 * D_M1 * num_M2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(*  Section 4 — rat-level Rayleigh-quotient bound                     *)
(* ================================================================= *)

Local Open Scope ring_scope.

(* The rational entries of the witness vector v.  Identical to
   v_witness/v_den modulo Z2rat. *)
Definition v_rat (i : nat) : rat :=
  Z2rat (List.nth i v_num BinInt.Z0) / Z2rat v_den.

(* Rayleigh-quotient numerators, against the paper-form spec matrices
   M{1,2}_spec_ij.  These are bigop sums of 42*42 = 1764 rat-level
   terms.

   `quad_spec M_spec_ij` matches the standard Rayleigh-quotient
   numerator `v^T M v` where v is the rational vector
   `i |-> Z2rat v_num[i] / Z2rat v_den`. *)
Definition quad_spec (M_spec : nat -> nat -> rat) : rat :=
  \sum_(i < 42) \sum_(j < 42)
    v_rat i * M_spec i j * v_rat j.

Notation quad_M1_spec := (quad_spec M1_spec_ij) (only parsing).
Notation quad_M2_spec := (quad_spec M2_spec_ij) (only parsing).

(* ================================================================= *)
(*  Section 5 — Z->rat bridge for the Rayleigh-quotient sum           *)
(* ================================================================= *)

(* The integer quadratic form `quad M_int v_num` lifts to the
   rat-level `\sum_(i, j) Z2rat v_num[i] * Z2rat mat_get M_int i j *
   Z2rat v_num[j]` for any matrix M_int (whose 42x42 block is given
   as `mat_get`).  We prove this by structural induction on the
   bigop, working through the Fixpoint `dot`/`row_dot`/`mat_vec_mul`
   chain. *)

Lemma Z2rat_mul (a b : Z) : Z2rat (a * b) = Z2rat a * Z2rat b.
Proof. by rewrite /Z2rat Z_to_int_mul intrM. Qed.

Lemma Z2rat_add (a b : Z) : Z2rat (a + b) = Z2rat a + Z2rat b.
Proof. by rewrite /Z2rat Z_to_int_add intrD. Qed.

Lemma Z2rat_0 : Z2rat 0 = 0.
Proof. by rewrite /Z2rat Z_to_int_0. Qed.

(* `row_dot row v` lifted to rat = sum over indices. *)
Lemma Z2rat_row_dot_eq_sum (row v : list Z) (n : nat) :
  length v = n -> length row = n ->
  Z2rat (row_dot row v) =
  \sum_(i < n) Z2rat (List.nth i row BinInt.Z0)
             * Z2rat (List.nth i v BinInt.Z0).
Proof.
  elim: n row v => [|n IH] row v Hv Hr.
  - destruct row; destruct v; try discriminate.
    by rewrite /= Z2rat_0 big_ord0.
  - destruct row as [|r row']; [discriminate|].
    destruct v as [|x v']; [discriminate|].
    simpl in Hv, Hr.
    rewrite big_ord_recl /=.
    rewrite Z2rat_add Z2rat_mul.
    congr (_ + _).
    rewrite (IH row' v');
      [by apply: eq_bigr => i _ | by inversion Hv | by inversion Hr].
Qed.

(* For any well-formed 42x42 matrix M, the integer `quad M v_num`
   lifts to the bigop `\sum_(i<42) \sum_(j<42) v_num[i] * M[i][j] *
   v_num[j]` (all factors taken via Z2rat).

   The hypotheses precisely characterise the rayleigh-branch input shape:
   v_num has length 42, M has 42 rows, every row of M has length 42. *)
Section QuadBridge.

Variable M : list (list Z).
Hypothesis HM_rows : length M = 42%nat.
Hypothesis HM_cols : forall i, (i < 42)%nat ->
  length (List.nth i M nil) = 42%nat.
Hypothesis Hv_len : length v_num = 42%nat.

Lemma Z2rat_quad_eq_sum :
  Z2rat (quad M v_num) =
  \sum_(i < 42) \sum_(j < 42)
    Z2rat (List.nth i v_num BinInt.Z0) *
    Z2rat (mat_get M (nat_of_ord i) (nat_of_ord j)) *
    Z2rat (List.nth j v_num BinInt.Z0).
Proof.
  rewrite /quad.
  (* `mat_vec_mul M v_num = map (fun row => row_dot row v_num) M`
     so `dot v_num (mat_vec_mul M v_num)` = `\sum_(i<42) v_num[i] *
     row_dot M[i] v_num` = `\sum_(i<42) v_num[i] * \sum_(j<42) M[i][j]
     * v_num[j]`. *)
  pose Mvec := mat_vec_mul M v_num.
  have HMvec_len : length Mvec = 42%nat.
  { by rewrite /Mvec /mat_vec_mul List.length_map. }
  rewrite (Z2rat_row_dot_eq_sum (n := 42) HMvec_len Hv_len).
  apply: eq_bigr => i _.
  rewrite /Mvec /mat_vec_mul.
  have Hr_len : length (List.nth (nat_of_ord i) M nil) = 42%nat.
  { apply: HM_cols. exact: (ltn_ord i). }
  have Hnth_map :
       List.nth i (List.map (fun row => row_dot row v_num) M) BinInt.Z0
     = row_dot (List.nth i M nil) v_num.
  { rewrite (List.nth_indep _ BinInt.Z0 (row_dot nil v_num)); last by
      rewrite List.length_map HM_rows; apply/ltP; exact: (ltn_ord i).
    by rewrite (List.map_nth (fun row => row_dot row v_num) M nil i). }
  rewrite Hnth_map.
  rewrite (Z2rat_row_dot_eq_sum (n := 42) Hv_len Hr_len).
  rewrite GRing.mulr_sumr.
  apply: eq_bigr => j _.
  rewrite /mat_get /nth_Z.
  by rewrite GRing.mulrA.
Qed.

End QuadBridge.

(* ================================================================= *)
(*  Section 6 — well-formedness of M1_int, M2_int, v_num              *)
(* ================================================================= *)

Lemma M1_int_rows : length M1_int = 42%nat.
Proof. by vm_compute. Qed.

Lemma M2_int_rows : length M2_int = 42%nat.
Proof. by vm_compute. Qed.

Lemma M1_int_cols : forall i, (i < 42)%nat ->
  length (List.nth i M1_int nil) = 42%nat.
Proof.
  move=> i Hi.
  have Hall : forallb (fun row => Nat.eqb (length row) 42) M1_int = true
    by vm_compute.
  have Hin : List.In (List.nth i M1_int nil) M1_int.
  { apply: List.nth_In; rewrite M1_int_rows; apply/ltP; exact: Hi. }
  move: Hall; rewrite List.forallb_forall => /(_ _ Hin) /Nat.eqb_eq //.
Qed.

Lemma M2_int_cols : forall i, (i < 42)%nat ->
  length (List.nth i M2_int nil) = 42%nat.
Proof.
  move=> i Hi.
  have Hall : forallb (fun row => Nat.eqb (length row) 42) M2_int = true
    by vm_compute.
  have Hin : List.In (List.nth i M2_int nil) M2_int.
  { apply: List.nth_In; rewrite M2_int_rows; apply/ltP; exact: Hi. }
  move: Hall; rewrite List.forallb_forall => /(_ _ Hin) /Nat.eqb_eq //.
Qed.

Lemma v_num_length : length v_num = 42%nat.
Proof. by vm_compute. Qed.

Lemma v_den_neq0_rat : Z2rat v_den != 0.
Proof. by apply: Z_to_int_pos_rat_neq0; exact: v_den_pos. Qed.

(* ================================================================= *)
(*  Section 7 — Rayleigh-quotient identity for M_spec                 *)
(* ================================================================= *)

(* Abstract per-cell algebraic identity, Qed-sealed to keep the heavy
   `field` proof OUT of the per-cell goal inside the bigop of
   quad_spec_eq_Z (which OOMs the kernel when the field-tactic's
   proof term is unfolded under 42*42 nested binders). *)
Lemma quad_cell_identity (dm vd vi mij vj : rat) :
  vd != 0 -> dm != 0 ->
  dm * vd^+2 * (vi / vd * (mij / dm) * (vj / vd)) = vi * mij * vj.
Proof. by move=> Hvd Hdm; rewrite expr2; field; apply/andP. Qed.

(* The full Rayleigh-quotient sum on M_spec_ij decomposes through the
   spec=Z bridge. *)
Lemma quad_spec_eq_Z (M_spec : nat -> nat -> rat) (M_int : list (list Z))
                     (D_M : Z)
                     (HM_rows  : length M_int = 42%nat)
                     (HM_cols  : forall i, (i < 42)%nat ->
                                  length (List.nth i M_int nil) = 42%nat)
                     (HD_M_pos : Z.lt 0 D_M)
                     (Hbridge  : forall i j, (i < 42)%nat -> (j < 42)%nat ->
                                  M_spec i j = Z2rat (mat_get M_int i j) /
                                               Z2rat D_M) :
  Z2rat D_M * Z2rat v_den ^+ 2 * quad_spec M_spec =
  Z2rat (quad M_int v_num).
Proof.
  (* The natural proof — `rewrite !mulr_sumr` then `field` on each
     of the 42*42 cells — OOMs the kernel: the unfolded `field` proof
     term is duplicated under each `eq_bigr` binder, blowing past the
     16 GB cgroup limit.

     The fix follows quad's AbstractPencilHelper pattern: factor the
     per-cell algebraic identity (Section 7's `quad_cell_identity`,
     already Qed-sealed) so the bigop walk references it by NAME
     instead of inlining a fresh `field` proof term per cell.  We
     also constrain the `mulr_sumr` rewrite to [LHS] to keep
     unification cheap. *)
  rewrite (Z2rat_quad_eq_sum HM_rows HM_cols v_num_length).
  rewrite /quad_spec.
  rewrite [LHS]mulr_sumr.
  apply: eq_bigr => i _.
  rewrite [LHS]mulr_sumr.
  apply: eq_bigr => j _.
  rewrite (Hbridge i j (ltn_ord i) (ltn_ord j)) /v_rat.
  apply: quad_cell_identity.
  - exact: v_den_neq0_rat.
  - by apply: Z_to_int_pos_rat_neq0; exact: HD_M_pos.
Qed.

(* Specialised to M1, M2 with the explicit spec=Z bridge. *)
Lemma quad_M1_spec_eq_Z :
  Z2rat D_M1 * Z2rat v_den ^+ 2 * quad_spec M1_spec_ij =
  Z2rat num_M1.
Proof.
  apply: quad_spec_eq_Z;
    [exact: M1_int_rows | exact: M1_int_cols
     | exact: D_M1_pos | exact: @M1_spec_eq_int].
Qed.

Lemma quad_M2_spec_eq_Z :
  Z2rat D_M2 * Z2rat v_den ^+ 2 * quad_spec M2_spec_ij =
  Z2rat num_M2.
Proof.
  apply: quad_spec_eq_Z;
    [exact: M2_int_rows | exact: M2_int_cols
     | exact: D_M2_pos | exact: @M2_spec_eq_int].
Qed.

(* ================================================================= *)
(*  Section 8 — strict Rayleigh-quotient bound at v_witness           *)
(* ================================================================= *)

(* Z2rat is positive on positive Z. *)
Lemma Z2rat_pos (a : Z) : BinInt.Z.lt 0 a -> (0 : rat) < Z2rat a.
Proof.
  case: a => [//|p _|p Hp]; last by lia.
  by rewrite /Z2rat Z_to_int_pos_pos ltr0z; apply/ltP; exact: Pos2Nat.is_pos.
Qed.

Lemma Z2rat_lt (a b : Z) : BinInt.Z.lt a b -> Z2rat a < Z2rat b.
Proof.
  move=> Hab; rewrite -subr_gt0.
  have -> : Z2rat b - Z2rat a = Z2rat (BinInt.Z.sub b a).
    rewrite /Z2rat -intrB -Z_to_int_opp -Z_to_int_add.
    by congr ((Z_to_int _)%:~R); lia.
  by apply: Z2rat_pos; lia.
Qed.

Lemma rayleigh_witness_holds_rat :
  Z2rat (4 * D_M2 * num_M1) < Z2rat (105 * D_M1 * num_M2).
Proof. by apply: Z2rat_lt; exact: rayleigh_witness_holds. Qed.

(* Generic Rayleigh-quotient lift: from two scaled-quad identities
   `Z2rat d_k * v^2 * q_k = Z2rat a_k` (k = 1, 2) and the integer
   inequality `4*d2*a1 < 105*d1*a2`, deduce `4*q1 < 105*q2`.

   This is the AbstractPencilHelper trick from the quad branch: we
   abstract over `q1`, `q2`, `v`, the denominators, and the
   numerators, so the heavy `ring` calls inside operate on tiny
   abstract scalars instead of the concrete `quad_spec M{1,2}_spec_ij`
   bigops.  The proof term stays small enough for kernel verification
   (avoiding the 16 GB OOM that hit the inline `field`/`ring`
   variant). *)
Section RayleighLift.

Variables (d1Z d2Z a1Z a2Z : Z) (v q1 q2 : rat).
Hypothesis Hd1  : BinInt.Z.lt 0 d1Z.
Hypothesis Hd2  : BinInt.Z.lt 0 d2Z.
Hypothesis Hv   : (0 : rat) < v.
Hypothesis Ha1  : Z2rat d1Z * v ^+ 2 * q1 = Z2rat a1Z.
Hypothesis Ha2  : Z2rat d2Z * v ^+ 2 * q2 = Z2rat a2Z.
Hypothesis Hcmp : Z2rat (4 * d2Z * a1Z) < Z2rat (105 * d1Z * a2Z).

Lemma rayleigh_lift_generic : 4%:Q * q1 < 105%:Q * q2.
Proof.
  have Hd1r : (0 : rat) < Z2rat d1Z by exact: Z2rat_pos.
  have Hd2r : (0 : rat) < Z2rat d2Z by exact: Z2rat_pos.
  have HK   : (0 : rat) < Z2rat d1Z * Z2rat d2Z * v ^+ 2.
    by rewrite expr2; do !apply: mulr_gt0.
  rewrite -(ltr_pM2r HK).
  have H4   : Z2rat 4   = 4%:Q   by rewrite /Z2rat /=.
  have H105 : Z2rat 105 = 105%:Q by rewrite /Z2rat /=.
  have HLHS : 4%:Q * q1 * (Z2rat d1Z * Z2rat d2Z * v ^+ 2)
            = Z2rat (4 * d2Z * a1Z).
    by rewrite !Z2rat_mul -Ha1 H4; ring.
  have HRHS : 105%:Q * q2 * (Z2rat d1Z * Z2rat d2Z * v ^+ 2)
            = Z2rat (105 * d1Z * a2Z).
    by rewrite !Z2rat_mul -Ha2 H105; ring.
  by rewrite HLHS HRHS; exact: Hcmp.
Qed.

End RayleighLift.

(* The headline rat-level Rayleigh-quotient inequality:
       4 * v^T M1 v  <  105 * v^T M2 v
   on the paper-form spec matrices. *)
Lemma rayleigh_lt_main : 4%:Q * quad_spec M1_spec_ij <
                         105%:Q * quad_spec M2_spec_ij.
Proof.
  exact: (rayleigh_lift_generic D_M1_pos D_M2_pos
                                (Z2rat_pos v_den_pos)
                                quad_M1_spec_eq_Z quad_M2_spec_eq_Z
                                rayleigh_witness_holds_rat).
Qed.

(* ================================================================= *)
(*  Section 9 — headline theorem                                      *)
(* ================================================================= *)

(* The rayleigh-branch headline:

     1. The FLINT-shipped (M1_int, M2_int, D_M1, D_M2) matches the
        paper-form Maynard spec entry-wise.

     2. At the shipped witness v (= v_witness, lifted to a rat vector
        via v_rat), the strict Rayleigh-quotient bound
        4 * v^T M1 v < 105 * v^T M2 v holds on the paper-form spec.

   Modulo Maynard's Lemma 8.3 (M_k = k * sup_F J_k(F)/I_k(F),
   paper-side), conclusion (2) entails M_{105} > 4: Lemma 8.3 says
   M_{105} is 105 times the sup of the Rayleigh quotient over an
   admissible function space, and the sup is at least any individual
   quotient.  Lemma 8.3 is NOT formalised here; see AUDITOR_CHECKLIST.md. *)
Theorem maynard_M105_certified_rayleigh :
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M1_spec_ij i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1) /\
  (forall i j, (i < 42)%nat -> (j < 42)%nat ->
     M2_spec_ij i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2) /\
  4%:Q * quad_spec M1_spec_ij < 105%:Q * quad_spec M2_spec_ij.
Proof.
  split; first by move=> i j Hi Hj; apply: M1_spec_eq_int.
  split; first by move=> i j Hi Hj; apply: M2_spec_eq_int.
  exact: rayleigh_lt_main.
Qed.

