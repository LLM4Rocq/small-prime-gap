(**md**************************************************************************)
(* # M1PosDef                                                                *)
(*                                                                           *)
(* Axiom-free positive-definiteness of the 42x42 rational witness matrix     *)
(* `M1_rat = M1_int / D_M1`, delivered as a complex congruence factorisation *)
(* over `C := algC`.                                                         *)
(*                                                                           *)
(* Route (all over the COMPLEX spectral theorem of mathcomp 2.5.0; no        *)
(* dependence on the real spectral theorem / PR #1611):                      *)
(*                                                                           *)
(*  1. `Mz_C := map_mx ratr (mat_int_to_rat M1_int 1 42)` is hermitian       *)
(*     (`M1_int` is symmetric and rationals are conj-fixed).                 *)
(*  2. `char_poly Mz_C = map_poly ratr (pol_to_polyrat (char_poly_int        *)
(*     M1_int))`, whose integer coefficients are `cp_M1_value`, which         *)
(*     strictly alternates in sign (`M1CharPoly`).                            *)
(*  3. KEY: a monic poly over `algC` whose coefficients are integers with    *)
(*     strictly-alternating signs (positive constant) is strictly positive   *)
(*     at every real `x <= 0`; hence every real root is `> 0`.               *)
(*  4. Spectral decomposition: every `spectral_diag` entry is a real         *)
(*     eigenvalue, hence a root of `char_poly Mz_C`, hence `> 0`.            *)
(*  5. `Rfac := diag_mx (sqrtC of the spectrum) *m spectralmx Mz_C` is a     *)
(*     unitary-scaled congruence factor: `Rfac^t* *m Rfac = Mz_C`.          *)
(*  6. Transfer the `1/D_M1` scaling (over `Q`, no `algC` division):         *)
(*                                                                           *)
(* ```                                                                       *)
(*   M1_rat_factor : exists R : 'M[algC]_42,                                  *)
(*       (R \in unitmx) /\ (R^t* *m R = map_mx ratr M1_rat).                  *)
(* ```                                                                       *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra all_field.
From mathcomp Require Import spectral.
From PrimeGapS1 Require Import IntMat CharPoly Witness WitnessM1CharPoly.
From PrimeGapS1 Require Import EigenBridge SpectralCrux M1CharPoly.

(* Stdlib is imported AFTER mathcomp so that the `%Z` / `%N` delimiters and
   the unqualified `nth` / `map` resolve to the Stdlib (Z_scope / List)
   meanings used below; mathcomp's int_scope also claims `%Z`. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* ================================================================== *)
(* Section 0: sign-preservation of the Z -> int embedding              *)
(* ================================================================== *)

Lemma Zti_pos (z : Z) : (0 < z)%Z -> (0 < Z_to_int z)%R.
Proof.
case: z => [|p|p] // _.
rewrite Z_to_int_pos_pos.
have := Pos2Nat.is_pos p.
by move=> /ltP.
Qed.

Lemma Zti_neg (z : Z) : (z < 0)%Z -> (Z_to_int z < 0)%R.
Proof. by case: z => [|p|p] // _. Qed.

(* ================================================================== *)
(* Section 1: the matrices MZ (integer) and Mz_C (over algC)           *)
(* ================================================================== *)

Local Notation C := algC.

Definition MZ : 'M[rat]_42 := mat_int_to_rat M1_int 1 42.
Definition Mz_C : 'M[C]_42 := map_mx (ratr : rat -> C) MZ.

(* M1_int is symmetric, checked entrywise over Z by vm_compute. *)
Definition M1_sym_check : bool :=
  List.forallb (fun i => List.forallb (fun j =>
     Z.eqb (mat_get M1_int i j) (mat_get M1_int j i)) (List.seq 0 42))
     (List.seq 0 42).

Lemma M1_sym_checkE : M1_sym_check = true.
Proof. by vm_compute. Qed.

Lemma M1_get_sym (i j : 'I_42) :
  mat_get M1_int (nat_of_ord i) (nat_of_ord j)
  = mat_get M1_int (nat_of_ord j) (nat_of_ord i).
Proof.
apply/Z.eqb_eq.
move: M1_sym_checkE; rewrite /M1_sym_check => /forallb_forall H.
have Hi := ltn_ord i; have Hj := ltn_ord j.
move/ltP in Hi; move/ltP in Hj.
have Ii : In (nat_of_ord i) (List.seq 0 42) by apply/in_seq; lia.
have Ij : In (nat_of_ord j) (List.seq 0 42) by apply/in_seq; lia.
move: (H (nat_of_ord i) Ii) => /forallb_forall Hrow.
exact: (Hrow (nat_of_ord j) Ij).
Qed.

Lemma MZ_sym : trmx MZ = MZ.
Proof. by apply/matrixP => i j; rewrite !mxE (M1_get_sym i j). Qed.

Lemma Mz_C_real : Mz_C \is a mxOver Num.real.
Proof.
apply/mxOverP => i j.
rewrite mxE.
exact: (Creal_Crat (Crat_rat _)).
Qed.

Lemma Mz_C_sym : Mz_C \is symmetricmx.
Proof.
apply/is_hermitianmxP.
rewrite expr0 scale1r.
by apply/matrixP => i j; rewrite !mxE (M1_get_sym i j).
Qed.

Lemma Mz_C_herm : Mz_C \is hermsymmx.
Proof. exact: (realsym_hermsym Mz_C_sym Mz_C_real). Qed.

(* ================================================================== *)
(* Section 2: char_poly Mz_C and its integer coefficients             *)
(* ================================================================== *)

Lemma M1_dim : mat_dim M1_int = 42%nat.
Proof. by vm_compute. Qed.

Lemma M1_wf : forall i, (i < List.length M1_int)%coq_nat ->
  List.length (List.nth i M1_int nil) = 42%nat.
Proof.
move=> i Hi.
have Hb : List.forallb (fun r => Nat.eqb (List.length r) 42) M1_int = true
  by vm_compute.
apply/Nat.eqb_eq.
apply: (proj1 (forallb_forall _ _) Hb).
by apply: nth_In; exact: Hi.
Qed.

Lemma cp_Mz :
  char_poly Mz_C
  = map_poly (ratr : rat -> C) (pol_to_polyrat (char_poly_int M1_int)).
Proof.
rewrite (char_poly_int_correct M1_dim M1_wf).
by rewrite map_char_poly.
Qed.

Lemma seqnth_listmap (l : list Z) (i : nat) :
  seq.nth 0 (List.map (fun z => (Z_to_int z)%:~R : rat) l) i
  = ((Z_to_int (List.nth i l 0%Z))%:~R : rat).
Proof.
elim: l i => [|z l IH] i.
- by rewrite nth_nil; case: i => [|i] /=.
- by case: i => [|i] //=.
Qed.

Lemma cpC_coef (i : nat) :
  (char_poly Mz_C)`_i = ((Z_to_int (List.nth i cp_M1_value 0%Z))%:~R : C).
Proof.
rewrite cp_Mz coef_map char_poly_int_M1_eq /pol_to_polyrat coef_Poly.
rewrite seqnth_listmap.
exact: ratr_int.
Qed.

(* ================================================================== *)
(* Section 3: the integer sign machinery from `cp_M1_alternates`       *)
(* ================================================================== *)

Lemma alt_signs_adj : forall (k : nat) (l : list Z),
  alternating_signs l = true -> (S k < List.length l)%coq_nat ->
  (List.nth k l 0 * List.nth (S k) l 0 < 0)%Z.
Proof.
elim => [|k IH] l Halt Hlen.
- destruct l as [|x [|y l']]; simpl in Hlen; try lia.
  simpl in Halt. move/andP: Halt => [H1 _].
  by simpl; apply/Z.ltb_lt; exact: H1.
- destruct l as [|x l']; simpl in Hlen; try lia.
  destruct l' as [|y l'']; simpl in Hlen; try lia.
  simpl in Halt. move/andP: Halt => [_ H2].
  apply: (IH (y :: l'')).
  + exact: H2.
  + simpl in Hlen |- *. lia.
Qed.

Lemma signsq (k : nat) : ((-1 : int) ^+ k * (-1) ^+ k = 1)%R.
Proof.
rewrite -exprMn_comm; last exact: mulrC.
by rewrite mulrNN mul1r expr1n.
Qed.

Lemma sgnprod (k : nat) : ((-1 : int) ^+ k * (-1) ^+ (S k) = -1)%R.
Proof. by rewrite exprS mulrCA signsq mulr1. Qed.

Lemma zc0_pos : (0 < Z_to_int (List.nth 0 cp_M1_value 0%Z))%R.
Proof. by apply: Zti_pos; exact: (proj1 (proj2 cp_M1_alternates)). Qed.

Lemma zc_sign (k : nat) :
  (k < List.length cp_M1_value)%coq_nat ->
  (0 < Z_to_int (List.nth k cp_M1_value 0%Z) * (-1) ^+ k)%R.
Proof.
elim: k => [|k IH] Hk.
- by rewrite expr0 mulr1; exact: zc0_pos.
- have IH' : (0 < Z_to_int (List.nth k cp_M1_value 0%Z) * (-1) ^+ k)%R
    by apply: IH; lia.
  have Hadj : (Z_to_int (List.nth k cp_M1_value 0%Z)
               * Z_to_int (List.nth (S k) cp_M1_value 0%Z) < 0)%R.
    rewrite -Z_to_int_mul; apply: Zti_neg.
    by apply: (alt_signs_adj k cp_M1_value (proj1 cp_M1_alternates)); exact: Hk.
  by rewrite -(pmulr_rgt0 _ IH') mulrACA sgnprod mulrN1 oppr_gt0; exact: Hadj.
Qed.

Lemma zc_nonneg (k : nat) :
  (0 <= Z_to_int (List.nth k cp_M1_value 0%Z) * (-1) ^+ k)%R.
Proof.
case: (Nat.lt_ge_cases k (List.length cp_M1_value)) => Hk.
- by apply: Order.POrderTheory.ltW; apply: zc_sign.
- have -> : List.nth k cp_M1_value 0%Z = 0%Z by apply: List.nth_overflow; lia.
  by rewrite Z_to_int_0 mul0r.
Qed.

(* ================================================================== *)
(* Section 4: the KEY positivity-of-roots lemma                        *)
(* ================================================================== *)

Lemma cp_pos_on_nonpos (x : C) :
  x \is Num.real -> x <= 0 -> 0 < (char_poly Mz_C).[x].
Proof.
move=> _ xle0.
have term_ge : forall i : nat, 0 <= (char_poly Mz_C)`_i * x ^+ i.
  move=> i.
  rewrite cpC_coef.
  have xE : x = (-1) * (- x) by rewrite mulN1r opprK.
  rewrite xE exprMn_comm; last exact: mulrC.
  rewrite mulrA -intr_sign -intrM.
  apply: mulr_ge0.
    by rewrite ler0z; exact: zc_nonneg.
  by apply: exprn_ge0; rewrite oppr_ge0.
have F0pos : 0 < (char_poly Mz_C)`_0 * x ^+ 0.
  by rewrite expr0 mulr1 cpC_coef ltr0z; exact: zc0_pos.
rewrite horner_coef size_char_poly big_ord_recl.
apply: (Order.POrderTheory.lt_le_trans F0pos).
have -> : (char_poly Mz_C)`_ord0 * x ^+ ord0
        = (char_poly Mz_C)`_0 * x ^+ 0 by [].
rewrite lerDl.
by apply: sumr_ge0 => i _; exact: term_ge.
Qed.

Lemma cp_root_pos (a : C) :
  a \is Num.real -> root (char_poly Mz_C) a -> 0 < a.
Proof.
move=> areal Hroot.
have h0 := real0 algC.
case: (boolP (0 < a)) => // Hna.
have ale0 : a <= 0 by rewrite (real_leNgt areal h0).
move: Hroot; rewrite rootE => /eqP H0.
have := cp_pos_on_nonpos a areal ale0.
by rewrite H0 Order.POrderTheory.ltxx.
Qed.

(* ================================================================== *)
(* Section 5: the spectrum of Mz_C is strictly positive                *)
(* ================================================================== *)

Lemma spd_pos (i : 'I_42) : 0 < spectral_diag Mz_C 0 i.
Proof.
have Punit : spectralmx Mz_C \in unitmx := spectral_unit Mz_C.
have AE : Mz_C = invmx (spectralmx Mz_C) *m diag_mx (spectral_diag Mz_C)
                  *m spectralmx Mz_C
  by apply/orthomx_spectralP; exact: (hermitian_normalmx Mz_C_herm).
have spr : forall a b, spectral_diag Mz_C a b \is Num.real
  by apply/mxOverP; apply: hermitian_spectral_diag_real Mz_C_herm.
apply: cp_root_pos; first exact: spr.
rewrite -eigenvalue_root_char.
have E := eig_transfer (spectral_diag Mz_C) i Punit.
rewrite -AE in E.
exact: E.
Qed.

(* ================================================================== *)
(* Section 6: the complex congruence factor of Mz_C                    *)
(* ================================================================== *)

Definition dvec : 'rV[C]_42 := \row_i sqrtC (spectral_diag Mz_C 0 i).
Definition Rfac : 'M[C]_42 := diag_mx dvec *m spectralmx Mz_C.

Lemma dvec_pos (i : 'I_42) : 0 < dvec 0 i.
Proof. by rewrite mxE sqrtC_gt0; exact: spd_pos. Qed.

Lemma diag_sq : diag_mx dvec *m diag_mx dvec = diag_mx (spectral_diag Mz_C).
Proof.
apply/matrixP => i j.
rewrite mul_diag_mx !mxE mulrnAr.
congr (_ *+ _).
by rewrite -expr2 sqrtCK.
Qed.

Lemma diag_tC : ((diag_mx dvec) ^t*)%sesqui = diag_mx dvec.
Proof.
apply/matrixP => i j.
rewrite !mxE.
case: (eqVneq i j) => [->|ne].
- rewrite conj_Creal //.
  rewrite rpredMn // sqrtC_real //.
  apply: Order.POrderTheory.ltW; exact: spd_pos.
- by rewrite !mulr0n rmorph0.
Qed.

Lemma Rfac_unit : Rfac \in unitmx.
Proof.
rewrite /Rfac unitmx_mul.
apply/andP; split; last exact: spectral_unit.
rewrite unitmxE det_diag unitfE.
apply: lt0r_neq0.
by apply: prodr_gt0 => i _; exact: dvec_pos.
Qed.

Lemma Rfac_factor : ((Rfac ^t*)%sesqui *m Rfac) = Mz_C.
Proof.
have Puni : spectralmx Mz_C \is unitarymx := spectral_unitarymx Mz_C.
have AE : Mz_C = invmx (spectralmx Mz_C) *m diag_mx (spectral_diag Mz_C)
                  *m spectralmx Mz_C
  by apply/orthomx_spectralP; exact: (hermitian_normalmx Mz_C_herm).
rewrite [X in _ = X]AE (invmx_unitary Puni).
rewrite /Rfac trmxC_mul diag_tC.
by rewrite mulmxA -[X in X *m _]mulmxA diag_sq.
Qed.

(* ================================================================== *)
(* Section 7: transfer the 1/D_M1 scaling and deliver the factor       *)
(* ================================================================== *)

Lemma D_M1_posZ : (0 < D_M1)%Z.
Proof. by vm_compute. Qed.

Lemma map_ratr_scale (a : rat) (A : 'M[rat]_42) :
  map_mx (ratr : rat -> C) (a *: A) = ratr a *: map_mx ratr A.
Proof. by apply/matrixP => i j; rewrite !mxE rmorphM. Qed.

(* The denominator factors out of `mat_int_to_rat`.  Proved GENERICALLY in   *)
(* `M`, `D`, `n` so the entrywise `mxE` runs on abstract symbols and never    *)
(* forces `Z_to_int D_M1` (whose `Pos.to_nat` would be ~10^200 in unary).     *)
Lemma mat_int_to_rat_den (M : mat) (D : Z) (n : nat) :
  mat_int_to_rat M D n = ((Z_to_int D)%:~R : rat)^-1 *: mat_int_to_rat M 1 n.
Proof.
apply/matrixP => i j.
rewrite !mxE Z_to_int_1_rat divr1.
by rewrite mulrC.
Qed.

Lemma M1rat_eq : M1_rat = ((Z_to_int D_M1)%:~R : rat)^-1 *: MZ.
Proof. by rewrite /M1_rat /MZ mat_int_to_rat_den. Qed.

(* Over Q (no algC division): D_M1 * M1_rat = MZ. *)
Lemma MZ_scaled : ((Z_to_int D_M1)%:~R : rat) *: M1_rat = MZ.
Proof.
have dn0 : ((Z_to_int D_M1)%:~R : rat) != 0.
  by rewrite intr_eq0; apply: lt0r_neq0; apply: Zti_pos; exact: D_M1_posZ.
by rewrite M1rat_eq scalerA (mulfV dn0) scale1r.
Qed.

Lemma map_M1rat_scale :
  map_mx (ratr : rat -> C) M1_rat = ((Z_to_int D_M1)%:~R : C)^-1 *: Mz_C.
Proof.
have dn0 : ((Z_to_int D_M1)%:~R : C) != 0.
  by rewrite intr_eq0; apply: lt0r_neq0; apply: Zti_pos; exact: D_M1_posZ.
have key : ((Z_to_int D_M1)%:~R : C) *: map_mx ratr M1_rat = Mz_C.
  by rewrite -ratr_int -map_ratr_scale MZ_scaled.
(* Close with `reflexivity`, NOT `by []`: `done` normalises                  *)
(* `map_mx ratr M1_rat`, forcing `Pos.to_nat D_M1` (~10^200 in unary).        *)
rewrite -key scalerA (mulVf dn0) scale1r.
reflexivity.
Qed.

Lemma scaleC_tC (a : C) (A : 'M[C]_42) :
  ((a *: A) ^t*)%sesqui = a^* *: (A ^t*)%sesqui.
Proof. by apply/matrixP => i j; rewrite !mxE rmorphM. Qed.

Theorem M1_rat_factor :
  exists R : 'M[C]_42, (R \in unitmx) /\
    ((R ^t*)%sesqui *m R = map_mx (ratr : rat -> C) M1_rat).
Proof.
have dpos : 0 < ((Z_to_int D_M1)%:~R : C).
  by rewrite ltr0z; apply: Zti_pos; exact: D_M1_posZ.
set s := sqrtC (((Z_to_int D_M1)%:~R : C)^-1).
have spos : 0 < s by rewrite /s sqrtC_gt0 invr_gt0.
have sreal : s \is Num.real by apply: ger0_real; apply: Order.POrderTheory.ltW.
have sE : s * s = ((Z_to_int D_M1)%:~R : C)^-1.
  rewrite /s -expr2.
  exact: sqrtCK.
exists (s *: Rfac); split.
- rewrite unitmxE detZ unitfE.
  apply: mulf_neq0.
    by apply: expf_neq0; apply: lt0r_neq0.
  by move: Rfac_unit; rewrite unitmxE unitfE.
- rewrite scaleC_tC (conj_Creal sreal).
  rewrite -scalemxAl -scalemxAr scalerA Rfac_factor sE.
  (* `reflexivity`, NOT `by []`: avoid `done` forcing `Pos.to_nat D_M1`. *)
  rewrite map_M1rat_scale.
  reflexivity.
Qed.
