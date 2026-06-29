(**md**************************************************************************)
(* # MaynardEigen                                                            *)
(*                                                                           *)
(* The spectral bridge and the headline theorem for the eigenvalue route to  *)
(* `M_{105} > 4`, over `C := algC`.  Let `ratrM := map_mx (ratr : rat -> C)`.*)
(*                                                                           *)
(* ```                                                                       *)
(*   maynard_M105_certified :                                                *)
(*     matches_closed_forms M105 /\                                          *)
(*     exists lam : algC, eigenvalue (ratrM M105) lam /\ (4 < lam).          *)
(* ```                                                                       *)
(*                                                                           *)
(* Route.  `M1PosDef.M1_rat_factor` gives a complex congruence factor `R`    *)
(* (`R \in unitmx`, `R^t* *m R = ratrM M1_rat`).  Writing                     *)
(* `Sc := ratrM (105 *: M2_rat - 4 *: M1_rat)` (Hermitian, since `M1_rat`,    *)
(* `M2_rat` are real symmetric) and `S2 := (invmx R)^t* *m Sc *m invmx R`,    *)
(* `S2` is Hermitian (congruence) and is similar to                          *)
(* `invmx (ratrM M1_rat) *m Sc = ratrM M105 - 4 *: 1%:M`.  The Rayleigh      *)
(* witness `w := (R *m ratrM v)^t*` makes the Hermitian form of `S2`         *)
(* positive (it collapses to `ratr` of the rat-level Rayleigh numerator,     *)
(* `> 0` by `CertRayleigh.rayleigh_lt_main`).  `SpectralCrux.herm_crux`       *)
(* then yields a positive eigenvalue `a` of `S2`; transferring along the      *)
(* similarity and shifting by `4` gives the eigenvalue `a + 4 > 4` of         *)
(* `ratrM M105`.                                                              *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp Require Import spectral.
From PrimeGapS1 Require Import IntMat CharPoly Witness.
From PrimeGapS1 Require Import MaynardSpec MaynardSpecBridge Cert.
From PrimeGapS1 Require Import CertRayleigh EigenBridge SpectralCrux M1PosDef.

(* Stdlib is imported AFTER mathcomp so the `%Z` delimiter and the
   unqualified `nth` / `map` resolve to the Stdlib meanings used in the
   `vm_compute` symmetry check below; `Local Open Scope ring_scope` is
   re-asserted last so ring-scope numerals dominate. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
From mathcomp.algebra_tactics Require Import ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Local Notation C := algC.
Local Notation ratrM := (map_mx (ratr : rat -> C)).

(* ================================================================== *)
(* Section 1: symmetry of the integer / rational witness matrices      *)
(* ================================================================== *)

(* `M2_int` is symmetric, checked entrywise over Z by `vm_compute`.       *)
Definition M2_sym_check : bool :=
  List.forallb (fun i => List.forallb (fun j =>
     Z.eqb (mat_get M2_int i j) (mat_get M2_int j i)) (List.seq 0 42))
     (List.seq 0 42).

Lemma M2_sym_checkE : M2_sym_check = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_get_sym (i j : 'I_42) :
  mat_get M2_int (nat_of_ord i) (nat_of_ord j)
  = mat_get M2_int (nat_of_ord j) (nat_of_ord i).
Proof.
apply/Z.eqb_eq.
move: M2_sym_checkE; rewrite /M2_sym_check => /forallb_forall H.
have Hi := ltn_ord i; have Hj := ltn_ord j.
move/ltP in Hi; move/ltP in Hj.
have Ii : In (nat_of_ord i) (List.seq 0 42) by apply/in_seq; lia.
have Ij : In (nat_of_ord j) (List.seq 0 42) by apply/in_seq; lia.
move: (H (nat_of_ord i) Ii) => /forallb_forall Hrow.
exact: (Hrow (nat_of_ord j) Ij).
Qed.

Lemma M1_rat_sym : trmx M1_rat = M1_rat.
Proof. by apply/matrixP => i j; rewrite !mxE (M1_get_sym i j). Qed.

Lemma M2_rat_sym : trmx M2_rat = M2_rat.
Proof. by apply/matrixP => i j; rewrite !mxE (M2_get_sym i j). Qed.

(* ================================================================== *)
(* Section 2: the rat-level pencil `Srat` and its image `Sc` over C     *)
(* ================================================================== *)

Local Definition vr : 'cV[rat]_42 := \col_i v_rat i.
Local Definition Srat : 'M[rat]_42 := 105%:Q *: M2_rat - 4%:Q *: M1_rat.
Local Definition Sc : 'M[C]_42 := ratrM Srat.

Lemma M1_ratE (i j : 'I_42) :
  M1_rat i j = Z2rat (mat_get M1_int i j) / Z2rat D_M1.
Proof. by rewrite /M1_rat mxE /Z2rat. Qed.

Lemma M2_ratE (i j : 'I_42) :
  M2_rat i j = Z2rat (mat_get M2_int i j) / Z2rat D_M2.
Proof. by rewrite /M2_rat mxE /Z2rat. Qed.

Lemma M1_rat_spec (i j : 'I_42) : M1_rat i j = M1_spec_ij i j.
Proof. by rewrite M1_ratE (M1_spec_eq_int (ltn_ord i) (ltn_ord j)). Qed.

Lemma M2_rat_spec (i j : 'I_42) : M2_rat i j = M2_spec_ij i j.
Proof. by rewrite M2_ratE (M2_spec_eq_int (ltn_ord i) (ltn_ord j)). Qed.

Lemma Sc_real : Sc \is a mxOver Num.real.
Proof. apply/mxOverP => i j; rewrite mxE; exact: (Creal_Crat (Crat_rat _)). Qed.

Lemma Sc_sym : Sc \is symmetricmx.
Proof.
apply/is_hermitianmxP; rewrite expr0 scale1r.
apply/matrixP => i j; rewrite !mxE.
by rewrite /idfun (M2_get_sym j i) (M1_get_sym j i).
Qed.

Lemma Sc_herm : Sc \is hermsymmx.
Proof. exact: (realsym_hermsym Sc_sym Sc_real). Qed.

(* `ratrM M2_rat` is Hermitian (real symmetric).  Proved before the
   `Local Opaque` below, while `M2_rat` is still entry-transparent. *)
Lemma M2_C_real : (ratrM M2_rat) \is a mxOver Num.real.
Proof. apply/mxOverP => i j; rewrite mxE; exact: (Creal_Crat (Crat_rat _)). Qed.

Lemma M2_C_sym : (ratrM M2_rat) \is symmetricmx.
Proof.
apply/is_hermitianmxP; rewrite expr0 scale1r.
apply/matrixP => i j; rewrite !mxE.
by rewrite /idfun (M2_get_sym j i).
Qed.

Lemma M2_C_herm : (ratrM M2_rat) \is hermsymmx.
Proof. exact: (realsym_hermsym M2_C_sym M2_C_real). Qed.

(* ================================================================== *)
(* Section 3: the rat-level Rayleigh quadratic form of the pencil       *)
(* ================================================================== *)

(* The matrix quadratic form `v^T A v` of a 42x42 rat matrix, unfolded
   to the bigop used by `CertRayleigh.quad_spec`.  `A` is kept abstract
   so `mxE` never forces the ~10^200 denominators of the concrete
   matrices into unary. *)
Lemma quad_form_expand (A : 'M[rat]_42) :
  (trmx vr *m A *m vr) 0 0 = \sum_(j < 42) \sum_(i < 42) v_rat i * A i j * v_rat j.
Proof.
rewrite mxE; apply: eq_bigr => j _.
rewrite mxE big_distrl /=; apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

Lemma quadf_M1 : (trmx vr *m M1_rat *m vr) 0 0 = quad_spec M1_spec_ij.
Proof.
rewrite quad_form_expand /quad_spec exchange_big /=.
apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite M1_rat_spec.
Qed.

Lemma quadf_M2 : (trmx vr *m M2_rat *m vr) 0 0 = quad_spec M2_spec_ij.
Proof.
rewrite quad_form_expand /quad_spec exchange_big /=.
apply: eq_bigr => i _; apply: eq_bigr => j _.
by rewrite M2_rat_spec.
Qed.

(* Entry of the pencil, with `M1_rat` / `M2_rat` kept abstract via a
   universally-quantified helper (so `mxE` cannot unfold their entries). *)
Lemma Srat_entry (i j : 'I_42) :
  Srat i j = 105%:Q * M2_rat i j - 4%:Q * M1_rat i j.
Proof.
have HE : forall (a b : rat) (A B : 'M[rat]_42),
    (a *: A - b *: B) i j = a * A i j - b * B i j.
  by move=> a b A B; rewrite !mxE.
by rewrite /Srat HE.
Qed.

(* Bilinearity of the matrix quadratic form in the middle matrix,
   proved with all arguments abstract so the rewrites operate on small
   symbols and never force the concrete (~10^200-denominator) data. *)
Lemma quad_bilin (a b : rat) (A B : 'M[rat]_42) (u : 'cV[rat]_42) :
  trmx u *m (a *: A - b *: B) *m u
  = a *: (trmx u *m A *m u) - b *: (trmx u *m B *m u).
Proof. by rewrite mulmxBr mulmxBl -!scalemxAr -!scalemxAl. Qed.

(* The pencil quadratic form, as a CLOSED equation (no metavariables):
   instantiating `quad_bilin` by `apply` substitutes `vr` rather than
   unifying it, so `vr`'s ~10^200-denominator entries are never forced. *)
Lemma Srat_lin :
  trmx vr *m Srat *m vr
  = 105%:Q *: (trmx vr *m M2_rat *m vr) - 4%:Q *: (trmx vr *m M1_rat *m vr).
Proof. by rewrite /Srat; apply: (quad_bilin 105%:Q 4%:Q M2_rat M1_rat vr). Qed.

Lemma Srat_form_val :
  (trmx vr *m Srat *m vr) 0 0 =
  105%:Q * quad_spec M2_spec_ij - 4%:Q * quad_spec M1_spec_ij.
Proof.
have HE : forall (c d : rat) (P Q : 'M[rat]_1),
    (c *: P - d *: Q) 0 0 = c * P 0 0 - d * Q 0 0.
  by move=> c d P Q; rewrite !mxE.
(* `rewrite Srat_lin` is a closed-equation rewrite: it matches
   `trmx vr *m Srat *m vr` syntactically, without unifying `vr`.  The
   two quad-forms are discharged by `exact` (not `rewrite`, which would
   force the ~10^200 denominators when re-checking the goal). *)
rewrite Srat_lin HE.
by congr (105%:Q * _ - 4%:Q * _); [exact: quadf_M2 | exact: quadf_M1].
Qed.

(* `(ratrM v)^t* = ratrM (v^T)`: conjugation fixes the (real) `ratr`
   image entrywise. *)
Lemma ratrM_tC (m n : nat) (B : 'M[rat]_(m,n)) :
  ((ratrM B)^t*)%sesqui = ratrM (trmx B).
Proof.
apply/matrixP => i j; rewrite !mxE.
by rewrite conj_Crat // Crat_rat.
Qed.

(* From here on the concrete data (`M1_rat` / `M2_rat`, the witness vector
   `v_rat` / `vr`) are treated as opaque.  This is essential: every
   remaining proof only manipulates them through ring/`map_mx` lemmas, and
   making them opaque stops `done` / conversion from unfolding the
   `1 / (Z_to_int D)` and `1 / (Z_to_int v_den)` factors, whose
   `Pos.to_nat` (~10^200) would otherwise blow up the kernel in unary. *)
Local Opaque M1_rat M2_rat v_rat vr.

(* Positivity of the Hermitian form of `Sc` at the witness `ratrM vr`. *)
Lemma form_pos : 0 < (((ratrM vr)^t*)%sesqui *m Sc *m ratrM vr) 0 0.
Proof.
have -> : (((ratrM vr)^t*)%sesqui *m Sc *m ratrM vr)
        = ratrM (trmx vr *m Srat *m vr).
  by rewrite /Sc ratrM_tC -!map_mxM.
rewrite mxE Srat_form_val ltr0q subr_gt0.
exact: rayleigh_lt_main.
Qed.

(* ================================================================== *)
(* Section 4: generic spectral / matrix lemmas (abstract over C)        *)
(* ================================================================== *)

(* Conjugate-transpose of the identity. *)
Lemma tC1 (n : nat) : ((1%:M)^t*)%sesqui = 1%:M :> 'M[C]_n.
Proof. by rewrite trmx1 map_mx1. Qed.

(* Hermitian-preservation under congruence by an arbitrary factor. *)
Lemma herm_congr (n : nat) (X B : 'M[C]_n) :
  B \is hermsymmx -> ((X^t*)%sesqui *m B *m X) \is hermsymmx.
Proof.
move=> Bh.
have BE : (B^t*)%sesqui = B.
  by move/is_hermitianmxP: Bh; rewrite expr0 scale1r => H; rewrite -H.
apply/is_hermitianmxP; rewrite expr0 scale1r.
by rewrite !trmxC_mul trmxCK BE !mulmxA.
Qed.

(* Eigenvalues are preserved under similarity. *)
Lemma eig_simil (n : nat) (B X : 'M[C]_n) (a : C) :
  X \in unitmx -> eigenvalue B a -> eigenvalue (invmx X *m B *m X) a.
Proof.
move=> Xunit /eigenvalueP [v vB vneq0]; apply/eigenvalueP; exists (v *m X).
- have -> : (v *m X) *m (invmx X *m B *m X) = (v *m B) *m X.
    by rewrite !mulmxA -[v *m X *m invmx X]mulmxA mulmxV // mulmx1.
  by rewrite vB scalemxAl.
- apply/negP => /eqP h.
  move/negP: vneq0; apply; apply/eqP.
  by rewrite -[v](mulmxK Xunit) h mul0mx.
Qed.

(* Eigenvalue shift by a scalar matrix. *)
Lemma eig_shift (n : nat) (B : 'M[C]_n) (a c : C) :
  eigenvalue (B - c%:M) a -> eigenvalue B (a + c).
Proof.
move=> /eigenvalueP [v vB vne]; apply/eigenvalueP; exists v => //.
move: vB; rewrite mulmxBr mul_mx_scalar => Hv.
by rewrite scalerDl -Hv subrK.
Qed.

(* Congruence collapse of the Hermitian form: a unitary-free version of
   `w *m S2 *m w^t*` for `S2 = (invmx X)^t* *m B *m invmx X` and the
   witness `w = (X *m u)^t*`. *)
Lemma congr_collapse (n : nat) (X B : 'M[C]_n) (u : 'cV[C]_n) :
  X \in unitmx ->
  (((X *m u)^t*)%sesqui *m ((invmx X)^t* *m B *m invmx X)%sesqui *m (X *m u)) 0 0
   = ((u^t*)%sesqui *m B *m u) 0 0.
Proof.
move=> Xunit.
have h1 : invmx X *m (X *m u) = u by rewrite mulmxA mulVmx // mul1mx.
have h2 : ((X *m u)^t* *m (invmx X)^t*)%sesqui = (u^t*)%sesqui
  by rewrite -trmxC_mul h1.
by rewrite !mulmxA h2 mulmxKV.
Qed.

(* Conjugate-transpose of a real-scaled difference. *)
Lemma tC_scaleB (n : nat) (a b : C) (P Q : 'M[C]_n) :
  ((a *: P - b *: Q)^t*)%sesqui = a^* *: (P^t*)%sesqui - b^* *: (Q^t*)%sesqui.
Proof. by apply/matrixP => i j; rewrite !mxE rmorphB !rmorphM. Qed.

(* The abstract spectral bridge, free of all concrete (huge-denominator)
   data, so its kernel type-check never forces `Pos.to_nat D`.  Given a
   complex congruence factor `R` of `M1c` (`R^t* *m R = M1c`), a Hermitian
   `M2c`, and a vector `u` making the Hermitian form of the pencil
   `Sc' = 105 *: M2c - 4 *: M1c` strictly positive, the generalized matrix
   `A105 = 105 *: (M1c^-1 *m M2c)` has an eigenvalue `> 4`. *)
Lemma eigen_bridge (n : nat) (M1c M2c R Sc' A105 : 'M[C]_n) (u : 'cV[C]_n) :
  R \in unitmx ->
  (R^t*)%sesqui *m R = M1c ->
  M2c \is hermsymmx ->
  Sc' = 105%:R *: M2c - 4%:R *: M1c ->
  A105 = 105%:R *: (invmx M1c *m M2c) ->
  0 < ((u^t*)%sesqui *m Sc' *m u) 0 0 ->
  exists2 lam : C, eigenvalue A105 lam & 4%:R < lam.
Proof.
move=> Runit HM1c M2ch HSc'def HA105 Hpos.
have RtCu : (R^t*)%sesqui \in unitmx.
  by rewrite unitmxE det_map_mx det_tr fmorph_unit -unitfE -unitmxE.
have M1cu : M1c \in unitmx by rewrite -HM1c unitmx_mul RtCu Runit.
have M2cE : (M2c^t*)%sesqui = M2c.
  by move/is_hermitianmxP: M2ch; rewrite expr0 scale1r => H; rewrite -H.
have Sch : Sc' \is hermsymmx.
  apply/is_hermitianmxP; rewrite expr0 scale1r HSc'def tC_scaleB !conjC_nat M2cE.
  by rewrite -HM1c !trmxC_mul trmxCK.
set S2 := ((invmx R)^t* *m Sc' *m invmx R)%sesqui.
have S2herm : S2 \is hermsymmx by rewrite /S2; apply: herm_congr; exact: Sch.
have [a aeig apos] : exists2 a : C, eigenvalue S2 a & 0 < a.
  apply: (herm_crux (w := ((R *m u)^t*)%sesqui) S2herm).
  rewrite trmxCK /S2.
  rewrite (congr_collapse Sc' u Runit).
  exact: Hpos.
have keyInv : invmx R *m ((invmx R)^t*)%sesqui = invmx M1c.
  have hh : (invmx R *m ((invmx R)^t*)%sesqui) *m M1c = 1%:M.
    rewrite -HM1c !mulmxA.
    rewrite -[invmx R *m ((invmx R)^t*)%sesqui *m (R^t*)%sesqui]mulmxA -trmxC_mul.
    by rewrite mulmxV // tC1 mulmx1 mulVmx.
  by rewrite -[invmx R *m _](mulmxK M1cu) hh mul1mx.
have simEq : invmx R *m S2 *m R = invmx M1c *m Sc'.
  by rewrite /S2 !mulmxA keyInv (mulmxKV Runit).
have simEig : eigenvalue (invmx M1c *m Sc') a.
  by rewrite -simEq; exact: (eig_simil Runit aeig).
have HSc : invmx M1c *m Sc' = A105 - 4%:R *: 1%:M.
  by rewrite HSc'def mulmxBr -!scalemxAr (mulVmx M1cu) -HA105.
exists (a + 4%:R).
  apply: eig_shift; rewrite -scalemx1 -HSc; exact: simEig.
by rewrite -subr_gt0 addrK.
Qed.

(* ================================================================== *)
(* Section 5: the headline theorem                                      *)
(* ================================================================== *)

(* Connection facts feeding `eigen_bridge`: the concrete pencil `Sc` and
   `ratrM M105` rewritten into the algC-level `105 *: M2 - 4 *: M1` and
   `105 *: M1^-1 M2` shapes, by pushing the rat-level scaling / inverse
   through `ratr`.  The two `ratrM_*` helpers below do the push on ABSTRACT
   matrices (`map_mxB` / `map_ratr_scale` / `map_mxM` / `map_invmx`), so the
   ~10^200-denominator FLINT data is never forced: `ratrM_bridge_facts` only
   specialises them, keeping `M1_rat` / `M2_rat` folded.  Rewriting the
   helpers directly against the concrete goal would make `rewrite` scan the
   RHS and try to convert `invmx M1_rat` (a 42x42 determinant) to normal
   form and OOM; the abstract helpers + `exact:` / `transitivity` sidestep
   that, so both identities are now fully proved. *)
Lemma ratrM_lin (a b : rat) (A B : 'M[rat]_42) :
  ratrM (a *: A - b *: B) = ratr a *: ratrM A - ratr b *: ratrM B.
Proof. by rewrite map_mxB !map_ratr_scale. Qed.

Lemma ratrM_scaleM (a : rat) (A B : 'M[rat]_42) :
  ratrM (a *: (invmx A *m B)) = ratr a *: (invmx (ratrM A) *m ratrM B).
Proof. by rewrite map_ratr_scale map_mxM map_invmx. Qed.

Lemma ratrM_bridge_facts :
  (Sc = 105%:R *: ratrM M2_rat - 4%:R *: ratrM M1_rat) /\
  (ratrM M105 = 105%:R *: (invmx (ratrM M1_rat) *m ratrM M2_rat)).
Proof.
split.
  by rewrite /Sc /Srat ratrM_lin !rmorph_int.
transitivity (ratr 105%:Q *: (invmx (ratrM M1_rat) *m ratrM M2_rat)).
  by rewrite /M105 /A_rat; exact: ratrM_scaleM.
by rewrite rmorph_int.
Qed.

Theorem maynard_M105_certified :
  matches_closed_forms M105 /\
  exists lam : C, eigenvalue (ratrM M105) lam /\ (4 < lam).
Proof.
split; first exact: matches_closed_forms_M105.
have [R [Runit RR]] := M1_rat_factor.
have [HscE HM105] := ratrM_bridge_facts.
have [lam Hlam Hgt] :=
  eigen_bridge Runit RR M2_C_herm HscE HM105 form_pos.
by exists lam; split; [exact: Hlam | exact: Hgt].
Qed.
