(**md**************************************************************************)
(* # SpectralCrux                                                            *)
(*                                                                           *)
(* The variational "crux" for the eigenvalue route, over a                   *)
(* `numClosedFieldType` (instantiated at `algC`).  Built on the COMPLEX      *)
(* spectral theorem shipped in mathcomp 2.5.0 (`orthomx_spectralP`); no      *)
(* dependency on the real spectral theorem (PR #1611) and no project axioms. *)
(*                                                                           *)
(* ```                                                                       *)
(*   herm_crux : A hermitian, 0 < w^* A w  ->  exists a, eig A a & a > 0.    *)
(* ```                                                                       *)
(* i.e. a Hermitian matrix with a strictly positive Hermitian quadratic      *)
(* form at some vector has a strictly positive eigenvalue.  Needs only       *)
(* `hermsymmx` (not `realmx`), so a *complex* congruence factor may be used  *)
(* downstream -- no real Cholesky needed for the crux.                       *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp Require Import spectral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section HermCrux.
Variable C : numClosedFieldType.

(* conjugate-transpose of a product *)
Lemma trmxC_mul m n p (A : 'M[C]_(m, n)) (B : 'M[C]_(n, p)) :
  ((A *m B) ^t*)%sesqui = ((B ^t*)%sesqui) *m ((A ^t*)%sesqui).
Proof. by rewrite trmx_mul map_mxM. Qed.

(* quadratic form of a diagonal matrix is a real-weighted sum of squares *)
Lemma quad_diag n (d : 'rV[C]_n) (u : 'cV[C]_n) :
  (((u ^t*)%sesqui) *m diag_mx d *m u) 0 0 = \sum_j d 0 j * `|u j 0| ^+ 2.
Proof.
rewrite -mulmxA mul_diag_mx mxE.
apply: eq_bigr => j _.
by rewrite !mxE normCKC mulrCA.
Qed.

(* a diagonal entry is an eigenvalue of any matrix similar to that diagonal *)
Lemma eig_transfer n (d : 'rV[C]_n) (P : 'M[C]_n) (i : 'I_n) :
  P \in unitmx -> eigenvalue (invmx P *m diag_mx d *m P) (d 0 i).
Proof.
move=> Punit.
apply/eigenvalueP; exists ('e_i *m P).
  by rewrite !mulmxA (mulmxK Punit) -(rowE i (diag_mx d))
             row_diag_mx -scalemxAl.
apply/negP => /eqP h.
have key : ('e_i : 'rV[C]_n) 0 i = 0.
  by rewrite -['e_i](mulmxK Punit) h mul0mx mxE.
move: key; rewrite !mxE !eqxx /= => /eqP H.
by rewrite oner_eq0 in H.
Qed.

(* a strictly positive real-weighted sum of squares has a positive weight *)
Lemma realsum_pos n (s t : 'I_n -> C) :
  (forall j, s j \is Num.real) -> (forall j, 0 <= t j) ->
  0 < \sum_j s j * t j -> exists j, 0 < s j.
Proof.
move=> sr tge Hsum.
apply/existsP.
rewrite -[[exists j, 0 < s j]]negbK negb_exists.
apply/negP => /forallP Hall.
have Hle : \sum_j s j * t j <= 0.
  apply: sumr_le0 => j _.
  apply: mulr_le0_ge0; last exact: tge.
  have e : (s j <= 0) = ~~ (0 < s j) := @real_leNgt C (s j) 0 (sr j) (@real0 C).
  by rewrite e; exact: Hall.
by move: Hsum; rewrite (Order.POrderTheory.le_gtF Hle).
Qed.

(* The Hermitian crux. *)
Lemma herm_crux n (A : 'M[C]_n) (w : 'rV[C]_n) :
  A \is hermsymmx -> 0 < (w *m A *m (w ^t*)%sesqui) 0 0 ->
  exists2 a : C, eigenvalue A a & 0 < a.
Proof.
move=> Aherm Hpos.
have Anorm : A \is normalmx := hermitian_normalmx Aherm.
set P := spectralmx A.
set sp := spectral_diag A.
have spr : forall i j, sp i j \is Num.real.
  by apply/mxOverP; apply: hermitian_spectral_diag_real Aherm.
have Punit : P \in unitmx := spectral_unit A.
have Puni : P \is unitarymx := spectral_unitarymx A.
have AE : A = invmx P *m diag_mx sp *m P by apply/orthomx_spectralP.
pose u := P *m (w ^t*)%sesqui.
have keyq : w *m A *m (w ^t*)%sesqui = ((u ^t*)%sesqui) *m diag_mx sp *m u.
  rewrite /u trmxC_mul trmxCK AE (invmx_unitary Puni).
  by rewrite !mulmxA.
have keyq0 : (w *m A *m (w ^t*)%sesqui) 0 0 = \sum_j sp 0 j * `|u j 0| ^+ 2.
  by rewrite keyq quad_diag.
have [j Hj] : exists j, 0 < sp 0 j.
  apply: (realsum_pos (t := fun j => `|u j 0| ^+ 2)).
  - by move=> k; apply: spr.
  - by move=> k; apply: exprn_ge0; apply: normr_ge0.
  - by rewrite -keyq0.
exists (sp 0 j); last exact: Hj.
rewrite AE; apply: eig_transfer; exact: Punit.
Qed.

End HermCrux.
