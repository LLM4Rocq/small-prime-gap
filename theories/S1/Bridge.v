(* ================================================================== *)
(*  theories/S1/Bridge.v                                                *)
(*                                                                      *)
(*  Lifts the integer-polynomial primitives in IntPoly.v / SignChain.v  *)
(*  up to mathcomp-real-closed's `{poly realalg}`, plus the two         *)
(*  load-bearing sign-matching lemmas the IVT proof in CertL1.v reads:  *)
(*                                                                      *)
(*    pol_to_polyralg : list Z -> {poly realalg} (via pol_to_polyrat).  *)
(*    threshold_ralg  : Z -> Z -> realalg (rational threshold).         *)
(*    sgn_matches     : Z -> realalg -> Prop (joint-sign predicate).    *)
(*    sign_at_pinf_matches : sign_at_pinf p matches sgr (lead_coef p).  *)
(*    sign_at_rat_matches  : sign_at_rat p num den matches sgr p(.).    *)
(*                                                                      *)
(*  Pre-cleanup, this file also carried ~1300 lines of mods_int /       *)
(*  pnorm / prem-step / variation-bridge lemmas that fed the abstract   *)
(*  Sturm-count layer; that layer was retired and the helpers along     *)
(*  with it.  The file now lives at ~510 lines.                         *)
(* ================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf_th realalg.
Import GRing.Theory Num.Theory.
Import order.Order.POrderTheory.

From PrimeGapS1 Require Import IntPoly SignChain CharPoly.

Local Open Scope ring_scope.

(* `Z_to_int` is exported from CharPoly.v; we re-use it directly. *)

(* ------------------------------------------------------------------ *)
(*  Lifting `pol = list Z` to `{poly realalg}` via `pol_to_polyrat`    *)
(*  (from CharPoly.v), so any future proof pinning down                *)
(*  `pol_to_polyrat` automatically lifts to `pol_to_polyralg`.         *)
(* ------------------------------------------------------------------ *)

Definition pol_to_polyralg (p : pol) : {poly realalg} :=
  map_poly (ratr : rat -> realalg) (pol_to_polyrat p).

(* The rational threshold `num/den` lifted to realalg. *)
Definition threshold_ralg (num den : Z) : realalg :=
  ((Z_to_int num)%:~R / (Z_to_int den)%:~R)%R.
(* ------------------------------------------------------------------ *)
(* Helper: the core "no-zero" equivalence between our Z-valued         *)
(* `variation` and mathcomp's R-valued `changes`, stated on two        *)
(* parallel lists whose signs agree pointwise.                         *)
(*                                                                     *)
(* We work in `realDomainType` because mathcomp's `sgzM` (sign of a    *)
(* product) is only stated there; `realalg` is a realDomainType.       *)
(* ------------------------------------------------------------------ *)

Section SgnMatches.

Variable R : rcfType.

(* Joint-sign predicate: `n` is nonzero in Z, `r` is nonzero in R,
   and they have the same sign. We phrase it via comparisons with 0,
   which are directly useful in the `variation` / `changes` fixpoints. *)
Definition sgn_matches (n : Z) (r : R) : Prop :=
  ((BinInt.Z.eq n BinInt.Z0) <-> (r = 0))
  /\ (BinInt.Z.lt n BinInt.Z0 <-> (r < 0)%R)
  /\ (BinInt.Z.lt BinInt.Z0 n <-> (0 < r)%R).

Lemma sgn_matches_Rnz n r : sgn_matches n r -> n <> BinInt.Z0 -> (r != 0)%R.
Proof. by case=> [H1 _] Hn; apply/eqP => Hr; apply: Hn; apply/H1. Qed.


End SgnMatches.

(* ------------------------------------------------------------------ *)
(*  Sub-bridge helpers: "sign of `plead p` matches `sgz (lead_coef ...)`"*)
(*  and the analogous statement for Horner evaluation at a rational.    *)
(*                                                                     *)
(*  Both facts follow mechanically from `pol_to_polyrat`'s structural  *)
(*  definition and the injectivity of `ratr : rat -> realalg`.          *)
(* ------------------------------------------------------------------ *)

(* Structural cons-lemma for the rat-lifted polynomial. *)
Lemma pol_to_polyrat_cons (x : Z) (p : pol) :
  pol_to_polyrat (x :: p)
  = cons_poly ((Z_to_int x)%:~R : rat) (pol_to_polyrat p).
Proof. by []. Qed.

Lemma pol_to_polyrat_nil :
  pol_to_polyrat nil = 0 :> {poly rat}.
Proof. by []. Qed.

(* Cons-lemma for the realalg-lifted polynomial: goes through
   `map_poly` + `cons_poly_def`. *)
Lemma pol_to_polyralg_cons (x : Z) (p : pol) :
  pol_to_polyralg (x :: p)
  = pol_to_polyralg p * 'X + ((Z_to_int x)%:~R : realalg)%:P.
Proof.
rewrite /pol_to_polyralg pol_to_polyrat_cons cons_poly_def.
rewrite rmorphD rmorphM /= map_polyX map_polyC /=.
by rewrite ratr_int.
Qed.

Lemma pol_to_polyralg_nil :
  pol_to_polyralg nil = 0 :> {poly realalg}.
Proof. by rewrite /pol_to_polyralg pol_to_polyrat_nil rmorph0. Qed.

(* ------------------------------------------------------------------ *)
(*  Structural lemma `sgn_matches_int` (below) used by the four        *)
(*  sign-bridge helpers.                                                *)
(*                                                                      *)
(*  This is a small, local structural fact about `pol_to_polyralg` that *)
(*  connects the `{poly realalg}` leading coefficient with the integer  *)
(*  `plead` function.  Proved outright by case analysis on the Z        *)
(*  constructor (Z0 / Zpos / Zneg) and standard MathComp lemmas         *)
(*  `ltr0z` / `ltrz0`.                                                  *)
(* ------------------------------------------------------------------ *)

(* Symbolic sign-matching for a realalg element that comes from an int.
   We split on `n` into its three Z constructors and dispatch each sub-case
   by reducing to integer-to-real ordering lemmas `ltr0z` / `ltrz0`. *)
Lemma sgn_matches_int (n : Z) :
  sgn_matches realalg (sgn_Z n) ((Z_to_int n)%:~R : realalg).
Proof.
rewrite /sgn_matches /sgn_Z.
have Hpos_pos : forall q : positive, ((Z_to_int (Z.pos q))%:~R : realalg) > 0.
{ by move=> q; rewrite ltr0z /Z_to_int; apply/ltP/Pos2Nat.is_pos. }
have Hneg_neg : forall q : positive, ((Z_to_int (Z.neg q))%:~R : realalg) < 0.
{ by move=> q; rewrite ltrz0 /Z_to_int; case: (Pos.to_nat _). }
case: n => [|q|q] /=.
- split; last split.
  + split; first by []. by move=> _.
  + split; first by []. by rewrite ltxx.
  + split; first by []. by rewrite ltxx.
- split; last split.
  + split; first by [].
    move=> H; have := Hpos_pos q; by rewrite H ltxx.
  + split; first by [].
    move=> H; have := Hpos_pos q; by rewrite lt_gtF.
  + split; first by move=> _; exact: Hpos_pos.
    by [].
- split; last split.
  + split; first by [].
    move=> H; have := Hneg_neg q; by rewrite H ltxx.
  + split; first by move=> _; exact: Hneg_neg.
    by [].
  + split; first by [].
    move=> H; have := Hneg_neg q; by rewrite lt_gtF.
Qed.

(* Auxiliary: Z -> realalg lifts nonzero integers to nonzero realalg. *)
Lemma Z_to_int_realalg_nz (x : Z) :
  x <> BinInt.Z0 -> ((Z_to_int x)%:~R : realalg) != 0.
Proof.
move=> Hx.
have Hsgn : sgn_Z x <> BinInt.Z0 by rewrite /sgn_Z; case: x Hx.
have Hs : sgn_matches realalg (sgn_Z x) ((Z_to_int x)%:~R : realalg)
  := sgn_matches_int x.
exact: (sgn_matches_Rnz _ _ _ Hs Hsgn).
Qed.

(* Strengthened induction: `plead_aux p acc`, lifted through `Z_to_int`,
   agrees with `lead_coef (pol_to_polyralg p)` when `pol_to_polyralg p`
   is nonzero, and with `(Z_to_int acc)%:~R` otherwise. *)
Lemma lead_coef_pol_to_polyralg_aux (p : pol) (acc : Z) :
  ((Z_to_int (plead_aux p acc))%:~R : realalg) =
  (if pol_to_polyralg p == 0 then ((Z_to_int acc)%:~R : realalg)
   else lead_coef (pol_to_polyralg p)).
Proof.
elim: p acc => [|x p IH] acc.
  by rewrite /= pol_to_polyralg_nil eqxx.
rewrite pol_to_polyralg_cons.
set p' := pol_to_polyralg p in IH *.
set c : realalg := ((Z_to_int x)%:~R)%R.
have Hstep : plead_aux (x :: p) acc =
             plead_aux p (if BinInt.Z.eqb x BinInt.Z0 then acc else x).
{ by simpl; case: (BinInt.Z.eqb x BinInt.Z0). }
rewrite Hstep.
case Hp' : (p' == 0).
- (* p' = 0: sum reduces to c%:P *)
  move/eqP: Hp' => Hp'.
  rewrite Hp' mul0r add0r.
  case Hx : (BinInt.Z.eqb x BinInt.Z0).
  + have Hxz : x = BinInt.Z0 by apply/Z.eqb_eq.
    have Hc0 : c = 0 by rewrite /c Hxz /Z_to_int /=; exact: mulr0n.
    rewrite Hc0 polyC0 eqxx.
    by rewrite IH Hp' eqxx.
  + have Hxnz : x <> BinInt.Z0 by move/Z.eqb_neq: Hx.
    have Hcnz : c != 0 := Z_to_int_realalg_nz x Hxnz.
    have Hcpnz : c%:P != 0 by rewrite polyC_eq0.
    rewrite (negbTE Hcpnz).
    rewrite lead_coefC.
    by rewrite IH Hp' eqxx.
- (* p' != 0: lead_coef comes from the 'X part *)
  move/negbT: Hp' => Hp'.
  have Hszp : (0 < size p')%N by rewrite lt0n size_poly_eq0.
  have HsMX : size (p' * 'X) = (size p').+1 by apply: size_mulX.
  have Hsz : size (p' * 'X + c%:P) = (size p').+1.
  { rewrite size_MXaddC (negbTE Hp') /=. by []. }
  have Hsum_nz : p' * 'X + c%:P != 0.
  { apply/eqP => H; have : size (p' * 'X + c%:P) = 0%N by rewrite H size_poly0.
    by rewrite Hsz. }
  rewrite (negbTE Hsum_nz).
  have Hsize_lt : (size (c%:P : {poly realalg}) < size ((p' * 'X)%R : {poly realalg}))%N.
  { rewrite HsMX ltnS.
    exact: (leq_trans (size_polyC_leq1 _) Hszp). }
  rewrite lead_coefDl // lead_coefMX.
  rewrite IH (negbTE Hp').
  by case: (BinInt.Z.eqb x BinInt.Z0).
Qed.

Lemma lead_coef_pol_to_polyralg (p : pol) :
  lead_coef (pol_to_polyralg p)
  = ((Z_to_int (plead p))%:~R : realalg).
Proof.
rewrite /plead.
have := lead_coef_pol_to_polyralg_aux p BinInt.Z0.
case Hp : (pol_to_polyralg p == 0).
- move/eqP: Hp => Hp0.
  rewrite Hp0 lead_coef0.
  have -> : ((Z_to_int BinInt.Z0)%:~R : realalg) = 0
    by rewrite /Z_to_int /=; exact: mulr0n.
  by move=> ->.
- by move=> ->.
Qed.

(* Unconditional sign-matching for the leading coefficient. *)
Lemma sign_at_pinf_matches (p : pol) :
  sgn_matches _ (sign_at_pinf p) (lead_coef (pol_to_polyralg p)).
Proof.
rewrite /sign_at_pinf lead_coef_pol_to_polyralg.
exact: sgn_matches_int.
Qed.

(* ------------------------------------------------------------------ *)
(*  Bridge `Z_to_int` is a ring homomorphism (enough for our uses).    *)
(* ------------------------------------------------------------------ *)

Lemma Z_to_int_case (z : Z) :
  z = BinInt.Z0 \/
  (exists n : nat, (0 < n)%N /\ z = BinInt.Z.of_nat n /\ Z_to_int z = Posz n) \/
  (exists n : nat, (0 < n)%N /\ z = BinInt.Z.opp (BinInt.Z.of_nat n)
                   /\ Z_to_int z = (- Posz n)%R).
Proof.
case: z => [|p|p]; [by left|right; left|right; right].
- exists (Pos.to_nat p); split; [exact/ltP/Pos2Nat.is_pos|].
  split; [by rewrite positive_nat_Z|by []].
- exists (Pos.to_nat p); split; [exact/ltP/Pos2Nat.is_pos|].
  split; [by rewrite positive_nat_Z|].
  rewrite /Z_to_int /= NegzE.
  have Hp := Pos2Nat.is_pos p.
  case Hn : (Pos.to_nat p) => [|n]; first by lia.
  by rewrite subn1 /=.
Qed.

Lemma Z_to_int_of_nat (n : nat) :
  Z_to_int (BinInt.Z.of_nat n) = Posz n.
Proof. case: n => [//|n]; by rewrite /Z_to_int /= SuccNat2Pos.id_succ. Qed.

Lemma Z_to_int_opp_of_nat (n : nat) :
  Z_to_int (BinInt.Z.opp (BinInt.Z.of_nat n)) = (- Posz n)%R.
Proof.
case: n => [|n] /=; first by rewrite /Z_to_int /= oppr0.
rewrite /Z_to_int /= NegzE SuccNat2Pos.id_succ.
by rewrite subn1 /=.
Qed.

Lemma Z_to_int_mul (a b : Z) :
  Z_to_int (BinInt.Z.mul a b) = (Z_to_int a * Z_to_int b)%R.
Proof.
have [->|[[na [_ [-> ->]]]|[na [_ [-> ->]]]]] := Z_to_int_case a.
- by rewrite /= mul0r.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.mul_0_r mulr0 /=.
  + by rewrite -Nat2Z.inj_mul Z_to_int_of_nat -PoszM.
  + rewrite BinInt.Z.mul_opp_r -Nat2Z.inj_mul Z_to_int_opp_of_nat.
    by rewrite mulrN -PoszM.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.mul_0_r mulr0 /=.
  + rewrite BinInt.Z.mul_opp_l -Nat2Z.inj_mul Z_to_int_opp_of_nat.
    by rewrite mulNr -PoszM.
  + rewrite BinInt.Z.mul_opp_opp -Nat2Z.inj_mul Z_to_int_of_nat.
    by rewrite mulrNN -PoszM.
Qed.

Lemma nat_sub_Posz (n m : nat) :
  ((Posz n - Posz m)%R : int) =
  Z_to_int (BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)).
Proof.
case Hcmp : (n <= m)%N.
- have -> : BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)
          = BinInt.Z.opp (BinInt.Z.of_nat (m - n)).
  { rewrite Nat2Z.inj_sub; [lia|apply/leP; exact: Hcmp]. }
  rewrite Z_to_int_opp_of_nat.
  rewrite -(subzn Hcmp).
  by rewrite opprB.
- move/negbT: Hcmp; rewrite -ltnNge => Hlt.
  have Hle : (m <= n)%N := ltnW Hlt.
  have -> : BinInt.Z.sub (BinInt.Z.of_nat n) (BinInt.Z.of_nat m)
          = BinInt.Z.of_nat (n - m).
  { rewrite Nat2Z.inj_sub; [lia|apply/leP; exact: Hle]. }
  by rewrite Z_to_int_of_nat -(subzn Hle).
Qed.

Lemma Z_to_int_add (a b : Z) :
  Z_to_int (BinInt.Z.add a b) = (Z_to_int a + Z_to_int b)%R.
Proof.
have [->|[[na [_ [-> ->]]]|[na [_ [-> ->]]]]] := Z_to_int_case a.
- by rewrite BinInt.Z.add_0_l add0r.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.add_0_r addr0 Z_to_int_of_nat.
  + by rewrite -Nat2Z.inj_add Z_to_int_of_nat -PoszD.
  + have -> : BinInt.Z.add (BinInt.Z.of_nat na) (BinInt.Z.opp (BinInt.Z.of_nat nb))
            = BinInt.Z.sub (BinInt.Z.of_nat na) (BinInt.Z.of_nat nb)
      by rewrite /BinInt.Z.sub.
    by rewrite -nat_sub_Posz.
- have [->|[[nb [_ [-> ->]]]|[nb [_ [-> ->]]]]] := Z_to_int_case b.
  + by rewrite BinInt.Z.add_0_r addr0 Z_to_int_opp_of_nat.
  + have -> : BinInt.Z.add (BinInt.Z.opp (BinInt.Z.of_nat na)) (BinInt.Z.of_nat nb)
            = BinInt.Z.sub (BinInt.Z.of_nat nb) (BinInt.Z.of_nat na)
      by rewrite /BinInt.Z.sub BinInt.Z.add_comm.
    by rewrite -nat_sub_Posz addrC.
  + rewrite -BinInt.Z.opp_add_distr -Nat2Z.inj_add Z_to_int_opp_of_nat.
    by rewrite -opprD PoszD.
Qed.

(* Lift to the realalg level. *)
Lemma Z_to_int_mul_ralg (a b : Z) :
  ((Z_to_int (BinInt.Z.mul a b))%:~R : realalg) =
  ((Z_to_int a)%:~R * (Z_to_int b)%:~R)%R.
Proof. by rewrite Z_to_int_mul intrM. Qed.

Lemma Z_to_int_add_ralg (a b : Z) :
  ((Z_to_int (BinInt.Z.add a b))%:~R : realalg) =
  ((Z_to_int a)%:~R + (Z_to_int b)%:~R)%R.
Proof. by rewrite Z_to_int_add intrD. Qed.


(* Auxiliary: positivity of `snd (peval_at_rat_aux p num den)` when `den > 0`. *)
Lemma peval_at_rat_aux_snd_pos (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  BinInt.Z.lt BinInt.Z0 (snd (peval_at_rat_aux p num den)).
Proof.
Local Close Scope ring_scope.
move=> Hd.
elim: p => [//|a p IH] /=.
case Hp : (peval_at_rat_aux p num den) => [v dp].
rewrite Hp /= in IH. simpl. nia.
Qed.
Local Open Scope ring_scope.

(* Key identity over realalg: the realalg horner evaluation of the lifted
   polynomial at `num/den`, multiplied by the (lifted) denominator power,
   equals the (lifted) integer result of `peval_at_rat_aux`. *)
Lemma horner_pol_to_polyralg_aux_identity (p : pol) (num den : Z)
  (Hd : BinInt.Z.lt BinInt.Z0 den) :
  let (v, dp) := peval_at_rat_aux p num den in
  ((pol_to_polyralg p).[threshold_ralg num den] : realalg) *
     ((Z_to_int dp)%:~R : realalg) = ((Z_to_int v)%:~R : realalg).
Proof.
have Hden_ra_pos : ((Z_to_int den)%:~R : realalg) > 0.
{ have Hsgn : BinInt.Z.lt BinInt.Z0 (sgn_Z den)
    by rewrite /sgn_Z; case: den Hd => //.
  have Hds : sgn_matches realalg (sgn_Z den) ((Z_to_int den)%:~R : realalg)
    := sgn_matches_int den.
  by case: Hds => [_ [_ Hg]]; apply/Hg. }
have Hden_ra_nz : ((Z_to_int den)%:~R : realalg) != 0 by apply: lt0r_neq0.
elim: p => /=.
- rewrite pol_to_polyralg_nil horner0 mul0r /Z_to_int /=.
  symmetry; exact: mulr0z.
- move=> a p IH.
  case Hp : (peval_at_rat_aux p num den) => [v dp].
  rewrite Hp in IH.
  rewrite pol_to_polyralg_cons.
  rewrite hornerD hornerC hornerM hornerX.
  set t : realalg := threshold_ralg num den.
  set cr : realalg := ((Z_to_int a)%:~R)%R.
  set P : realalg := (pol_to_polyralg p).[t].
  set num_ra : realalg := ((Z_to_int num)%:~R)%R.
  set den_ra : realalg := ((Z_to_int den)%:~R)%R.
  set dp_ra : realalg := ((Z_to_int dp)%:~R)%R.
  (* t * den_ra = num_ra *)
  have Htden : (t * den_ra = num_ra)%R.
  { rewrite /t /threshold_ralg /num_ra /den_ra.
    by rewrite -mulrA mulVf // mulr1. }
  (* Key: reduce both sides to the same sum. *)
  rewrite Z_to_int_add_ralg !Z_to_int_mul_ralg.
  rewrite -/num_ra -/den_ra -/dp_ra -/cr.
  (* Goal: (P * t + cr) * (den_ra * dp_ra) = cr * (den_ra * dp_ra) + num_ra * (Z_to_int v)%:~R *)
  rewrite mulrDl addrC.
  congr (_ + _).
  (* (P * t) * (den_ra * dp_ra) = num_ra * (Z_to_int v)%:~R *)
  rewrite -(mulrA P t _) (mulrA t _ _) Htden.
  rewrite mulrA.
  (* (P * num_ra) * dp_ra = num_ra * (Z_to_int v)%:~R *)
  rewrite (mulrC P num_ra) -mulrA.
  by rewrite IH.
Qed.

(* Generic: sign-matching is preserved by multiplication by a positive
   realalg scalar. *)
Lemma sgn_matches_mul_pos_r (n : Z) (r s : realalg) :
  (0 < s)%R -> sgn_matches _ n (r * s) -> sgn_matches _ n r.
Proof.
move=> Hs [Hz [Hl Hg]].
have Hsnz : s != 0 by apply: lt0r_neq0.
have Hsinv : (0 < s^-1)%R by rewrite invr_gt0.
split; last split.
- split.
  + move=> Hnz.
    have : (r * s = 0)%R by apply/Hz.
    by move/eqP; rewrite mulf_eq0 (negbTE Hsnz) orbF => /eqP.
  + move=> Hr0; apply/Hz. rewrite Hr0 mul0r. by [].
- split.
  + move=> Hnl.
    have : (r * s < 0)%R by apply/Hl.
    by rewrite pmulr_llt0.
  + move=> Hrneg; apply/Hl.
    by rewrite pmulr_llt0.
- split.
  + move=> Hng.
    have : (0 < r * s)%R by apply/Hg.
    by rewrite pmulr_lgt0.
  + move=> Hrpos; apply/Hg.
    by rewrite pmulr_lgt0.
Qed.

(* Main: sign-matching of the integer peval and the realalg horner. *)
Lemma horner_pol_to_polyralg_rat (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  sgn_matches _ (peval_at_rat p num den)
    ((pol_to_polyralg p).[threshold_ralg num den]).
Proof.
move=> Hd.
have Hid := horner_pol_to_polyralg_aux_identity p num den Hd.
have Hdp_pos := peval_at_rat_aux_snd_pos p num den Hd.
have Hgen : forall z, BinInt.Z.lt BinInt.Z0 z ->
  ((Z_to_int z)%:~R : realalg) > 0.
{ move=> z Hz.
  have Hsgn : BinInt.Z.lt BinInt.Z0 (sgn_Z z)
    by rewrite /sgn_Z; case: z Hz.
  have Hds : sgn_matches realalg (sgn_Z z) ((Z_to_int z)%:~R : realalg)
    := sgn_matches_int z.
  by case: Hds => [_ [_ Hg]]; apply/Hg. }
rewrite /peval_at_rat.
case Hp : (peval_at_rat_aux p num den) => [v dp].
rewrite Hp in Hid. rewrite Hp /= in Hdp_pos. simpl.
clear Hp.
set H := (pol_to_polyralg p).[_].
have Hdp_ra_pos : ((Z_to_int dp)%:~R : realalg) > 0 by exact: Hgen.
(* We want sgn_matches _ v H.
   By sgn_matches_mul_pos_r, it suffices: sgn_matches _ v (H * dp_ra),
   where dp_ra = (Z_to_int dp)%:~R.
   By Hid, H * dp_ra = (Z_to_int v)%:~R, and the sign of that w.r.t. v
   is sgn_matches_int (after reducing sgn_Z to Z.lt/eq).
   But sgn_matches_int gives `sgn_matches _ (sgn_Z v) (Z_to_int v)%:~R`,
   which is sgn_matches of `sgn_Z v`, not `v`. However the two are
   equivalent on v because `sgn_matches` only uses the comparisons with 0. *)
apply: (sgn_matches_mul_pos_r _ _ _ Hdp_ra_pos).
rewrite Hid. clear Hid H Hdp_ra_pos Hdp_pos Hgen.
(* Goal: sgn_matches _ v (Z_to_int v)%:~R.
   Prove by case on v. *)
have Hgen2 : forall z, sgn_matches realalg z ((Z_to_int z)%:~R : realalg).
{ move=> z; rewrite /sgn_matches.
  have Hpos_pos : forall q : positive, ((Z_to_int (Z.pos q))%:~R : realalg) > 0.
  { by move=> q; rewrite ltr0z /Z_to_int; apply/ltP/Pos2Nat.is_pos. }
  have Hneg_neg : forall q : positive, ((Z_to_int (Z.neg q))%:~R : realalg) < 0.
  { by move=> q; rewrite ltrz0 /Z_to_int; case: (Pos.to_nat _). }
  case: z => [|q|q].
  - split; last split.
    + by split => // _; rewrite /Z_to_int /= mulr0z.
    + by split => //; rewrite /Z_to_int /= mulr0z ltxx.
    + by split => //; rewrite /Z_to_int /= mulr0z ltxx.
  - split; last split.
    + split => //.
      move=> H; have := Hpos_pos q; by rewrite H ltxx.
    + split => //.
      move=> H; have := Hpos_pos q; by rewrite lt_gtF.
    + split; first by move=> _; exact: Hpos_pos.
      by [].
  - split; last split.
    + split => //.
      move=> H; have := Hneg_neg q; by rewrite H ltxx.
    + split; first by move=> _; exact: Hneg_neg.
      by [].
    + split => //.
      move=> H; have := Hneg_neg q; by rewrite lt_gtF. }
exact: Hgen2.
Qed.

Lemma sign_at_rat_matches (p : pol) (num den : Z) :
  BinInt.Z.lt BinInt.Z0 den ->
  sgn_matches _ (sign_at_rat p num den)
    ((pol_to_polyralg p).[threshold_ralg num den]).
Proof.
move=> Hden.
have Hm := horner_pol_to_polyralg_rat p num den Hden.
rewrite /sign_at_rat /sgn_matches /sgn_Z.
case: Hm => [Hz [Hl Hg]]; split; last split.
- split.
  + case En : (peval_at_rat p num den) => [||q] // _.
    by apply/Hz.
  + move=> Heq. move/Hz in Heq. by rewrite Heq.
- split.
  + case En : (peval_at_rat p num den) => [||q] //= _.
    apply/Hl; rewrite En. by lia.
  + move=> Hr. move/Hl in Hr. case En : (peval_at_rat p num den) Hr => //=; lia.
- split.
  + case En : (peval_at_rat p num den) => [||q] //= _.
    apply/Hg; rewrite En. by lia.
  + move=> Hr. move/Hg in Hr. case En : (peval_at_rat p num den) Hr => //=; lia.
Qed.

