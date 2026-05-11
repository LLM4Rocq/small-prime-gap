(* ============================================================== *)
(*  MaynardSpecBridge.v                                             *)
(*                                                                  *)
(*  Bridge between PART A (rat-level) and PART B (Z-level) of       *)
(*  MaynardSpec.v.  Each operation in PART A has a directly         *)
(*  corresponding operation in PART B, so each bridge is a small    *)
(*  structural induction.                                           *)
(*                                                                  *)
(*  Headlines:                                                      *)
(*    M1_spec_rat_eq i j  :  M1_spec_ij i j = qfrac (m1_num_den_at i j)*)
(*    M2_spec_rat_eq i j  :  M2_spec_ij i j = qfrac (m2_num_den_at i j)*)
(*                                                                  *)
(*  This file is a leaf in the dependency DAG (Cert.v does not      *)
(*  import it) and is independent of MaynardVerify.v's load-bearing *)
(*  Z-level cross-check.  Its purpose is to certify in the kernel   *)
(*  that the rat-level paper-form spec and the Z-level computational*)
(*  spec encode the same closed forms.                              *)
(* ============================================================== *)

From Stdlib Require Import ZArith List Lia Znumtheory.
Import ListNotations.

From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import
  MaynardFactQ MaynardBasis MaynardSpec CharPoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ============================================================== *)
(*  Layer 0: factorial bridge.                                      *)
(* ============================================================== *)

(* `factZ n = Z.of_nat n!`.  Pure structural induction. *)
Lemma factZ_eq_Z_of_nat (n : nat) :
  factZ n = BinInt.Z.of_nat n`!.
Proof.
  elim: n => [//|n IH] /=.
  rewrite IH factS.
  by rewrite -multE Nat2Z.inj_mul.
Qed.

(* `Z_to_int (factZ n) = Posz n!`. *)
Lemma Z_to_int_factZ (n : nat) :
  Z_to_int (factZ n) = Posz n`!.
Proof. by rewrite factZ_eq_Z_of_nat Z_to_int_of_nat. Qed.

(* `factZ n` lifted to `rat` equals `factQ n`. *)
Lemma factZ_to_rat (n : nat) :
  ((Z_to_int (factZ n))%:~R : rat) = factQ n.
Proof. by rewrite Z_to_int_factZ /factQ. Qed.

(* nat-level: m! divides n! when m <= n.  Standard induction. *)
Lemma fact_dvd_fact (m n : nat) :
  (m <= n)%nat -> (m`! %| n`!)%nat.
Proof.
  elim: n => [|n IH] H.
  - by rewrite leqn0 in H; rewrite (eqP H).
  - rewrite factS.
    case: (leqP m n) => Hmn.
    + apply: dvdn_mull; exact: (IH Hmn).
    + have -> : m = n.+1 by apply/eqP; rewrite eqn_leq H Hmn.
      exact: dvdnn.
Qed.

(* Z.of_nat preserves divisibility from nat to Z. *)
Lemma Z_of_nat_dvd (a b : nat) :
  (a %| b)%nat -> (Z.of_nat a | Z.of_nat b)%Z.
Proof.
  move=> /dvdnP[k Hk]. exists (Z.of_nat k).
  by rewrite Hk -multE Nat2Z.inj_mul Z.mul_comm.
Qed.

(* Z-level: factZ x divides factZ (2*x) for any nat x. *)
Lemma factZ_dvd_double (x : nat) :
  (factZ x | factZ (2 * x)%nat)%Z.
Proof.
  rewrite !factZ_eq_Z_of_nat.
  apply: Z_of_nat_dvd; apply: fact_dvd_fact.
  by rewrite leq_pmull.
Qed.

(* `factZ n` is strictly positive. *)
Lemma factZ_pos (n : nat) : Z.lt 0 (factZ n).
Proof.
  rewrite factZ_eq_Z_of_nat.
  have /ltP H := fact_gt0 n.
  lia.
Qed.

(* `Z_to_int` of a strictly-positive Z is nonzero in int. *)
Lemma Z_to_int_pos_neq0 (z : Z) : Z.lt 0 z -> Z_to_int z != 0.
Proof.
  case: z => [|p _|p H] //.
  rewrite Z_to_int_pos_pos eqz_nat -lt0n.
  apply/ltP; exact: Pos2Nat.is_pos.
Qed.

(* Lifted to rat: ((Z_to_int z)%:~R : rat) is nonzero when z > 0. *)
Lemma Z_to_int_pos_rat_neq0 (z : Z) :
  Z.lt 0 z -> ((Z_to_int z)%:~R : rat) != 0.
Proof.
  by move=> /Z_to_int_pos_neq0; rewrite intr_eq0.
Qed.

(* Generic integer-division-is-exact bridge: when `b | a` and `b > 0`,
   the integer division `a / b` lifts to the rat division
   `(a : rat) / (b : rat)`. *)
Lemma Z_to_int_div_exact (a b : Z) :
  Z.lt 0 b -> (b | a)%Z ->
  ((Z_to_int (a / b))%:~R : rat)
  = (Z_to_int a)%:~R / (Z_to_int b)%:~R.
Proof.
  move=> Hbpos Hdvd.
  have Hnz : ((Z_to_int b)%:~R : rat) != 0 by exact: Z_to_int_pos_rat_neq0.
  apply: (canRL (mulfK Hnz)).
  rewrite -intrM -Z_to_int_mul Z.mul_comm.
  by rewrite -Zdivide_Zdiv_eq.
Qed.

(* ============================================================== *)
(*  Layer 1: dblratZ, prod_dblratZ, cffZ                            *)
(* ============================================================== *)

Lemma dblratZ_to_rat (x : nat) :
  ((Z_to_int (dblratZ x))%:~R : rat)
  = factQ (2 * x) / factQ x.
Proof.
  rewrite /dblratZ Z_to_int_div_exact ?factZ_to_rat //.
  - exact: factZ_pos.
  - exact: factZ_dvd_double.
Qed.

Lemma prod_dblratZ_to_rat (a : list nat) :
  ((Z_to_int (prod_dblratZ a))%:~R : rat)
  = \prod_(x <- a) (factQ (2 * x) / factQ x).
Proof.
  elim: a => [|x a IH] /=.
  - by rewrite Z_to_int_1_rat big_nil.
  - rewrite Z_to_int_mul intrM dblratZ_to_rat IH.
    by rewrite big_cons.
Qed.

(* `cffZ a = prod_dblratZ a` definitionally; bridge is direct. *)
Lemma cffZ_to_rat (a : list nat) :
  ((Z_to_int (cffZ a))%:~R : rat) = cff a.
Proof.
  by rewrite /cffZ /cff prod_dblratZ_to_rat.
Qed.

(* ============================================================== *)
(*  Layer 2: binZ                                                   *)
(* ============================================================== *)

(* nat-level: k! * (n-k)! divides n! when k <= n.  Standard via
   bin_fact: 'C(n,k) * (k! * (n-k)!) = n!. *)
Lemma bin_dvd_fact (n k : nat) :
  (k <= n)%nat -> (k`! * (n - k)`! %| n`!)%nat.
Proof.
  move=> Hkn. apply/dvdnP. exists 'C(n,k).
  by rewrite -(bin_fact Hkn).
Qed.

(* Z-level lift: factZ k * factZ (n-k) divides factZ n. *)
Lemma factZ_factZ_dvd (n k : nat) :
  (k <= n)%nat ->
  (factZ k * factZ (n - k)%nat | factZ n)%Z.
Proof.
  move=> Hkn.
  rewrite !factZ_eq_Z_of_nat -Nat2Z.inj_mul.
  apply: Z_of_nat_dvd. exact: bin_dvd_fact.
Qed.

Lemma factZ_factZ_pos (n k : nat) :
  Z.lt 0 (factZ k * factZ (n - k)%nat).
Proof.
  apply: Z.mul_pos_pos; exact: factZ_pos.
Qed.

(* binQ n k = factQ n / (factQ k * factQ (n-k)) when k <= n. *)
Lemma binQ_factQ (n k : nat) :
  (k <= n)%nat ->
  binQ n k = factQ n / (factQ k * factQ (n - k)%nat).
Proof.
  move=> Hkn.
  have Hnz : factQ k * factQ (n - k)%nat != 0
    by rewrite mulf_neq0 ?factQ_neq0.
  apply: (canRL (mulfK Hnz)).
  rewrite /binQ /factQ -natrM -natrM.
  apply/eqP. rewrite Num.Theory.eqr_nat. apply/eqP.
  exact: bin_fact.
Qed.

(* Tiny reflection bridge between Stdlib's `Nat.leb` and mathcomp's
   `<=%N`.  Used in `binZ_to_rat`, where `binZ` is defined with
   `Nat.leb` (Stdlib bool) but the proof lives in mathcomp leq. *)
Lemma Nat_leb_leqP k n : reflect (k <= n)%N (Nat.leb k n).
Proof. by apply: (iffP idP) => [/Nat.leb_le/leP|/leP/Nat.leb_le]. Qed.

Lemma binZ_to_rat (n k : nat) :
  ((Z_to_int (binZ n k))%:~R : rat) = binQ n k.
Proof.
  rewrite /binZ.
  case: Nat_leb_leqP => Hkn.
  - rewrite Z_to_int_div_exact;
      [|exact: factZ_factZ_pos|exact: factZ_factZ_dvd Hkn].
    rewrite Z_to_int_mul intrM !factZ_to_rat.
    by rewrite -binQ_factQ.
  - rewrite Z_to_int_0 /=.
    have {}Hkn : (n < k)%N by rewrite ltnNge; apply/negP.
    rewrite /binQ (bin_small Hkn) /=.
    by rewrite mulr0n.
Qed.

(* ============================================================== *)
(*  Layer 3: compositionsZ <-> compositions                         *)
(* ============================================================== *)

(* The following three identities are definitional: mathcomp's
   `iota`, `flatten` and `[seq _ | _ <- _]` are conv-equal to
   Stdlib's `List.seq`, `List.concat` and `List.map`. *)
Lemma iota_seq_eq (m n : nat) : iota m n = List.seq m n.
Proof. exact: erefl. Qed.

Lemma flatten_concat T (s : seq (seq T)) :
  flatten s = List.concat s.
Proof. exact: erefl. Qed.

Lemma seq_map_eq T1 T2 (f : T1 -> T2) (l : seq T1) :
  [seq f x | x <- l] = List.map f l.
Proof. exact: erefl. Qed.

Lemma flat_map_concat_map T1 T2 (f : T1 -> list T2) (l : list T1) :
  List.flat_map f l = List.concat (List.map f l).
Proof. by elim: l => [|x l IH] //=; rewrite IH. Qed.

Lemma compositions_auxZ_eq (r remaining : nat) :
  compositions_auxZ r remaining = compositions_aux r remaining.
Proof.
  elim: r remaining => [|r IH] remaining /=.
  - case: (Nat.eqb_spec remaining 0) => [-> //|H].
    by have -> : (remaining == 0)%N = false by apply/eqP.
  - rewrite flat_map_concat_map -flatten_concat.
    rewrite -seq_map_eq -iota_seq_eq.
    congr (flatten _). apply: eq_map => a /=.
    by rewrite IH seq_map_eq.
Qed.

Lemma compositionsZ_eq_compositions (r n : nat) :
  compositionsZ r n = compositions r n.
Proof. exact: compositions_auxZ_eq. Qed.

(* ============================================================== *)
(*  Layer 4: G2Z <-> G_2                                            *)
(* ============================================================== *)

Lemma fold_left_Zadd_acc (xs : list Z) (acc : Z) :
  List.fold_left Z.add xs acc = Z.add acc (List.fold_left Z.add xs Z0).
Proof.
  elim: xs acc => [|x xs IH] acc /=.
  - by rewrite Z.add_0_r.
  - rewrite IH (IH (Z.add Z0 x)).
    by rewrite Z.add_0_l Z.add_assoc.
Qed.

Lemma fold_left_Zadd_sum (xs : list Z) :
  ((Z_to_int (List.fold_left Z.add xs Z0))%:~R : rat) =
  \sum_(z <- xs) ((Z_to_int z)%:~R).
Proof.
  elim: xs => [|x xs IH] /=.
  - rewrite big_nil. by [].
  - rewrite fold_left_Zadd_acc /=.
    rewrite Z_to_int_add intrD IH big_cons.
    by rewrite addrC.
Qed.

Lemma G2Z_to_rat (n k : nat) :
  ((Z_to_int (G2Z n k))%:~R : rat) = G_2 n k.
Proof.
  rewrite /G2Z /G_2.
  case: n => [|n].
  - by rewrite Z_to_int_1_rat.
  - rewrite Z_to_int_mul intrM factZ_to_rat.
    congr (_ * _).
    rewrite fold_left_Zadd_sum -seq_map_eq -iota_seq_eq big_map.
    apply: eq_big_seq => r Hr.
    rewrite Z_to_int_mul intrM binZ_to_rat.
    congr (_ * _).
    rewrite fold_left_Zadd_sum -seq_map_eq -compositionsZ_eq_compositions big_map.
    apply: eq_big_seq => a Ha.
    by rewrite cffZ_to_rat.
Qed.

(* ============================================================== *)
(*  Layer 5: qfrac calculus                                         *)
(*                                                                  *)
(*  Reads (n, d) : Z * Z as the rational n / d.  qmul / qplus on    *)
(*  the (Z * Z) side correspond to * / + on rat.                    *)
(* ============================================================== *)

Definition qfrac (p : Z * Z) : rat :=
  (Z_to_int p.1)%:~R / (Z_to_int p.2)%:~R.

Lemma qfrac_pair (a b : Z) :
  qfrac (a, b) = (Z_to_int a)%:~R / (Z_to_int b)%:~R.
Proof. by []. Qed.

Lemma qfrac_qmul (p q : Z * Z) :
  qfrac (qmul p q) = qfrac p * qfrac q.
Proof.
  case: p => [a b]; case: q => [c d].
  rewrite /qfrac /qmul /=.
  rewrite !Z_to_int_mul !intrM.
  by rewrite mulf_div.
Qed.

Lemma qfrac_qplus (p q : Z * Z) :
  Z_to_int p.2 != 0 -> Z_to_int q.2 != 0 ->
  qfrac (qplus p q) = qfrac p + qfrac q.
Proof.
  case: p => [a b]; case: q => [c d] /= Hb Hd.
  rewrite /qfrac /qplus /=.
  rewrite Z_to_int_add !Z_to_int_mul !intrD !intrM.
  by rewrite addf_div ?intr_eq0.
Qed.

(* ============================================================== *)
(*  Layer 6: alphaZ <-> alpha                                       *)
(* ============================================================== *)

Lemma alphaZ_to_rat (b c cp : nat) :
  qfrac (alphaZ b c cp) = alpha b c cp.
Proof.
  rewrite /qfrac /alphaZ /alpha /=.
  by rewrite !Z_to_int_mul !intrM !factZ_to_rat binZ_to_rat.
Qed.

(* ============================================================== *)
(*  Layer 7: M1 spec bridge                                         *)
(* ============================================================== *)

Lemma m1_num_den_to_rat (bi ci bj cj : nat) :
  qfrac (m1_num_den bi ci bj cj) = M1_entry bi ci bj cj.
Proof.
  rewrite /qfrac /m1_num_den /M1_entry.
  rewrite Z_to_int_mul intrM !factZ_to_rat G2Z_to_rat.
  by rewrite mulrAC.
Qed.

Lemma M1_spec_rat_eq (i j : nat) :
  M1_spec_ij i j = qfrac (m1_num_den_at i j).
Proof.
  rewrite /M1_spec_ij /m1_num_den_at.
  by rewrite m1_num_den_to_rat.
Qed.

(* ============================================================== *)
(*  Layer 8: M2 spec bridge                                         *)
(* ============================================================== *)

Lemma Z_to_int_factZ_neq0 (n : nat) : Z_to_int (factZ n) != 0.
Proof. apply: Z_to_int_pos_neq0. exact: factZ_pos. Qed.

Lemma Z_to_int_qplus_den_neq0 (a b : Z * Z) :
  Z_to_int a.2 != 0 -> Z_to_int b.2 != 0 ->
  Z_to_int (qplus a b).2 != 0.
Proof.
  case: a => [n d]; case: b => [n' d'] /= Hd Hd'.
  by rewrite Z_to_int_mul mulf_neq0.
Qed.

Lemma Z_to_int_qmul_den_neq0 (a b : Z * Z) :
  Z_to_int a.2 != 0 -> Z_to_int b.2 != 0 ->
  Z_to_int (qmul a b).2 != 0.
Proof.
  case: a => [n d]; case: b => [n' d'] /= Hd Hd'.
  by rewrite Z_to_int_mul mulf_neq0.
Qed.

Lemma Z_to_int_alphaZ_den_neq0 (b c cp : nat) :
  Z_to_int (alphaZ b c cp).2 != 0.
Proof. by rewrite /alphaZ /=; exact: Z_to_int_factZ_neq0. Qed.

Lemma Z_to_int_m2_term_den_neq0 bi ci bj cj cp1 cp2 :
  Z_to_int (m2_term_num_den bi ci bj cj cp1 cp2).2 != 0.
Proof.
  rewrite /m2_term_num_den.
  apply: Z_to_int_qmul_den_neq0.
  - apply: Z_to_int_qmul_den_neq0; exact: Z_to_int_alphaZ_den_neq0.
  - exact: Z_to_int_factZ_neq0.
Qed.

(* Bridge for one m2 term. *)
Lemma m2_term_to_rat (bi ci bj cj cp1 cp2 : nat) :
  qfrac (m2_term_num_den bi ci bj cj cp1 cp2) =
  let bp1 := (bi + 2 * ci - 2 * cp1 + 1)%N in
  let bp2 := (bj + 2 * cj - 2 * cp2 + 1)%N in
  let bsum := (bp1 + bp2)%N in
  let csum := (cp1 + cp2)%N in
  alpha bi ci cp1 * alpha bj cj cp2
    * factQ bsum / factQ (K2 + bsum + 2 * csum)%N
    * G_2 csum K2.
Proof.
  cbv zeta.
  rewrite /m2_term_num_den.
  cbv zeta.
  rewrite !qfrac_qmul !alphaZ_to_rat.
  rewrite qfrac_pair.
  rewrite Z_to_int_mul intrM factZ_to_rat factZ_to_rat G2Z_to_rat.
  rewrite -(_ : K2n = K2) //.
  by rewrite !mulrA mulrAC.
Qed.

(* Generic fold_left qplus -> sum bridge. *)
Lemma fold_left_qplus_qfrac (l : list (Z * Z)) (acc : Z * Z) :
  Z_to_int acc.2 != 0 ->
  (forall t, List.In t l -> Z_to_int t.2 != 0) ->
  qfrac (List.fold_left qplus l acc) =
  qfrac acc + \sum_(t <- l) qfrac t.
Proof.
  elim: l acc => [|t l IH] acc Hacc Hl /=.
  - by rewrite big_nil addr0.
  - have Ht : Z_to_int t.2 != 0 by apply: Hl; left.
    rewrite IH.
    + rewrite qfrac_qplus //.
      by rewrite big_cons addrA.
    + by apply: Z_to_int_qplus_den_neq0.
    + move=> t' Ht'. apply: Hl. by right.
Qed.

Lemma fold_left_qplus_den_neq0 (l : list (Z * Z)) (acc : Z * Z) :
  Z_to_int acc.2 != 0 ->
  (forall t, List.In t l -> Z_to_int t.2 != 0) ->
  Z_to_int (List.fold_left qplus l acc).2 != 0.
Proof.
  elim: l acc => [|x l IH] acc Hacc Hl //=.
  apply: IH.
  - apply: Z_to_int_qplus_den_neq0 => //. apply: Hl. by left.
  - move=> t Ht. apply: Hl. by right.
Qed.

Lemma fold_left_inner_to_map (T : Type) (l : list T) (g : T -> Z * Z) (acc : Z * Z) :
  List.fold_left (fun acc' x => qplus acc' (g x)) l acc =
  List.fold_left qplus (List.map g l) acc.
Proof. by elim: l acc => [|x l IH] acc //=; rewrite IH. Qed.

Lemma fold_left_pointwise_eq (T1 T2 : Type)
  (f g : T1 -> T2 -> T1) (l : list T2) (acc : T1) :
  (forall a x, f a x = g a x) ->
  List.fold_left f l acc = List.fold_left g l acc.
Proof.
  move=> Hfg. elim: l acc => [|x l IH] acc //=.
  by rewrite Hfg IH.
Qed.

Lemma qfrac_init : qfrac (Z0, Zpos xH) = (0 : rat).
Proof.
  rewrite /qfrac /=.
  by rewrite mul0r.
Qed.

(* Sum bridge for the inner row. *)
Lemma inner_row_sum (l : list nat) bi ci bj cj cp1 :
  \sum_(t <- List.map (m2_term_num_den bi ci bj cj cp1) l) qfrac t =
  \sum_(cp2 <- l) qfrac (m2_term_num_den bi ci bj cj cp1 cp2).
Proof. by rewrite -seq_map_eq big_map. Qed.

(* M2 outer fold bridge.  The outer accumulator is fed through the
   inner fold each iteration.  Total fold equals qfrac(acc) plus
   the double sum over (cp1, cp2). *)
Lemma m2_outer_qfrac (outer : list nat) (acc : Z * Z) bi ci bj cj :
  Z_to_int acc.2 != 0 ->
  qfrac (List.fold_left
    (fun acc' cp1 => List.fold_left qplus
      (List.map (m2_term_num_den bi ci bj cj cp1) (List.seq 0 (S cj)))
      acc')
    outer acc) =
  qfrac acc +
  \sum_(cp1 <- outer)
    \sum_(cp2 <- List.seq 0 (S cj))
      qfrac (m2_term_num_den bi ci bj cj cp1 cp2).
Proof.
  elim: outer acc => [|cp1 outer IH] acc Hacc /=.
  - by rewrite big_nil addr0.
  - have Hin : forall t,
      List.In t (List.map (m2_term_num_den bi ci bj cj cp1) (List.seq 0 (S cj))) ->
      Z_to_int t.2 != 0.
      move=> t /List.in_map_iff[cp2 [<- _]]. exact: Z_to_int_m2_term_den_neq0.
    have Hnext : Z_to_int (List.fold_left qplus
      (List.map (m2_term_num_den bi ci bj cj cp1) (List.seq 0 (S cj))) acc).2 != 0
      by apply: fold_left_qplus_den_neq0.
    have Hterm0 : Z_to_int (m2_term_num_den bi ci bj cj cp1 0).2 != 0
      by exact: Z_to_int_m2_term_den_neq0.
    have Hacc' : Z_to_int (qplus acc (m2_term_num_den bi ci bj cj cp1 0)).2 != 0
      by apply: Z_to_int_qplus_den_neq0.
    have Hrest : forall t : Z * Z,
        List.In t (List.map (m2_term_num_den bi ci bj cj cp1) (List.seq 1 cj)) ->
        Z_to_int t.2 != 0.
      move=> t Ht. apply: Hin. by right.
    rewrite IH //.
    rewrite fold_left_qplus_qfrac //.
    rewrite qfrac_qplus //.
    rewrite -!addrA.
    congr (qfrac acc + _).
    rewrite [in RHS]big_cons.
    rewrite [\sum_(cp2 <- (0%N :: _)) _]big_cons.
    rewrite !addrA.
    by rewrite inner_row_sum.
Qed.

Lemma m2_num_den_to_rat bi ci bj cj :
  qfrac (m2_num_den bi ci bj cj) = M2_entry bi ci bj cj.
Proof.
  rewrite /m2_num_den /M2_entry.
  rewrite (fold_left_pointwise_eq
    (g := fun acc' cp1 => List.fold_left qplus
      (List.map (m2_term_num_den bi ci bj cj cp1) (List.seq 0 (S cj)))
      acc'));
  last by move=> a x; rewrite fold_left_inner_to_map.
  rewrite m2_outer_qfrac; last by [].
  rewrite qfrac_init add0r -iota_seq_eq.
  apply: eq_big_seq => cp1 _.
  rewrite -iota_seq_eq.
  apply: eq_big_seq => cp2 _.
  by rewrite m2_term_to_rat.
Qed.

Lemma M2_spec_rat_eq (i j : nat) :
  M2_spec_ij i j = qfrac (m2_num_den_at i j).
Proof.
  rewrite /M2_spec_ij /m2_num_den_at.
  by rewrite m2_num_den_to_rat.
Qed.
