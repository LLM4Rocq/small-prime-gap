(* ============================================================== *)
(*  CRTCheck.v                                                      *)
(*                                                                  *)
(*  CRT (Chinese Remainder Theorem) helper lemmas: lifting modular  *)
(*  agreement over a list of distinct primes to an identity over Z. *)
(*                                                                  *)
(*  Standalone: depends only on the Stdlib (no Uint63, no project   *)
(*  imports).  Provides the reusable [crt_reconstruct] theorem.     *)
(* ============================================================== *)

From Stdlib Require Import ZArith List Bool Lia Znumtheory.
Import ListNotations.

Local Open Scope Z_scope.

(* --- Arithmetic helpers ---------------------------------------- *)

(* A multiple of P that is smaller than P/2 in absolute value
   must be zero. *)
Lemma small_multiple_zero : forall c P : Z,
  (P | c)%Z -> (0 < P)%Z -> (2 * Z.abs c < P)%Z -> c = 0%Z.
Proof.
  intros c P [k Hk] HP Hlt. subst c.
  rewrite Z.abs_mul in Hlt.
  assert (Z.abs k = 0)%Z by nia. lia.
Qed.

(* If a | n and b | n and gcd(a,b) = 1, then a*b | n. *)
Lemma coprime_div_mul : forall a b n : Z,
  (a | n)%Z -> (b | n)%Z -> rel_prime a b -> (a * b | n)%Z.
Proof.
  intros a b n [j Hj] Hb Hrel. subst n.
  assert (Hbj : (b | j)%Z).
  { apply Gauss with (b := a).
    rewrite Z.mul_comm. exact Hb.
    exact (rel_prime_sym _ _ Hrel). }
  destruct Hbj as [m Hm]. subst j.
  exists m. ring.
Qed.

(* --- CRT product helpers --------------------------------------- *)

(* fold_left Z.mul can be factored: fold(l, a) = a * fold(l, 1). *)
Local Lemma fold_left_mul_assoc : forall (l : list Z) (a : Z),
  fold_left Z.mul l a = (a * fold_left Z.mul l 1)%Z.
Proof.
  induction l as [|x l IHl]; intros a.
  - simpl. lia.
  - cbn [fold_left].
    rewrite IHl. rewrite (IHl (Z.mul 1 x)). nia.
Qed.

(* Product of positive numbers is positive. *)
Local Lemma fold_left_mul_pos (l : list Z) (acc : Z) :
  (0 < acc)%Z ->
  (forall z, In z l -> (0 < z)%Z) ->
  (0 < fold_left Z.mul l acc)%Z.
Proof.
  revert acc. induction l as [|z l IH]; intros acc Hacc Hall; simpl.
  - exact Hacc.
  - apply IH.
    + apply Z.mul_pos_pos; [exact Hacc | apply Hall; left; reflexivity].
    + intros z' Hz'. apply Hall. right. exact Hz'.
Qed.

(* A prime p cannot divide a different prime q. *)
Lemma prime_not_divide_other_prime : forall p q : Z,
  prime p -> prime q -> p <> q -> ~ (p | q)%Z.
Proof.
  intros p q Hp Hq Hneq Hdiv.
  assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
  assert (Hq1 : (1 < q)%Z) by (destruct Hq; lia).
  destruct Hdiv as [k Hk].
  assert (Hk_pos : (0 < k)%Z) by nia.
  assert (Hlt : (p < q)%Z \/ p = q) by nia.
  destruct Hlt as [Hlt | Hlt]; [| lia].
  assert (Hrange : (1 <= p < q)%Z) by lia.
  destruct Hq as [_ Hq2]. specialize (Hq2 _ Hrange).
  destruct Hq2 as [_ _ Hgcd].
  assert (Hdivpq : (p | q)%Z) by (exists k; lia).
  assert (Hdivpp : (p | p)%Z) by (exists 1%Z; lia).
  specialize (Hgcd _ Hdivpp Hdivpq).
  destruct Hgcd as [m Hm].
  assert (m = 0 \/ m >= 1 \/ m <= -1)%Z by lia.
  destruct H as [H|[H|H]]; nia.
Qed.

(* A prime p that does not appear in a list of primes qs cannot
   divide the product of qs. *)
Lemma prime_not_divide_prime_product : forall (p : Z) (qs : list Z),
  prime p ->
  (forall q, In q qs -> prime q) ->
  ~ In p qs ->
  ~ (p | fold_left Z.mul qs 1)%Z.
Proof.
  induction qs as [|q qs IHqs]; intros Hp Hprimes Hnotin Hdiv.
  - simpl in Hdiv. destruct Hdiv as [k Hk].
    assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
    assert (k = 0 \/ k >= 1 \/ k <= -1)%Z by lia.
    destruct H as [H|[H|H]]; nia.
  - cbn [fold_left] in Hdiv. rewrite fold_left_mul_assoc in Hdiv.
    assert (Hpq : p <> q) by (intro; subst; apply Hnotin; left; reflexivity).
    assert (Hprime_q : prime q) by (apply Hprimes; left; reflexivity).
    apply prime_mult in Hdiv; [| exact Hp].
    destruct Hdiv as [Hdiv | Hdiv].
    + rewrite Z.mul_1_l in Hdiv.
      exact (prime_not_divide_other_prime p q Hp Hprime_q Hpq Hdiv).
    + apply IHqs; auto.
      * intros r Hr. apply Hprimes. right. exact Hr.
      * intro. apply Hnotin. right. exact H.
Qed.

(* If all primes in a NoDup list divide c, then their product divides c. *)
Lemma all_primes_divide_product : forall (ps : list Z) (c : Z),
  NoDup ps ->
  (forall p, In p ps -> prime p) ->
  (forall p, In p ps -> (p | c)%Z) ->
  (fold_left Z.mul ps 1 | c)%Z.
Proof.
  induction ps as [|p ps IHps]; intros c Hnd Hprimes Hdivs.
  - simpl. exists c. lia.
  - cbn [fold_left]. rewrite fold_left_mul_assoc. rewrite Z.mul_1_l.
    apply coprime_div_mul.
    + apply Hdivs. left. reflexivity.
    + apply IHps.
      * inversion Hnd; assumption.
      * intros q Hq. apply Hprimes. right. exact Hq.
      * intros q Hq. apply Hdivs. right. exact Hq.
    + apply prime_rel_prime.
      * apply Hprimes. left. reflexivity.
      * apply prime_not_divide_prime_product.
        -- apply Hprimes. left. reflexivity.
        -- intros q Hq. apply Hprimes. right. exact Hq.
        -- inversion Hnd; assumption.
Qed.

(* --- Boolean NoDup check for list Z ---------------------------- *)

Fixpoint nodup_Z (l : list Z) : bool :=
  match l with
  | nil => true
  | x :: rest => negb (existsb (Z.eqb x) rest) && nodup_Z rest
  end.

Lemma nodup_Z_sound (l : list Z) : nodup_Z l = true -> NoDup l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
  constructor.
  - intro Hin. apply negb_true_iff in H1.
    assert (Hex : existsb (Z.eqb a) l = true).
    { apply existsb_exists. exists a.
      split; [exact Hin | apply Z.eqb_refl]. }
    rewrite Hex in H1. discriminate.
  - exact (IH H2).
Qed.

(* ================================================================ *)
(*  Reusable CRT reconstruction theorem                              *)
(*                                                                  *)
(*  If every prime in a NoDup list divides (c - d), and twice the    *)
(*  absolute value of (c - d) is below the product of those primes,  *)
(*  then c = d.  Packaged as the reusable CRT reconstruction step    *)
(*  for downstream det-equality checks.                              *)
(* ================================================================ *)

Lemma crt_reconstruct (c d : Z) (ps : list Z) :
  NoDup ps ->
  (forall p, In p ps -> prime p) ->
  (forall p, In p ps -> (p | (c - d))%Z) ->
  (2 * Z.abs (c - d) < fold_left Z.mul ps 1%Z)%Z ->
  c = d.
Proof.
  intros Hnd Hprimes Hdiv Hbound.
  cut ((c - d)%Z = 0%Z); [lia|].
  apply (small_multiple_zero _ (fold_left Z.mul ps 1%Z)).
  - apply all_primes_divide_product; assumption.
  - apply fold_left_mul_pos; [lia|].
    intros z Hz. assert (Hprime_z : prime z) by (apply Hprimes; exact Hz).
    destruct Hprime_z; lia.
  - exact Hbound.
Qed.
