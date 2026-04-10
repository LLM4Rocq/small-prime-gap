(* ============================================================== *)
(*  PrimPoly.v                                                      *)
(*                                                                  *)
(*  Blazing-fast modular polynomial arithmetic on Uint63 primitives *)
(*  for CRT-based PRS verification.                                 *)
(*                                                                  *)
(*  Strategy: verify each PRS step modulo many small 63-bit primes  *)
(*  (all < 2^31 so products fit in 62 bits). Then CRT concludes    *)
(*  the identity holds over Z.                                      *)
(*                                                                  *)
(*  Convention: polynomials are LOW-TO-HIGH coefficient lists,       *)
(*  matching IntPoly.v.                                              *)
(* ============================================================== *)

From Stdlib Require Import Uint63 ZArith List Bool.
Import ListNotations.
Open Scope uint63_scope.

(* ---- Core type ---- *)

Definition mpol := list int.

(* ---- Modular arithmetic helpers ---- *)

Definition addmod (p a b : int) : int := Uint63.mod (Uint63.add a b) p.
Definition submod (p a b : int) : int := Uint63.mod (Uint63.add a (Uint63.sub p (Uint63.mod b p))) p.
Definition mulmod (p a b : int) : int := Uint63.mod (Uint63.mul a b) p.

(* Modular exponentiation: simple linear recursion.
   For the small exponents in PRS steps (typically 1-6), this is fine. *)
Fixpoint powmod (p base : int) (exp : nat) : int :=
  match exp with
  | O => Uint63.mod 1 p
  | S n' => mulmod p base (powmod p base n')
  end.

(* ---- Z-to-modular conversion ---- *)

(* Reduce a Z coefficient modulo a Uint63 prime.
   Z.modulo always returns a non-negative result when the divisor is positive. *)
Definition Z_to_mod (p : int) (z : Z) : int :=
  Uint63.of_Z (Z.modulo z (Uint63.to_Z p)).

(* Reduce a list-Z polynomial to a modular polynomial *)
Definition reduce_poly (p : int) (poly : list Z) : mpol :=
  List.map (Z_to_mod p) poly.

(* ---- List equality with padding ---- *)

(* Check that all elements of a list are zero *)
Fixpoint all_zero (l : list int) : bool :=
  match l with
  | [] => true
  | x :: xs => Uint63.eqb x 0 && all_zero xs
  end.

(* Compare two lists, treating missing elements as 0 *)
Fixpoint list_eqb_pad (l1 l2 : list int) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, [] => all_zero l1
  | [], _ => all_zero l2
  | x :: xs, y :: ys => Uint63.eqb x y && list_eqb_pad xs ys
  end.

(* ---- Modular polynomial operations ---- *)

(* Addition: pointwise addmod, with implicit zero-padding *)
Fixpoint mpol_add (p : int) (a b : mpol) : mpol :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | x :: xs, y :: ys => addmod p x y :: mpol_add p xs ys
  end.

(* Scaling: multiply every coefficient by c mod p *)
Definition mpol_scale (p : int) (c : int) (a : mpol) : mpol :=
  List.map (mulmod p c) a.

(* Multiplication by convolution:
   p(x) * q(x): for each coefficient of p, scale q and shift.
   Same structure as IntPoly.pmul but with modular ops. *)
Fixpoint mpol_mul (p : int) (a b : mpol) : mpol :=
  match a with
  | [] => []
  | x :: xs => mpol_add p (mpol_scale p x b) (0 :: mpol_mul p xs b)
  end.

(* Reduce all coefficients mod p (ensure canonical form) *)
Definition mpol_reduce (p : int) (a : mpol) : mpol :=
  List.map (fun x => Uint63.mod x p) a.

(* ---- PRS step checker (single prime) ---- *)

(* Leading coefficient: last element of polynomial list *)
Definition mpol_lead (a : mpol) : int :=
  List.last a 0.

(* Check one PRS step modulo prime p:
     lc(B)^d * A = Q * B + beta * C  (mod p)
   Returns true if the identity holds coefficient-by-coefficient. *)
Definition check_prs_step_mod (p : int) (A B Q : mpol) (d : nat)
    (beta : int) (C : mpol) : bool :=
  let lc_B := mpol_lead B in
  let lc_pow := powmod p lc_B d in
  let lhs := mpol_scale p lc_pow A in
  let rhs := mpol_add p (mpol_mul p Q B) (mpol_scale p beta C) in
  list_eqb_pad lhs rhs.

(* ---- Multi-prime checker ---- *)

Definition check_prs_step_all_primes
    (primes : list int) (A B Q : list Z) (d : nat) (beta : Z)
    (C : list Z) : bool :=
  List.forallb (fun p =>
    check_prs_step_mod p
      (reduce_poly p A) (reduce_poly p B) (reduce_poly p Q)
      d (Z_to_mod p beta) (reduce_poly p C)
  ) primes.

(* ============================================================== *)
(*  Sanity tests                                                    *)
(* ============================================================== *)

(* Basic modular arithmetic *)
Example addmod_test : addmod 97 50 60 = 13.
Proof. vm_compute. reflexivity. Qed.

Example mulmod_test : mulmod 97 50 60 = 90.
Proof. vm_compute. reflexivity. Qed.

Example submod_test : submod 97 10 30 = 77.
Proof. vm_compute. reflexivity. Qed.

Example powmod_test : powmod 97 3 4 = 81.
Proof. vm_compute. reflexivity. Qed.

Example powmod_test2 : powmod 97 3 5 = 49.
Proof. vm_compute. reflexivity. Qed.

(* Z_to_mod with negative values *)
Example z_to_mod_neg : Z_to_mod 97 (-6%Z) = 91.
Proof. vm_compute. reflexivity. Qed.

Example z_to_mod_pos : Z_to_mod 97 11%Z = 11.
Proof. vm_compute. reflexivity. Qed.

(* Polynomial multiplication *)
(* (1 + 2X) * (3 + 4X) = 3 + 10X + 8X^2, mod 97: [3; 10; 8] *)
Example mpol_mul_test :
  mpol_mul 97 [1; 2] [3; 4] = [3; 10; 8].
Proof. vm_compute. reflexivity. Qed.

(* ---- Toy PRS step mod 97 ---- *)
(* From PRSCheck.v:
   Step 0: 3^1 * [-6;11;-6;1] = [-2;1] * [11;-12;3] + 1 * [4;-2]
   LHS: 3 * [-6;11;-6;1] = [-18;33;-18;3]
   RHS: [-2;1]*[11;-12;3] + [4;-2]
      = [-22;35;-18;3] + [4;-2]
      = [-18;33;-18;3]   checkmark *)

Example toy_mod_97 :
  check_prs_step_mod 97
    (reduce_poly 97 [-6;11;-6;1]%Z)
    (reduce_poly 97 [11;-12;3]%Z)
    (reduce_poly 97 [-2;1]%Z)
    1%nat 1
    (reduce_poly 97 [4;-2]%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* Test with a different prime *)
Example toy_mod_101 :
  check_prs_step_mod 101
    (reduce_poly 101 [-6;11;-6;1]%Z)
    (reduce_poly 101 [11;-12;3]%Z)
    (reduce_poly 101 [-2;1]%Z)
    1%nat 1
    (reduce_poly 101 [4;-2]%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* Multi-prime check *)
Example toy_multi_prime :
  check_prs_step_all_primes
    [97; 101; 103; 107; 109]
    [-6;11;-6;1]%Z [11;-12;3]%Z [-2;1]%Z
    1%nat 1%Z [4;-2]%Z = true.
Proof. vm_compute. reflexivity. Qed.

(* Second toy step: (-2)^1 * [11;-12;3] = [-6;3] * [4;-2] + 1*[2] *)
Example toy_step1_mod_97 :
  check_prs_step_mod 97
    (reduce_poly 97 [11;-12;3]%Z)
    (reduce_poly 97 [4;-2]%Z)
    (reduce_poly 97 [-6;3]%Z)
    1%nat 1
    (reduce_poly 97 [2]%Z) = true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  Performance test: ~100-bit coefficients, 1000 primes            *)
(*                                                                  *)
(*  We reuse the same polynomial data from PRSCheck.v (perf_A etc)  *)
(*  and check the identity modulo 1000 small primes.                *)
(* ============================================================== *)

(* Generate a list of 1000 primes below 2^31.
   We use a precomputed list of the first 1000 primes starting from 5.
   For brevity, we generate them programmatically via a sieve-like filter. *)

(* Simple trial-division primality test — only used at compile time *)
Fixpoint is_prime_aux (n k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      let d := (k + 2)%nat in
      if Nat.ltb n (d * d)%nat then true
      else if Nat.eqb (Nat.modulo n d) 0 then false
      else is_prime_aux n k'
  end.

Definition is_prime_nat (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | 2 | 3 => true
  | _ => if Nat.eqb (Nat.modulo n 2) 0 then false
         else is_prime_aux n (n - 2)%nat
  end.

(* Collect primes in a range *)
Fixpoint collect_primes (start count remaining : nat) : list nat :=
  match remaining with
  | O => []
  | S r =>
      match count with
      | O => []
      | _ =>
          if is_prime_nat start then
            start :: collect_primes (S start) (Nat.pred count) r
          else
            collect_primes (S start) count r
      end
  end.

(* Generate 1000 primes starting from 1000000007 — all well below 2^31.
   Actually, let's use small primes starting from 3 for speed of generation. *)
Definition prime_nats : list nat := collect_primes 3 1000 10000.

Definition test_primes : list int :=
  List.map (fun n => Uint63.of_Z (Z.of_nat n)) prime_nats.

(* Verify we got 1000 primes *)
Example got_1000_primes : List.length test_primes = 1000%nat.
Proof. vm_compute. reflexivity. Qed.

(* Performance polynomials (same data as PRSCheck.v) *)
Open Scope Z_scope.

Definition perf_A : list Z :=
  [809966202255178340048122171991; 715414241776024469301004276121; 1152368987556820949052656898953; 997424387602804228764386380768; 1164506576876531178671618796477; 883828142908806997456337938550; 739721230364895400087815711331; 1037628773726368420922090467601; 998570054203939489488175457299; 1246237746326720195039762314623; 994475115162150704487823024403; 917252337714282519858150691521; 1210445775716381550775052745424; 821186608246337721937317082927; 929277164332700316486675185153; 980801507851122182885779750639; 1084206841911773143245962625593; 695306347659476886487749174437; 734266080783625157565191653372; 896441138248459566815093825774; 828635614382951791821626264165].

Definition perf_B : list Z :=
  [1228791269573460165506476449776; 841993022085797371758395914037; 992658707519561023102199648153; 770154928466323009254487780240; 1080748338392614716360344119240; 826727277469879707656036200169; 1042075287410553213178630994119; 1214104726699003203594637114065; 1103576888948019817877081976194; 876099092503422002244749967103; 788078527543045282958407974072; 835841553814127752057138715422; 1133890984442475253416954077919; 1081454757100765759641091185598; 1229429020680009337623252784033; 730855820006717687282062205335].

Definition perf_Q : list Z :=
  [1112217120237894313622503749682; 1056285525905047779140306241916; 804931383821503981645109287247; 639361523633932584437107410755; 748573168096554221631581580100; 1181383059037322530695226046597].

Definition perf_R : list Z :=
  [168898365170154420223172818724078753261542309745835306931003070101067293587498789425723519677271850796864580293763201532621112505673822824201109203572230950274771799927922329269393; 149181898601428477065506918618716139718892881932934144259584061759041823468776895334828481168644559921869647416344526826292054550256989352691651672566766324777261298132653591112325; 240297974815761808198542592284152242545158286548479297132051903269880439590432322837460579280887356346199330280590217686222015062232559738851554290289654958409567628107732168040465; 207988120958511314014653440803770257998137881368247987043267311839890879379856241852753181408481139142396923066798801217719903059323899707308759611756751948490617966128151070708153; 242828968068934524994202043394352641180213049259062169368553484591798707094025596960252866332216292709074330104504312205056359150541209987306507792273028687075240926315097463295029; 184300441195003875668170879255456993233565352504022184860783007377875090688531441362516936953395192136561368149091149717635628084804867137479217240960139572041176256426771723235385; 154250518283878507245566687321042112917514717443968221001515348840567906617124740027041283702755115685901022029259325148106379186417377736578558210244323492596127484036009379098294; 216371748658078355750684677379445582563394989985903443506587708859251697178078421753393038768173057988010596050281173997812567053180259331950429959122014859878890589669502976984757; 208227021316850995352991424271215575743421133816587975580478731639733481936236194370237189399913088275579034571144354596374645785076725270900413520536733924807167217412596023799009; 259871976610706724679616926387642352342498937316874955429474114689283932702611380386370076111764813399576929832408835995889556205163582816475669580161917474873664450704056074714595; 207373123329868486458734838675880336925654560784778952723488620235456177094148733411153942142439318860553942434125552110145872578872945153595761792474968534538654325098703139294887; 191270228136799065052434526328885395646026541474228891151958672558056614481372723515533060563194925694413154937010002128186194191664265056912490684067306278467475605049956921915165; 252408448743157653208201365610338331763913251468883373870250297842264548866275018429688399708249387027942153768155131106991171486488396915030672003634666113719521716830264006770936; 171238102585340017586943345824539650719875377032174063427670122507656039039359757669305485282428230551611659771784106046166564851026008527743276088481101694323785745527713520203273; 193777707525013670716945786144878005776413162735469841419337606172028926166853872124282282343038590569847557552141280536792970081226888473660792019564512851801491168403883600802807; 204521831616237452006210421260682201662774822396480144303107973198895467289419363192341814891524766517654148163096976741811500707089829826523098500122374163937724461853016545362192; 226084449691028824125921867365292400805857849606303235485611138731532058253180309384012750698645269931515202705035751456462937531281034735179437353269639689375430093560309625323040; 144988895938053777650933472284979466118774704640304724359801914171938087316938754157271637522878819178208187096037999029574962685282069677429237120758038892483012029010986145092772; 153112982120678302739272654322882277271131850570076460502345122435826569698144148506220029806916839131789348432479585934957775094882541143956538885091318705867076481080514660031269; 186930568584066146689675946365699625249292567107217715940528923510863519490893107997903025602720290834765257279504946813044098347812041063403771274405547282830104514762766045262049; 172791408087611079559246282889718389613037138298686939871477388794474577878626647683353793729949183711894604824757022108330007520775751166749977022010195741415027727778856444426880].

Close Scope Z_scope.
Open Scope uint63_scope.

(* Performance test: check the PRS step modulo 1000 primes.
   Step: lc(B)^d * A = Q * B + 1 * R where d = len(A) - len(B) = 21 - 16 = 5 *)
Example perf_1000_primes :
  check_prs_step_all_primes test_primes perf_A perf_B perf_Q 5%nat 1%Z perf_R = true.
Proof. vm_compute. reflexivity. Qed.
