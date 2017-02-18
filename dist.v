Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(** Discrete distributions *)

Section Dist.
  Variable T : finType.
  Variable rty : numDomainType.

  Definition dist_axiom (f : {ffun T -> rty}) :=
    [&& \sum_t (f t) == 1
      & [forall t : T, f t >= 0]].
  Record dist : Type := mkDist { pmf :> {ffun T -> rty}; dist_ax : dist_axiom pmf }.
  Canonical dist_subType := [subType for pmf].

  (* We have eqType and choiceTypes on distributions:*)
  Definition dist_eqMixin := Eval hnf in [eqMixin of dist by <:].
  Canonical dist_eqType := Eval hnf in EqType dist dist_eqMixin.
  Definition dist_choiceMixin := [choiceMixin of dist by <:].
  Canonical dist_choiceType := Eval hnf in ChoiceType dist dist_choiceMixin.
End Dist.

Section distLemmas.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Lemma dist_normalized : \sum_t d t = 1.
  Proof. by case: (andP (dist_ax d)); move/eqP. Qed.

  Lemma dist_positive : forall t : T, d t >= 0.
  Proof. by case: (andP (dist_ax d))=> _; move/forallP. Qed.
End distLemmas.

Section support.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition support : {set T} := [set t : T | 0 < d t].

  Lemma in_support x : x \in support -> 0 < d x.
  Proof. by rewrite /support in_set. Qed.
End support.

Section bind.
  Variable T U : finType.
  Variable rty : numDomainType.  
  Variable d : {ffun T -> rty}.
  Variable f : T -> {ffun U -> rty}.
  Definition bind : {ffun U -> rty} :=
    finfun (fun u : U => \sum_(t : T) (d t) * (f t u)).
End bind.

Lemma sum_ffunE'
      (aT : finType) (rty : numDomainType) (g : aT -> rty) :
  \sum_t [ffun x => g x] t =
  \sum_t g t.
Proof. by apply: eq_big=> // i _; rewrite ffunE. Qed.

Lemma sum_ffunE''
      (aT : finType) (rty : numDomainType) (g : aT -> rty)
      (pred : aT -> bool) :
  \sum_(t | pred t)[ffun x => g x] t =
  \sum_(t | pred t) g t.
Proof. by apply: eq_big=> // i _; rewrite ffunE. Qed.

Lemma sum_exchange (A B : finType) (rty : numDomainType)
      (f : {ffun A -> B}) (g : A -> rty) :
  \sum_b \sum_(a | f a == b) g a = \sum_(a : A) g a.
Proof.
  have ->: (\sum_b \sum_(a | f a == b) g a =
            \sum_b \sum_a if f a == b then g a else 0).
  { by apply eq_big => // i _; rewrite big_mkcond. }
  rewrite exchange_big /=.
  have ->: (\sum_j \sum_i (if f j == i then g j else 0) = \sum_j g j).
  { apply eq_big => // i _; rewrite -big_mkcond /=.
    have ->: (\sum_(i0 | f i == i0) g i = \sum_(i0 | i0 == f i) g i).
    { by apply eq_big. }
    by rewrite big_pred1_eq. }
  by [].
Qed.

(* Lemma sum_exchange_ffun (A B : finType) (rty : numDomainType) *)
(*       (f : {ffun A -> B}) (g : {ffun A -> rty}) : *)
(*   \sum_b \sum_(a | f a == b) g a = \sum_(a : A) g a. *)
(* Proof. *)
(*   have ->: (\sum_b \sum_(a | f a == b) g a = *)
(*             \sum_b \sum_a if f a == b then g a else 0). *)
(*   { by apply eq_big => // i _; rewrite big_mkcond. } *)
(*   rewrite exchange_big /=. *)
(*   have ->: (\sum_j \sum_i (if f j == i then g j else 0) = \sum_j g j). *)
(*   { apply eq_big => // i _; rewrite -big_mkcond /=. *)
(*     have ->: (\sum_(i0 | f i == i0) g i = \sum_(i0 | i0 == f i) g i). *)
(*     { by apply eq_big. } *)
(*     by rewrite big_pred1_eq. } *)
(*   by []. *)
(* Qed. *)

Section mapDist.
  Variable U T : finType.
  Variable rty : numDomainType.
  Variable d : dist U rty.
  Variable f : {ffun U -> T}.

  Definition map_pmf := finfun (fun x : T => \sum_(u | f u == x) d u).

  Lemma map_pmf_dist : dist_axiom map_pmf.
  Proof.
    rewrite /dist_axiom. apply /andP. split.
    { rewrite /map_pmf. destruct d => /=. rewrite /dist_axiom in dist_ax0.
      move: dist_ax0 => /andP [dist_ax0 dist_ax1].
      by rewrite sum_ffunE' sum_exchange. }
    { rewrite /map_pmf. apply /forallP => x. rewrite ffunE.
      apply sumr_ge0 => u H. apply dist_positive. }
  Qed.

  Definition map_dist := mkDist map_pmf_dist.
End mapDist.

Section prob.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition probOf (p : pred T) :=
    \sum_(t : T | p t) d t.

  Lemma probOf_0_1 (p : pred T) :
    0 <= probOf p <= 1.
  Proof.
    move: d.(dist_ax). rewrite /dist_axiom => d_ax.
    apply Bool.andb_true_iff in d_ax. destruct d_ax as [d_ax0 d_ax1].
    rewrite /probOf. apply /andP. split.
    - by apply sumr_ge0 => i H; move: d_ax1 => /forallP.
    - move: d_ax0 => /eqP => d_ax0.
      have H: (\sum_(t | p t) d t =
               \sum_t d t - \sum_(t | ~~ p t) d t).
      { rewrite [\sum_(t | ~~ p t) d t]big_mkcond /=.
        rewrite -sumrB big_mkcond /=.
        apply eq_big => // i _.
        case: (p i) => /=.
        - by rewrite subr0.
        - by rewrite subrr. }
      rewrite d_ax0 in H. rewrite H.
      have ->: (1 = 1 - 0) by move=> t; rewrite subr0.
      apply ler_sub. by rewrite subr0.
      apply sumr_ge0 => i H0. by move: d_ax1 => /forallP.
  Qed.      
End prob.

Section expectedValue.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.

  Definition expectedCondValue (f : T -> rty) (p : pred T) :=
    \sum_(t : T | p t) (d t) * (f t).

  Lemma expectedCondValue_mull f p c :
    expectedCondValue (fun t => c * f t) p = c * expectedCondValue f p.
  Proof.                                               
    rewrite /expectedCondValue mulr_sumr; apply/congr_big=> //= i _.
    by rewrite mulrA [d i * c]mulrC -mulrA.
  Qed.

  Lemma expectedCondValue_linear f g p :
    expectedCondValue (fun t => f t + g t) p =
    expectedCondValue f p + expectedCondValue g p.
  Proof.
    rewrite /expectedCondValue.
    have H: \sum_(t | p t) d t * (f t + g t) =
            \sum_(t | p t) (d t * f t + d t * g t).
    { by apply/congr_big=> //= i _; rewrite mulrDr. }
    by rewrite H -big_split.
  Qed.    
    
  Definition expectedValue (f : T -> rty) :=
    expectedCondValue f xpredT.

  Lemma expectedValue_mull f c :
    expectedValue (fun t => c * f t) = c * expectedValue f.
  Proof. by apply: expectedCondValue_mull. Qed.

  Lemma expectedValue_linear f g :
    expectedValue (fun t => f t + g t) =
    expectedValue f + expectedValue g.
  Proof. by apply: expectedCondValue_linear. Qed.      
  
  Lemma expectedValue_const c : expectedValue (fun _ => c) = c.
  Proof.
    rewrite /expectedValue /expectedCondValue -mulr_suml.
    by case: (andP (dist_ax d)); move/eqP=> ->; rewrite mul1r.
  Qed.

  Lemma expectedValue_range f
        (H : forall x : T, 0 <= f x <= 1) :
    0 <= expectedValue f <= 1.
  Proof.      
    rewrite /expectedValue /expectedCondValue; apply/andP; split.
    apply: sumr_ge0=> i _; case H2: (f i == 0).
    { by move: (eqP H2)=> ->; rewrite mulr0. }
    { rewrite mulrC pmulr_rge0; first by apply: dist_positive.
      case: (andP (H i))=> H3 _.
      rewrite lt0r; apply/andP; split=> //.
      by apply/eqP=> H4; rewrite H4 eq_refl in H2. }
    rewrite -(@dist_normalized T rty d); apply: ler_sum.
    move=> i _; case H2: (d i == 0).
    { by move: (eqP H2)=> ->; rewrite mul0r. }
    rewrite mulrC ger_pmull; first by case: (andP (H i)).
    have H3: 0 <= d i by apply: dist_positive.
    rewrite ltr_def; apply/andP; split=> //.
    by apply/eqP=> H4; rewrite H4 eq_refl in H2.
  Qed.    
End expectedValue.

(* Section cdf. *)
(*   Variable T : finType. *)
(*   Variable rty : numDomainType. *)
(*   Variable d : dist T rty. *)

(*   Fixpoint cdf_aux (x : T) (l : seq T) : rty := *)
(*     if l is [:: y & l'] then *)
(*       if x == y then d y *)
(*       else d x + cdf_aux x l' *)
(*     else 0. *)

(*   Definition cdf (x : T) : rty := cdf_aux x (enum T). *)

(*   Fixpoint inverse_cdf_aux (p acc : rty) (cand : option T) (l : seq T) *)
(*     : option T := *)
(*     if l is [:: y & l'] then *)
(*       if acc > p then cand *)
(*       else inverse_cdf_aux p (acc + d y) (Some y) l' *)
(*     else cand. *)

(*   Definition inverse_cdf (p : rty) : option T := *)
(*     inverse_cdf_aux p 0 None (enum T). *)
(* End cdf. *)

Section cdf.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable d : dist T rty.
  
  Definition cdf (x : T) :=
    (* \sum_(y : T | (enum_rank y <= enum_rank x)%N) d y. *)
    \sum_(i : 'I_#|T| | (nat_of_ord i <= enum_rank x)%N) d (enum_val i).

  (* Maybe this should just be the definition of cdf. *)
  Lemma cdf_probOf x :
    cdf x = probOf d (fun y => (enum_rank y <= enum_rank x)%N).
  Proof.
    rewrite /probOf. rewrite /cdf. 
  Admitted.

  Lemma cdf_0_1 x :
    0 <= cdf x <= 1.
  Proof. rewrite cdf_probOf. apply probOf_0_1. Qed.

  Lemma inverse_cdf_lt_i_n pred :
    (\max_(x : T | pred x) (#|T| - enum_rank x - 1) < #|T|)%N.
  Admitted.

  (* This is weird. Maybe the fixpoint is a better idea. *)
  Definition inverse_cdf (u : {r : rty | 0 <= r <= 1}) : T :=
    (* (\max_(x | proj1_sig u <= cdf x) (1 - enum_rank x))%:R. *)
    (* \max_(x | proj1_sig u <= cdf x) (#|T| - 1 - enum_rank x) *)
    enum_val (Ordinal (inverse_cdf_lt_i_n (fun x => proj1_sig u <= cdf x))).

  (* Definition inverse_cdf := *)
  (*   finfun (fun u : [finType of {r : rty | 0 <= r <= 1}] => enum_val (Ordinal (inverse_cdf_lt_i_n (fun x => proj1_sig u <= cdf x)))). *)

  Lemma cdf_inverse_cdf u :
    cdf (inverse_cdf u) = proj1_sig u.
  Admitted.

  Lemma inverse_cdf_cdf (x : T) :
    inverse_cdf (@exist rty _ (cdf x) (cdf_0_1 x)) = x.
  Proof.
    rewrite /inverse_cdf /=.
  Admitted.

  (* Lemma inverse_cdf_le_rank (x : T) : *)
  (*   (enum_rank (inverse_cdf (exist (fun u => (0 <= u <= 1)%R) *)
  (*                                  (cdf x) (cdf_0_1 x))) *)
  (*    <= enum_rank x)%N. *)
  (* Admitted. *)
End cdf.

Section cdfLemmas.
  Variable T : finType.
  Variable rty : numDomainType.

  Lemma cdf_equiv_pmf (dA dB : dist T rty) :
    (forall x, cdf dA x = cdf dB x) -> (forall x, dA x = dB x).
  Proof.
    move => H x. specialize (H x).
    rewrite 2!cdf_probOf in H. rewrite /probOf in H.
    
  Admitted.

  (* (* I think this is true. If we can show that it's possible to drive *)
  (*    the cdf difference to below any epsilon, then it can be shown for *)
  (*    the pmf difference as well, which implies the same for the *)
  (*    "statistical difference" between the distributions. *) *)
  (* Lemma cdf_equiv_eps (dA dB : dist T rty) x eps : *)
  (*   cdf dA x - cdf dB x <= eps -> *)
  (*   dA x - dB x <= 2%:R * eps. *)
  (* Proof. *)
  (*   move=> H. rewrite 2!cdf_probOf in H. rewrite /probOf in H. *)
  (* Admitted. *)
End cdfLemmas.

(** Product distributions *)

Lemma prod_distr_sum
      (I J : finType) (rty : numDomainType) (F : I -> J -> rty) :
  \prod_i (\sum_j F i j) =
  \sum_(f : {ffun I -> J}) \prod_i F i (f i).
Proof. by apply: bigA_distr_bigA. Qed.

Section product.
  Variable T : finType.
  Variable rty : numDomainType.
  Variable n : nat.
  Variable f : {ffun 'I_n -> dist T rty}.

  Notation type := ({ffun 'I_n -> T}).
  
  Definition prod_pmf : {ffun type -> rty} :=
    finfun (fun p : type => \prod_(i : 'I_n) f i (p i)).

  Lemma prod_pmf_dist :
    dist_axiom (T:=[finType of type]) (rty:=rty) prod_pmf.
  Proof.
    apply/andP; split.
    { rewrite /prod_pmf sum_ffunE'.
      rewrite -(@prod_distr_sum _ _ rty (fun x y => f x y)).
      have H: \prod_(i<n) (\sum_j (f i) j) = \prod_(i<n) 1.
      { apply: congr_big => // i _.
        by rewrite dist_normalized. }
      by rewrite H prodr_const expr1n. }
    apply/forallP => x; rewrite /prod_pmf ffunE.
    by apply: prodr_ge0 => i _; apply: dist_positive.
  Qed.    
  
  Definition prod_dist : dist [finType of type] rty :=
    @mkDist _ _ prod_pmf prod_pmf_dist.
End product.
  
Section uniform.
  Variable T : finType.
  Variable t0 : T.
  Notation rty := rat.
  
  Definition uniform_dist : {ffun T -> rty} :=
    finfun (fun _ => 1 / #|T|%:R).

  Lemma itern_addr_const n (r : rty) : iter n (+%R r) 0 = r *+ n.  
  Proof. by elim: n r=> // n IH r /=; rewrite IH mulrS. Qed.

  Lemma ffun_lem (r : rty) :
            \sum_(t : T) [ffun => r / #|T|%:R] t
          = \sum_(t : T) r / #|T|%:R.
  Proof. by apply/congr_big=> // i _; rewrite ffunE. Qed.
  
  Lemma uniform_normalized : dist_axiom uniform_dist.
  Proof.
    rewrite /dist_axiom ffun_lem; rewrite big_const itern_addr_const.
    have Hgt0: (#|T| > 0)%N.
    { move: (@enumP T); move/(_ t0)=> H; rewrite cardT.
      move: (mem_enum T t0); rewrite /in_mem /=.
        by case: (enum T).
    }
    have H: #|T| != 0%N.
    { by apply/eqP=> H; rewrite H in Hgt0.
    }
    apply/andP; split.    
    { move: #|T| H=> n.
      rewrite div1r -[_ *+ n]mulr_natl; move/eqP=> H.
      apply/eqP; apply: mulfV=> //; apply/eqP=> H2; apply: H.
      suff: n == 0%N; first by move/eqP=> ->.
      by erewrite <-pnatr_eq0; apply/eqP; apply: H2.
    }
    apply/forallP=> t; rewrite /uniform_dist ffunE.
    apply: divr_ge0=> //. 
    by apply: ler0n.
  Qed.

  Definition uniformDist : dist T [numDomainType of rat] :=
    mkDist uniform_normalized.

  Lemma expectedValue_uniform (f : T -> rty) :
    expectedValue uniformDist f = (\sum_(t : T) (f t)) / #|T|%:R.
  Proof.
    rewrite /expectedValue /uniformDist /= /uniform_dist.
    rewrite mulr_suml; apply/congr_big=> // t _; rewrite ffunE.
    by rewrite -mulrA mul1r mulrC.
  Qed.      
End uniform.
