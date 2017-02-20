Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Require Import dist statdiff.

Lemma ler_mull2 (rty : realFieldType) (x y z : rty) (Hgt0 : 0 < z) :
  z * x <= z * y -> x <= y.
Proof.
   move=> H. rewrite -ler_pdivr_mull in H=> //. rewrite mulrA in H.
  rewrite [z^(-1) * _]mulrC divff in H=> //. rewrite mul1r in H.
  apply H. 
  apply/eqP=> H2; rewrite H2 in Hgt0.
  by move: (ltr0_neq0 Hgt0); move/eqP.
Qed.

(* I think it actually won't work quite like this. Maybe it just needs
   to be a distribution over nats along with a valuation function that
   turns them into rationals in [0, 1] by dividing by N-1. *)
Section standardUniform.
  Variable N : nat.
  Variable pf_N : (1 < N)%N.

  Definition n_weaken n (x : {y : nat | (y < n)%N}) : {y : nat | (y < n.+1)%N}.
  Proof.
    destruct x.
    apply (@exist _ _ x (leqW i)).
  Defined.

  Fixpoint n_weaken_list n (l : seq {x : nat | (x < n)%N})
    : seq {x : nat | (x < n.+1)%N} :=
    match l with
    | nil => nil
    | h :: t => n_weaken h :: (n_weaken_list t)
    end.

  Definition n_list n : seq {x : nat | (x < n)%N}.
  Proof.
    induction n.
    - apply nil.
    - apply ((@exist _ _ n%N (ltnSn n)) :: (n_weaken_list IHn)).
  Defined.

  Lemma n_norm_bounds n (x : {x : nat | (x < n)%N}) (pf_n : (1 < n)%N) :
    0 <= (proj1_sig x)%:Q / (n%:Q-1) <= 1.
  Proof.
    destruct x=> /=.
    apply /andP. split.
    - apply mulr_ge0.
      + apply ler0n.
      + rewrite invr_ge0 subr_ge0.
        have ->: (1 = 1%N%:R) by [].
        have ->: (1%:R *~ n = n%:R). by [].
        rewrite ler_nat. auto.
    - apply ler_mull2 with (z:=(n%:R-1)).
      { rewrite subr_gt0. have ->: (1 = 1%N%:R) by [].
        rewrite -[1%:R*+n]mulr_natr. rewrite mul1r.
          by rewrite ltr_nat. }
      rewrite mulrA. rewrite mulrC. rewrite mulrA.
      rewrite [(n%:~R - 1)^-1 * (n%:R - 1)]mulrC. rewrite divrr.
      { rewrite mul1r mulr1.
      have ->: (n%:R - 1 = (n - 1)%:R).
      { move=> t. symmetry. apply natrB. auto. }
      rewrite ler_nat.
      have ->: (x = x + 1 - 1)%N by rewrite addnK.
      apply leq_sub2r. by rewrite addn1. }
      { rewrite unitfE. apply /eqP => Contra.
        rewrite -(ler_nat rat_numDomainType) in pf_n.
        have Contra': (n%:Q = 1).
        { apply subr0_eq. apply Contra. }
        have H0: (n%:~R = n%:R) by []. rewrite H0 in Contra'.
        rewrite Contra' in pf_n. inversion pf_n. }
  Qed.

  Fixpoint n_list_norm n (pf_n : (1 < n)%N) (l : seq {x : nat | (x < n)%N})
    : seq {r : rat | 0 <= r <= 1} :=
    match l with
    | nil => nil
    | h :: t => exist _ ((proj1_sig h)%:Q / (n%:Q-1)) (n_norm_bounds h pf_n)
                      :: n_list_norm pf_n t
    end.
  
  Definition uniform_type := {r : rat | 0 <= r <= 1}.
  Definition uniform_enum := n_list_norm pf_N (n_list N).

  Lemma uniform_enumP : Finite.axiom uniform_enum.
  Proof.
    rewrite /uniform_enum. rewrite /Finite.axiom. move => x.
    rewrite /count /=.
    destruct x. simpl.
  Admitted.
  Definition uniform_finMixin := Eval hnf in FinMixin uniform_enumP.
  Canonical uniform_finType :=
    Eval hnf in FinType uniform_type uniform_finMixin.

  Lemma u0_valid : (0 <= 0 <= 1)%Q. Proof. by []. Qed.

  Definition u0 := @exist _ (fun r => 0 <= r <= 1) 0 u0_valid.
  Definition standardUniform_dist := @uniformDist uniform_finType u0.

  Section standardUniformSampler.
    Axiom st_ty : finType.
    Axiom init_st : st_ty.
    Axiom standardUniformSampler : SamplerClass uniform_finType st_ty.
    Axiom standardUniformSamplerAxiomInstance
      : SamplerAxiomClass standardUniform_dist standardUniformSampler init_st.
    Axiom standardUniformCorrectSampler : CorrectSampler _.
  End standardUniformSampler.
End standardUniform.

Section standardUniformLemmas.
  Variable N : nat.
  Variable pfN : (1 < N)%N.

  Lemma uniform_cdf_identity :
    forall u, cdf (standardUniform_dist pfN) u = u.
  Admitted.
  
  (* Lemma uniform_rank : *)
  (*   forall (u : uniform_finType pfN), nat_of_ord (enum_rank u) = `|numq (proj1_sig u)|%N. *)
  (* Admitted. *)

  Lemma ler_enum_rank (a b : uniform_finType pfN) :
    (enum_rank a <= enum_rank b)%N = (proj1_sig a <= proj1_sig b).
  Admitted.

  (* Variable f : rat -> (uniform_finType pfN). *)
  (* Variable pff : forall r, proj1_sig (f r) = r. *)
  
  (* Lemma uniform_cdf_probOf (r : rat) : *)
  (*   probOf (standardUniform_dist pfN) *)
  (*          (fun u' : uniform_finType (N:=N) pfN => *)
  (*             sval u' <= r) = *)
  (*   cdf (standardUniform_dist pfN) (f r). *)
  (* Proof. *)
  (*   rewrite cdf_probOf /=. rewrite /probOf /=. *)
  (*   have ->: (\sum_(t | (enum_rank t <= enum_rank (f r))%N) *)
  (*              (uniform_dist (uniform_finType (N:=N) pfN)) t = *)
  (*             \sum_(t : uniform_finType pfN | proj1_sig t <= proj1_sig (f r)) *)
  (*              (uniform_dist (uniform_finType (N:=N) pfN)) t). *)
  (*   { apply eq_big => x. apply ler_enum_rank. by []. } *)
  (*   by rewrite pff. *)
  (* Qed. *)

End standardUniformLemmas.

Section inverseTransform.
  Variable N : nat.
  Variable pfN : (1 < N)%N.
  Variable T : finType.
  Variable dT : dist T rat_numDomainType.

  (* Every probability in the range of the pmf exists in the uniform
     distribution domain. It should always be possible to choose an
     interval for the uniform distribution (GCD of all probabilities
     and 1) such that this is true. *)
  Variable rat_to_uniform : {r : rat | 0 <= r <= 1} -> (uniform_finType pfN).
  Variable pf_rat_to_uniform :
    forall x, rat_to_uniform (cdf dT x) = cdf dT x.

  (* Wrapper around the inverse_cdf of dT to be used as the map function
     for the map combinator. This is necessary because the domain of
     inverse_cdf is the entire interval [0,1] but the outcome space of
     our uniform distribution is a discrete subset of that interval.
     An important part of the proof is showing that every possible value
     of [cdf dT] exists in the discrete subset, making this function
     still the inverse of [cdf dT]. This should be possible by choosing
     the uniform distribution such that the distance between values is
     a common divisor of every value in the range of [cdf dT] and 1
     (which should be possible if they are rationals). *)
  Definition inverse_cdf' :=
    finfun (fun u : (uniform_finType pfN) => (inverse_cdf dT) u).

  Definition correctUniformSampler := standardUniformCorrectSampler pfN.

  Definition uniformDist := standardUniform_dist pfN.

  Definition inverseTransformDist :=
    map_dist uniformDist inverse_cdf'.

  Definition inverseTransformSamplerInstance :=
    mapSamplerInstance inverse_cdf'.

  Definition inverseTransformSamplerAxiomInstance :=
    mapSamplerAxiomInstance inverse_cdf'.

  Lemma uniform_cdf_probOf (x : T) :
    probOf (standardUniform_dist pfN)
           (fun u' : uniform_finType (N:=N) pfN => sval u' <= sval (cdf dT x)) =
    sval (cdf (standardUniform_dist pfN) (rat_to_uniform (cdf dT x))).
  Proof.
    rewrite /= /probOf /=.
    have ->: (\sum_(t |
                    (enum_rank t <= enum_rank (rat_to_uniform (cdf dT x)))%N)
               (uniform_dist (uniform_finType (N:=N) pfN)) t =
              \sum_(t : uniform_finType pfN |
                    proj1_sig t <= proj1_sig (rat_to_uniform (cdf dT x)))
               (uniform_dist (uniform_finType (N:=N) pfN)) t).
    { apply eq_big => x'. apply ler_enum_rank. by []. }
    by rewrite pf_rat_to_uniform.
  Qed.

  Lemma inverse_cdf'_cdf :
    forall x, inverse_cdf' (rat_to_uniform (cdf dT x)) = x.
  Proof.
    move=> x. rewrite /inverse_cdf' ffunE /inverse_cdf pf_rat_to_uniform /=.
    move: (inverse_cdf_cdf dT) => H. rewrite /inverse_cdf in H. apply H.
  Qed.

  (* Not sure what to call this *)
  Lemma l1 (x : T) :
    \sum_(t | (enum_rank t <= enum_rank x)%N)
     \sum_(u : uniform_finType pfN | inverse_cdf dT u == t)
     (uniform_dist (uniform_finType (N:=N) pfN)) u =
    \sum_(t : uniform_finType pfN |
          (enum_rank (inverse_cdf dT t) <= enum_rank x)%N)
     (uniform_dist (uniform_finType (N:=N) pfN)) t.
  Admitted.

  Lemma probOf_inverse_cdf u x :
    (enum_rank (inverse_cdf dT u) <= enum_rank x)%N =
    (sval u <= sval (cdf dT x)).
  Admitted.

  (* The inverse transform CDF is extensionally equal to the CDF of dT. *)
  Lemma map_cdf_equiv_target_cdf :
    forall x, proj1_sig (cdf inverseTransformDist x) = proj1_sig (cdf dT x).
  Proof.
    move=> x. rewrite /cdf /=.
    have ->: (probOf inverseTransformDist
                     (fun y : T => (enum_rank y <= enum_rank x)%N) =
              probOf uniformDist (fun u' => (enum_rank (inverse_cdf' u')
                                          <= enum_rank x)%N)).
    { rewrite /inverseTransformDist /=. rewrite /map_dist.
      rewrite /inverse_cdf'. rewrite /probOf. rewrite /map_pmf /=.
      rewrite sum_ffunE''.
      have ->: (\sum_(t | (enum_rank t <= enum_rank x)%N)
                 \sum_(u | [ffun u1 : uniform_finType pfN =>
                            inverse_cdf dT u1] u == t)
                 (uniform_dist (uniform_finType (N:=N) pfN)) u =
                \sum_(t | (enum_rank t <= enum_rank x)%N)
                 \sum_(u : uniform_finType pfN | inverse_cdf dT u == t)
                 (uniform_dist (uniform_finType (N:=N) pfN)) u).
      { apply eq_big => // i H.
        have ->: (\sum_(u | [ffun u1 : uniform_finType pfN =>
                             inverse_cdf dT u1] u == i)
                   (uniform_dist (uniform_finType (N:=N) pfN)) u =
                  \sum_(u : uniform_finType pfN | inverse_cdf dT u == i)
                   (uniform_dist (uniform_finType (N:=N) pfN)) u).
        { apply eq_big => // x'. by rewrite ffunE. }
          by []. }
      have ->: ( \sum_(t | (enum_rank ([ffun u : uniform_finType pfN =>
                                        inverse_cdf dT u] t)
                            <= enum_rank x)%N)
                  (uniform_dist (uniform_finType (N:=N) pfN)) t =
                 \sum_(t : uniform_finType pfN |
                       (enum_rank (inverse_cdf dT t) <= enum_rank x)%N)
                  (uniform_dist (uniform_finType (N:=N) pfN)) t).
      { apply eq_big => // x'. by rewrite ffunE. }
      apply l1. }
    have ->: (probOf uniformDist
                     (fun u' : uniform_finType (N:=N) pfN =>
                        (enum_rank (inverse_cdf' u') <= enum_rank x)%N) =
              probOf uniformDist
                     (fun u' : uniform_finType (N:=N) pfN =>
                        proj1_sig u' <= proj1_sig (cdf dT x))).
    { rewrite /inverse_cdf' /probOf /=. apply eq_big => // u.
      rewrite ffunE. apply probOf_inverse_cdf. }
    by rewrite uniform_cdf_probOf uniform_cdf_identity
               pf_rat_to_uniform.
  Qed.

  (* The inverse transform pmf is extensionally equal to dT *)
  Lemma map_pmf_equiv_target_pmf :
    forall u, inverseTransformDist u = dT u.
  Proof. by apply cdf_equiv_pmf; apply map_cdf_equiv_target_cdf. Qed.

  (* Since the sampler is correct wrt the inverse transform distribution
     which is extensionally equal to dT, the sampler is correct wrt dT. *)
  Instance targetSamplerAxiomInstance
    : SamplerAxiomClass dT inverseTransformSamplerInstance init_st.
  Proof.
    move: inverseTransformSamplerAxiomInstance.
    rewrite /SamplerAxiomClass /stat_diff_eps => H eps Heps.
    specialize (H eps Heps). destruct H as [n H]. exists n.
    apply: ler_trans; last by apply H.
    rewrite /stat_difference. apply ler_sum => i _.
    by rewrite map_pmf_equiv_target_pmf.
  Qed.

  (* A correct sampler for dT (where dT is an arbitrary distribution *)
  Instance targetCorrectSampler : CorrectSampler targetSamplerAxiomInstance.
End inverseTransform.
