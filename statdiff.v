Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Require Import dist.

Section sampler.
  Variable T st_ty : finType.
  Class SamplerClass :=
    sampler_fun : st_ty -> (st_ty * T).
End sampler.

(* Generating histogram dists by repeated sampling *)
Section hist.
  Variable T st_ty : finType.
  Variable rty : numDomainType.
  Variable sampler : SamplerClass T st_ty.
  Variable init_st : st_ty.
  Variable N : nat.

  Fixpoint build_hist_aux hist st n :=
    match n with
    | O => hist
    | S n' => let (st', x) := sampler st in
             build_hist_aux
               [ffun y => (hist y + (if y == x then 1%N else 0%N))%N]
               st' n'
    end.
  
  (* Generate a histogram of type T^n (mapping outcomes to their # of
       occurrences observed by sampling) *)
  Definition build_hist :=
    build_hist_aux [ffun x => 0%N] init_st (S N).

  Lemma hist_pos x : (0 <= build_hist x)%N. Proof. by case N. Qed.

  (* Convert a histogram to a dist (divide each # of occurrences by n) *)
  Lemma hist_dist_ax :
    @dist_axiom T rty [ffun x => (build_hist x)%:R / (S N)%:R].
  Proof.
    rewrite /dist_axiom. apply /andP. split.
    { rewrite /build_hist. admit. }
    { apply /forallP => x. admit. }
  Admitted.

  (* Generate a histogram from n samples and create a dist from it *)
  Definition hist_dist :=
    mkDist hist_dist_ax.
End hist.

Section statDifference.
  Variable T st_ty : finType.
  Variable rty : numDomainType.

  (* The actual definition is 1/2 times this I guess *)
  Definition stat_difference (dA dB : dist T rty) :=
    \sum_(t : T) `|dA t - dB t|.
  
  Notation "a '--' b" := (stat_difference a b) (at level 50).

  Definition stat_diff_eps (dA dB : dist T rty) eps :=
    dA -- dB <= eps.
  
  Lemma stat_diff_trans (dA dB dC : dist T rty) epsA epsB :
    dA -- dB <= epsA -> dB -- dC <= epsB -> dA -- dC <= epsA + epsB.
  Proof.
    rewrite /stat_difference.
    move=> H0 H1.
    have H: (\sum_t `|dA t - dC t|
             <= \sum_t `|dA t - dB t| + \sum_t `|dB t - dC t|).
    { by rewrite -big_split /=; apply ler_sum => i _; apply ler_dist_add. }
    apply: ler_trans. apply H.
    apply ler_add => //.
  Qed.
End statDifference.

Section correctSampler.
  Variable T st_ty : finType.
  Variable rty : numDomainType.

  Class SamplerAxiomClass (d : dist T rty)
        (sampler : SamplerClass T st_ty)
        (init_st : st_ty) :=
    samplerAxiom_fun :
      forall eps, 0 < eps -> exists n,
          stat_diff_eps d (hist_dist rty sampler init_st n) eps.

  Class CorrectSampler `(samplerAxiom : SamplerAxiomClass)
    : Type := {}.
End correctSampler.

(* The map distribution/sampler combinator - takes a distribution, a
   sampler, a map function, and a proof that the sampler is correct wrt
   the distribution, and produces a new distribution and sampler by
   mapping the outcome space via the map function along with a proof
   that the new sampler is correct wrt the new distribution. *)
Section mapDistSampler.
  Variable U T st_ty : finType.
  Variable rty : numDomainType.
  Variable d : dist U rty.
  Variable f : {ffun U -> T}.
  Context `{correctSampler : CorrectSampler U st_ty rty d}.

  Definition map_d := map_dist d f.

  Instance mapSamplerInstance : SamplerClass T st_ty:=
    fun st => let (st', sample) := sampler st in (st', f sample).

  (* This is basically the specification of build_hist (at least for
     the sake of inverse transform sampling). build_hist can be defined
     another way as long as this is true. *)
  Lemma map_hist n t :
      build_hist mapSamplerInstance init_st n t =
      (\sum_(u | f u == t) build_hist sampler init_st n u)%N.
  Proof.
    clear. rewrite /mapSamplerInstance /build_hist /=.
    destruct (sampler init_st).
  Admitted.

  (* Quite ugly but it seems that the proof is somewhat straightforward
     as long as map_hist is true. *)
  Instance mapSamplerAxiomInstance :
    SamplerAxiomClass map_d mapSamplerInstance init_st.
  Proof.
    move: samplerAxiom. clear.
    rewrite /SamplerAxiomClass /stat_diff_eps /stat_difference => H eps Heps.
    specialize (H eps Heps). destruct H as [n H]. exists n.
    rewrite /map_d /= /map_pmf.
    have ->: (\sum_t `|[ffun x => \sum_(u | f u == x) d u] t -
              [ffun x => (build_hist mapSamplerInstance
                                    init_st n x)%:R / n.+1%:R] t|
              = \sum_t `|\sum_(u | f u == t) d u -
                (build_hist mapSamplerInstance init_st n t)%:R / n.+1%:R|).
    { by apply eq_big => // i _; rewrite 2!ffunE. }
    move: H. rewrite /hist_dist /=.
    have ->: (\sum_t `|d t -
              [ffun x => (build_hist sampler init_st n x)%:R / n.+1%:R] t|
              = \sum_t `|d t - (build_hist _ init_st n t)%:R / n.+1%:R|).
    { by apply eq_big => // i _; rewrite ffunE. }
    move => H.
    apply: ler_trans; last by apply H.
    have ->: (\sum_t
     `|\sum_(u | f u == t) d u -
       (build_hist mapSamplerInstance init_st n t)%:R / n.+1%:R|
      = \sum_t `|\sum_(u | f u == t) d u -
        (\sum_(u0 | f u0 == t) (build_hist _ init_st n u0)%N)%:R / n.+1%:R|).
    { by apply eq_big => // i _; rewrite map_hist. }
    have ->: (\sum_t
               `|\sum_(u | f u == t) d u -
              (\sum_(u0 | f u0 == t) build_hist _ init_st n u0)%:R / n.+1%:R|
              = \sum_t `|\sum_(u | f u == t)
                 (d u - ((build_hist _ init_st n u)%:R) / n.+1%:R)|).
    { apply eq_big => // i _. rewrite sumrB. rewrite -big_distrl /=.
      suff: (forall a b, a = b -> `|a| = `|b|).
      {  move => H0. apply H0.
         suff: (forall a b c d, a = c -> b = d -> a - b = c - d).
         { move => H1. apply H1 => //. rewrite mulrC.
           rewrite big_distrl /=.
           have ->: (\sum_(i0 | f i0 == i)
                      (build_hist sampler init_st n i0)%:R / n.+1%:R
                     = \sum_(i0 | f i0 == i)
                        ((@GRing.inv
                            (Num.NumDomain.unitRingType rty)
                            (@GRing.natmul
                               (GRing.Ring.zmodType
                                  (GRing.UnitRing.ringType
                                     (Num.NumDomain.unitRingType rty)))
                               (GRing.one
                                  (GRing.UnitRing.ringType
                                     (Num.NumDomain.unitRingType rty)))
                               (S n))) * (build_hist _ init_st n i0)%:R)).
           { by apply eq_big => // i0 H'; rewrite mulrC. }
           rewrite -big_distrr /=.
           suff: (forall a b c d, a = c -> b = d -> a * b = c * d).
           { by move => H2; apply H2 => //; by rewrite natr_sum. }
           clear. by move => t a b c d H0 H1; rewrite H0; rewrite H1. }
         clear. by move => t a b c d H0 H1; rewrite H0; rewrite H1. }
      clear. by move => t a b H; rewrite H. }
    have H0: (\sum_t `|\sum_(u | f u == t)
               (d u - (build_hist sampler init_st n u)%:R / n.+1%:R)|
              <= \sum_t \sum_(u | f u == t)
                 `|(d u - (build_hist sampler init_st n u)%:R / n.+1%:R)|).
    { apply ler_sum => i _. apply ler_norm_sum. }
    apply: ler_trans; first by apply H0.
    by rewrite sum_exchange.
  Qed.

  Instance mapCorrectSampler : CorrectSampler mapSamplerAxiomInstance.
End mapDistSampler.
