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
   that the new sampler is correct wrt the new distribution.
   
   It may not work out the way it's constructed here, but it should be
   possible in some way. *)
Section mapDistSampler.
  Variable U T st_ty : finType.
  Variable rty : numDomainType.
  Variable d : dist U rty.
  Variable f : {ffun U -> T}.
  Context `{correctSampler : CorrectSampler U st_ty rty d}.

  Definition map_d := map_dist d f.

  Instance mapSamplerInstance : SamplerClass T st_ty:=
    fun st => let (st', sample) := sampler st in (st', f sample).

  Instance mapSamplerAxiomInstance :
    SamplerAxiomClass map_d mapSamplerInstance init_st.
  Proof.
    move: samplerAxiom. clear.
    rewrite /SamplerAxiomClass /stat_diff_eps /stat_difference => H eps Heps.
    specialize (H eps Heps). destruct H as [n H]. exists n.
    rewrite /map_d /= /map_pmf.
    have ->: (\sum_t `|[ffun x => \sum_(u | f u == x) d u] t -
              [ffun x => (build_hist (T:=T) (st_ty:=st_ty) mapSamplerInstance
                                    init_st n x)%:R / n.+1%:R] t|
              =
              \sum_t `|\sum_(u | f u == t) d u -
              (build_hist (T:=T) (st_ty:=st_ty) mapSamplerInstance
                          init_st n t)%:R / n.+1%:R|).
    { by apply eq_big => // i _; rewrite 2!ffunE. }    
  Admitted.

  Instance mapCorrectSampler : CorrectSampler mapSamplerAxiomInstance.

End mapDistSampler.
