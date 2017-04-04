Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Require Import dist.

Section samplerClasses.
  Variable T st_ty : finType.
  Variable rty : numDomainType.

  Class SamplerClass (d : dist T rty) :=
    sampler_fun : st_ty -> (st_ty * T).
  
  Section hist.
    Variable d : dist T rty.
    Variable sampler : SamplerClass d.
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
    
    (* Generate a histogram of type T^n (mapping outcomes to their # of *)
    (* occurrences observed by sampling *)
    Definition build_hist :=
      build_hist_aux [ffun x => 0%N] init_st (S N).

    Lemma hist_pos x : (0 <= build_hist x)%N. Proof. by case N. Qed.

    (* Convert a histogram to a dist (divide each # of occurrences by n) *)
    Lemma hist_dist_ax :
      @dist_axiom T rty [ffun x => (build_hist x)%:R / (S N)%:R].
    Admitted.

    (* Generate a histogram from n samples and create a dist based on it *)
    Definition hist_dist :=
      mkDist hist_dist_ax.
  End hist.

  Definition prob_ensemble := nat -> dist T rty.

  Definition true_dist_ensemble (d : dist T rty) : prob_ensemble :=
    fun _ => d.

  Definition hist_ensemble `(sampler : SamplerClass)
             (init_st : st_ty) : prob_ensemble :=
    fun n => hist_dist sampler init_st n.

  Definition stat_difference (A B : dist T rty) adv :=
    `|probOf A adv - probOf B adv|.

  (* Definition stat_indistinguishable (A B : prob_ensemble) := *)
  (*   exists N, forall adv n, (N < n)%N -> *)
  (*     stat_difference (A n) (B n) adv <= 1/n%:R. *)

  Definition stat_indistinguishable (A B : prob_ensemble) :=
    forall adv eps, exists N, forall n, (N < n)%N -> 0 < eps n ->
      stat_difference (A n) (B n) adv <= eps n.

  Lemma lt_n_0 n n' :
    (n < n' -> 0 < n')%N.
  Proof. move => H. induction n => //. apply IHn. auto. Qed.

  Class SamplerAxiomClass (d : dist T rty)
        (sampler : SamplerClass d)
        (init_st : st_ty) :=
    samplerAxiom_fun :
      stat_indistinguishable
        (hist_ensemble sampler init_st) (true_dist_ensemble d).

  (* A class that combines a sampler with its proof of correctness wrt.
     the dist it samples from *)
  Class GoodSampler `(samplerAxiom : SamplerAxiomClass)
    : Type := {}.
End samplerClasses.

Notation "a '~' b" := (stat_indistinguishable a b) (at level 50).

(* Statistical indistinguishability is reflexive. *)
Lemma stat_indist_refl (T : finType) (rty : numDomainType)
      (A : prob_ensemble T rty) :
  A ~ A.
Proof.
  rewrite /stat_indistinguishable /stat_difference.
  move => adv eps. exists O => n Hn Heps.
  by rewrite subrr normr0; auto.
Qed.

(* Statistical indistinguishability is symmetric. *)
Lemma stat_indist_symm (T : finType) (rty : numDomainType)
      (A B : prob_ensemble T rty) :
  A ~ B <-> B ~ A.
Proof.
  rewrite /stat_indistinguishable /stat_difference.
  split => H adv eps; specialize (H adv eps);
  destruct H as [N H]; exists N => n Hn;
  by specialize (H n Hn); rewrite distrC.
Qed.

(* Statistical difference satisfies the triangle inequality. *)
Lemma stat_indist_triangle (T : finType) (rty : numDomainType)
      (A B C : prob_ensemble T rty) :
  forall adv n, stat_difference (A n) (C n) adv <=
           stat_difference (A n) (B n) adv +
           stat_difference (B n) (C n) adv.
Proof. by move => adv n; apply ler_dist_add. Qed.

Lemma mul2r (rty : numFieldType) (a : rty) :
  a + a = 2%:R * a.
Proof.
  (* mulr2n *)
  have sdf: (forall i, 2%:Z * i = i + i).
  { apply mul2z. }
Admitted.

Lemma div2_sum (rty : numFieldType) (a : rty) :
  a = a / 2%:R + a / 2%:R.
Proof.
  rewrite mul2r [a*_]mulrC mulrA GRing.divff.
  rewrite mul1r => //. apply lt0r_neq0.
  have ->: (2%:R = 1 + 1) by [].
  by apply addr_gt0; apply: ltr01.
Qed.

Lemma ler_sum_div2 (rty : numFieldType) (a b c : rty) :
  a <= c/2%:R ->
  b <= c/2%:R ->
  a + b <= c.
Proof.
  by move => H0 H1; rewrite [c]div2_sum; apply ler_add.
Qed.

Lemma le_0_div2 (rty : numFieldType) (x : nat) (f : nat -> rty) :
  0 < f x -> 0 < f x / 2%:R.
Proof.
  move => H. apply divr_gt0 => //.
  have ->: (2%:R = 1 + 1) by [].
  apply addr_gt0. apply: ltr01. apply: ltr01.
Qed.

(* Statistical indistinguishability is transitive. *)
Lemma stat_indist_trans (T : finType) (rty : numFieldType)
      (A B C : prob_ensemble T rty) :
  A ~ B -> B ~ C -> A ~ C.
Proof.
  rewrite /stat_indistinguishable.
  move=> Hab Hbc adv eps.
  specialize (Hab adv (fun x => eps x / 2%:R)).
  specialize (Hbc adv (fun x => eps x / 2%:R)).
  destruct Hab as [Nab Hab]. destruct Hbc as [Nbc Hbc].
  destruct ((Nab <= Nbc)%N) eqn:HN.
  exists Nbc => n Hn Heps.
  specialize (Hbc n Hn (le_0_div2 Heps)).
  specialize (Hab n (leq_ltn_trans HN Hn) (le_0_div2 Heps)).
  move: (ler_sum_div2 Hab Hbc) => H0.
  apply ler_trans with (stat_difference (A n) (B n) adv +
                        stat_difference (B n) (C n) adv) => //.
  apply stat_indist_triangle.
  exists Nab => n Hn Heps.
  specialize (Hab n Hn (le_0_div2 Heps)).
  move: HN => /leP HN. apply Compare_dec.not_le in HN.
  move: HN => /leP HN.
  specialize (Hbc n (ltn_trans HN Hn) (le_0_div2 Heps)).
  move: (ler_sum_div2 Hab Hbc) => H0.
  apply ler_trans with (stat_difference (A n) (B n) adv +
                        stat_difference (B n) (C n) adv) => //.
  apply stat_indist_triangle.
Qed.

Lemma stat_indist_f_equiv (T : finType) (rty : numDomainType)
      (A B : prob_ensemble T rty)
      (f : prob_ensemble T rty -> prob_ensemble T rty) :
  A ~ B -> f A ~ f B.
Proof.
  rewrite /stat_indistinguishable /stat_difference => H adv eps.
  (* Probably use to use a different eps *)
  specialize (H adv eps). destruct H as [N H].
  exists N => n Hn Heps.

  rewrite /probOf.
  have ->: (\sum_(t | adv t) (f A n) t - \sum_(t | adv t) (f B n) t =
            \sum_(t | adv t) ((f A n) t - (f B n) t)).
  { admit. }

  rewrite /probOf in H.
  have H0: (\sum_(t | adv t) (A n) t - \sum_(t | adv t) (B n) t =
           \sum_(t | adv t) ((A n) t - (B n) t)).
  { admit. }
  
  specialize (H n Hn Heps). rewrite H0 in H.

Admitted.
