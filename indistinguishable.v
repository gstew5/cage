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
  
  (* Section hist. *)
  (*   Variable d : dist T rty. *)
  (*   Variable sampler : SamplerClass d. *)
  (*   Variable init_st : st_ty. *)
  (*   Variable n : nat. *)
  (*   (* I think this is probably necessary for the dist_axiom *) *)
  (*   Variable pf : (0 < n)%N. *)

  (*   Fixpoint build_hist_aux hist st n := *)
  (*     match n with *)
  (*     | O => hist *)
  (*     | S n' => let (st', x) := sampler st in *)
  (*              build_hist_aux *)
  (*                [ffun y => (hist y + (if y == x then 1%N else 0%N))%N] *)
  (*                st' n' *)
  (*     end. *)
    
  (*   (* Generate a histogram of type T^n (mapping outcomes to their # of *)
  (*      occurrences observed by sampling *) *)
  (*   Definition build_hist := *)
  (*     build_hist_aux [ffun x => 0%N] init_st n. *)

  (*   Lemma hist_pos x : (0 <= build_hist x)%N. Proof. by case n. Qed. *)

  (*   (* Convert a histogram to a dist (divide each # of occurrences by n) *) *)
  (*   Lemma hist_dist_ax : *)
  (*     @dist_axiom T rty [ffun x => (build_hist x)%:R / n%:R]. *)
  (*   Admitted. *)

  (*   (* Generate a histogram from n samples and create a dist based on it *) *)
  (*   Definition hist_dist := *)
  (*     mkDist hist_dist_ax. *)
  (* End hist. *)

  (** asdf *)
  Definition prob_ensemble := nat -> dist T rty.

  Axiom hist_ensemble : prob_ensemble.

  Definition statistical_difference (A B : dist T rty) adv :=
      `|probOf A adv - probOf B adv|.

  Definition statistically_indistinguishable (A B : prob_ensemble) :=
    forall eps adv n, 0 < eps -> statistical_difference (A n) (B n) adv <= eps.

  Class SamplerAxiomClass (d : dist T rty)
        (sampler : SamplerClass d) :=
    samplerAxiom_fun :
      (* exists n, forall init_st,*)
      statistically_indistinguishable (hist_ensemble) (fun _ => d).

  (* A class that combines a sampler with its proof of correctness wrt.
     the dist it samples from *)
  Class GoodSampler `(sampler : SamplerClass)
        (samplerAxiom : SamplerAxiomClass sampler)
    : Type := {}.
End samplerClasses.
