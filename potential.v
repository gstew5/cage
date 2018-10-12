Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import Num.Theory.

Require Import OUVerT.extrema games dynamics.

(** * Potential Games *)

Local Open Scope ring_scope.

Class PhiClass (pN : nat) (rty : realFieldType) (pT : finType)
      `(gameClass : game)
  : Type := Phi : state pN pT -> rty.

(* Class PhiAxiomClass (pN : nat) (rty : realFieldType) (pT : finType) *)
(*       `(costAxiomClass : CostAxiomClass pN rty pT) *)
(*       (gameClass : game costAxiomClass) *)
(*       (phiClass : PhiClass gameClass) : Type := *)
(*   PhiAxiom :  *)
(*     forall (i : 'I_pN) (t t' : state pN pT), *)
(*       Phi t' - Phi t = cost i t' - cost i t. *)
(* Notation "'phi_ax'" := (@PhiAxiom _ _ _ _ _ _ _) (at level 50). *)

Class PhiAxiomClass (pN : nat) (rty : realFieldType) (pT : finType)
      (costClass : CostClass pN rty pT)
      (costAxiomClass : CostAxiomClass costClass)
      (costMaxClass : CostMaxClass pN rty pT)
      (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
      (gameClass : game _ _)
      (phiClass : PhiClass _ _ _ gameClass) : Type :=
  PhiAxiom : 
    forall (i : 'I_pN) (t t' : state pN pT),
      Phi t' - Phi t = cost i t' - cost i t.
Notation "'phi_ax'" := (@PhiAxiom _ _ _ _ _ _ _) (at level 50).

(* Class Potential (N : nat) (rty : realFieldType) (T : finType) *)
(*       `(costAxiomClass : CostAxiomClass N rty T) *)
(*       (gameClass : game costAxiomClass) *)
(*       `(phiClass : PhiClass) *)
(*       (phiAxiomClass : PhiAxiomClass phiClass) *)
(*   : Type := {}. *)

Class Potential (* (N : nat) (rty : realFieldType) (T : finType) *)
      `(phiAxiomClass : PhiAxiomClass)
  : Type := {}.

Section PotentialLemmas.
  Context `{potentialClass : Potential}.
  Notation sT := (state pN pT).
  
  Definition minimal : pred sT :=
    [pred t : sT | [forall t' : sT, Phi t <= Phi t']].

  Lemma Phi_cost_le (t t' : sT) i :
    Phi t <= Phi t' -> cost i t <= cost i t'.
  Proof.
    rewrite -subr_ge0=> H0.
    generalize (phi_ax)=> H2. 
    by rewrite -subr_ge0 -H2.
  Qed.      

  Lemma cost_Phi_lt (t t' : sT) i :
    cost i t' < cost i t -> Phi t' < Phi t.
  Proof.
    generalize (phi_ax)=> H0.
    by rewrite -subr_lt0 -H0 subr_lt0.
  Qed.        
  
  (** Any [t] minimal wrt. the potential function [Phi] is 
      a Pure Nash Equilibrium. *)
  Lemma minimal_PNE (t : sT) : minimal t -> PNE t.
  Proof.
    rewrite /minimal=> /=; move/forallP=> H0 x.
    by move=> t'; move: H0; move/(_ t'); apply: Phi_cost_le.
  Qed.

  Definition Phi_minimizer (t0 : sT) : sT := arg_min predT Phi t0.

  Lemma minimal_Phi_minimizer (t0 : sT) : minimal (Phi_minimizer t0).
  Proof.
    have H0: predT t0 by [].
    by case: (andP (arg_minP Phi H0)).
  Qed.  

  Lemma PNE_Phi_minimizer (t0 : sT) : PNE (Phi_minimizer t0).
  Proof.
    apply: minimal_PNE.
    apply: minimal_Phi_minimizer.
  Qed.    
  
  (** Assuming [T] is inhabited, every potential game over [T] has at
      least one PNE. *)
  Lemma exists_PNE (t0 : sT) : exists t : sT, PNE t.
  Proof.
    exists (Phi_minimizer t0).
    apply: PNE_Phi_minimizer.
  Qed.    
End PotentialLemmas.

Section BestResponseDynamics.
  Context `{potentialClass : Potential}.
  Notation sT := (state pN pT).
  
  Inductive step : sT -> sT -> Prop :=
  | step_progress t t' (i : 'I_pN) :
      cost i t' < cost i t -> step t t'.
      
  Definition halted (t : sT) := PNE t.

  Let hstate := (simpl_pred sT * simpl_pred sT * sT)%type.
  
  Definition P (sut : hstate) : Prop :=
    let: (s,u,t) := sut in
    forall t0, s t0 -> Phi t <= Phi t0.

  Lemma init_P t : P (init t).
  Proof. by move=> t0 /=; move/eqP=> <-. Qed.

  (* TODO: This proof should be cleaned up. *)
  
  Lemma step_P s u t t' :
    inv (s,u,t) -> P (s,u,t) -> step t t' -> 
    [/\ u t' & P (predU1 t' s, predD1 u t', t')].
  Proof.
    case=> H0 H1 H2 H3; inversion 1; subst.
    have Hx: Phi t' < Phi t.
    { by apply: (cost_Phi_lt H4).
    }
    suff: ~~ s t'; last first.
    { apply/negP; move=> H6.
      move: (H3 _ H6)=> H7.
      move: (ltrW Hx)=> H8.
      have H9: Phi t' <> Phi t.
      { apply/eqP.
        by rewrite ltr_eqF.
      }
      move: H7 H8 H9; rewrite !ler_eqVlt; case/orP; first by move/eqP=> <-.
      move=> H7; case/orP; first by move/eqP=> <-.
      move=> H8 H9.
      have H10: Phi t' < Phi t'.
      { apply: ltr_trans.
        apply: H8.
        by [].
      }
      by rewrite ltrr in H10.
    }
    move=> H6.
    move: (H3 t')=> /=.
    move: (H0 t')=> /=.
    case: (s t') H6=> //= _.
    rewrite (mem_enum sT _).
    move=> -> _; split=> //.
    move=> t0; case/orP; first by move/eqP=> <-.
    move=> H6.
    apply: ltrW.
    apply: ltr_le_trans.
    apply: Hx.
    apply: (H3 t0 H6).
  Qed.    

  Lemma halted_doesnt_step t t' :
    halted t -> step t t' -> False.
  Proof.
    rewrite /halted=> H0; inversion 1; subst.
    move: (H0 i)=> H4.
    generalize (ltr_le_asym (cost i t') (cost i t)).
    by rewrite H1 H4.
  Qed.    

  Lemma best_response_safe t : 
    safe step halted t.
  Proof.    
    move=> t''; induction 1=> //.
    case: (PNEP t).
    { by move=> H0; right.
    }
    move=> H0; left.
    suff H2: ~~ (@PNEb _ _ _ costClass t); last first.
    { apply/negP=> H1; case: (PNE_PNEb t)=> H2 H3.
      by apply: H0; apply H3.
    }
    rewrite negb_forall in H2; case: (existsP H2)=> i; rewrite negb_forall.
    case/existsP=> t'; move/negP=> H4.
    exists t'; apply: (step_progress (i:=i))=> //.
    by rewrite ltrNge; apply/negP.
  Qed.
  
  Lemma best_response_everywhere_halts t :
    everywhere_halts step halted t.
  Proof.
    apply: (step_everywhere_halts_or_stuck P).
    apply: init_P.
    apply: step_P.
    apply: halted_doesnt_step.
    apply: best_response_safe.
  Qed.    
End BestResponseDynamics.

Print Assumptions best_response_everywhere_halts.

Section PriceOfStabilityBound.
  (** The following section proves a bound on the Price of Stability 
      of potential games. *)
  Context `{potentialClass : Potential}.
  Notation sT := (state pN pT).
  
  (** We assume the social cost function is positive. *)
  Hypothesis Cost_pos : forall t : sT, 0 < Cost t.

  (** The bound [A] must also be positive; otherwise, dividing by [A] 
      in [AB_bound_Phi] is undefined. *)
  Variables A B : rty.
  Hypothesis (HAgt0 : 0 < A).

  (** The bound is proved assuming there exist real numbers [A] and [B] 
      such that for any state [t], [Phi t] is bounded on the left by 
      [Cost t / A] and bounded on the right by [B * Cost t]. *)
  Hypothesis AB_bound_Phi :
    forall t : sT, Cost t / A <= Phi t <= B * Cost t.

  (** Under the conditions stated above, the Price of Stability of 
      any potential game is at most [A * B]. (For games in which the 
      PNE is unique, this bound gives a bound on the Price of Anarchy
      as well.) *)
  Lemma POS_bounded (t0 : sT) (PNE_t0 : PNE t0) : POS t0 <= A * B.
  Proof.
    set (tN := Phi_minimizer t0).
    generalize (minimal_Phi_minimizer t0); move/forallP=> HtN.
    case: (andP (AB_bound_Phi tN))=> H3 H4; rewrite /POS.
    set (tStar := arg_min optimal Cost t0).
    move: (HtN tStar)=> H5.
    case: (andP (AB_bound_Phi tStar))=> H6 H7.
    rewrite ler_pdivr_mulr; last by apply: Cost_pos.
    apply: ler_trans.
    have H8: Cost (arg_min PNEb Cost t0) <= Cost tN.
    { have H9: PNE tN by apply: PNE_Phi_minimizer.
      have H10: PNEb t0 by move: PNE_t0; case: (PNEP t0).
      case: (andP (arg_minP Cost H10)).
      by move=> H11; move/forallP; move/(_ tN)/implyP; apply; rewrite -PNE_PNEb.
    }
    apply: H8.
    rewrite ler_pdivr_mulr in H3=> //.
    have H8: Phi tN * A <= Phi tStar * A.
    { rewrite GRing.mulrC [Phi tStar * _]GRing.mulrC.
      apply: ler_mull=> //; by rewrite -H.        
    }
    apply: ler_trans; [apply: H3|].
    apply: ler_trans; [apply: H8|].
    rewrite GRing.mulrC -GRing.mulrA.
    by apply: ler_mull.
  Qed.
End PriceOfStabilityBound.
