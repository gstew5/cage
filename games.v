Set Implicit Arguments.
Unset Strict Implicit.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import OUVerT.extrema OUVerT.dist.

Local Open Scope ring_scope.

(** This module defines an interface over multiplayer games. *)

(** Operational type classe for 'cost';
    cf. "Type Classes for Mathematics in Type Theory", 
        Spitters and van der Weegen,
        http://www.eelis.net/research/math-classes/mscs.pdf*)

Class CostClass (cN : nat) (rty : realFieldType) (cT : finType) :=
  cost_fun : 'I_cN -> {ffun 'I_cN -> cT} -> rty.
Notation "'cost'" := (@cost_fun _ _ _) (at level 30).

Class CostAxiomClass cN rty cT `(CostClass cN rty cT) :=
  cost_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : 0 <= cost i f.

Section costLemmas.
  Context {N rty T} `(CostAxiomClass N rty T).

  Lemma cost_pos i f : 0 <= cost i f.
  Proof. apply: cost_axiom. Qed.
End costLemmas.
  
(*Instance finCloneCostInstance cN rty cT `(H : CostClass cN rty cT) :
  CostClass cN rty [finType of cT] :=
  @cost_fun cN rty [finType of cT] H.*)

Class CostMaxClass (N : nat) (rty : realFieldType) (T : Type) :=
  costmax_fun : rty.

Class CostMaxAxiomClass (N : nat) (rty : realFieldType) (T : finType)
      (costClass : CostClass N rty T)
      (costMaxClass : CostMaxClass N rty T) :=
  costMaxAxiom_fun : forall i s, cost i s  <= costmax_fun.

Class game (T : finType) (N : nat) (rty : realFieldType)
      (costClass : CostClass N rty T)
      (costAxiomClass : CostAxiomClass costClass)
      (costMaxClass : CostMaxClass N rty T)
      (costMaxAxiomClass : CostMaxAxiomClass costClass costMaxClass)
  : Type := {}.

Notation "'gameOf' " := (@game _ _ _ _ _ _ _) (at level 30).

(***********************)
(** Negative cost game *)

Class NegativeCostAxiomClass cN rty cT `(CostClass cN rty cT) :=
  negative_cost_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : cost i f <= 0.

Section negativeCostLemmas.
  Context {N rty T} `(NegativeCostAxiomClass N rty T).

  Lemma cost_neg i f : cost i f <= 0.
  Proof. apply: negative_cost_axiom. Qed.
End negativeCostLemmas.

Class negative_cost_game (T : finType) (N : nat) (rty : realFieldType) 
      `(negativeCostAxiomClass : NegativeCostAxiomClass N rty T)
  : Type := {}.

(** End negative cost game *)
(***************************)

(****************)
(** Payoff game *)

Class PayoffClass (cN : nat) (rty : realFieldType) (cT : finType) :=
  payoff_fun : 'I_cN -> {ffun 'I_cN -> cT} -> rty.
Notation "'payoff'" := (@payoff_fun _ _ _) (at level 30).

Class PayoffAxiomClass cN rty cT `(PayoffClass cN rty cT) :=
  payoff_axiom (i : 'I_cN) (f : {ffun 'I_cN -> cT}) : 0 <= payoff i f.

Section payoffLemmas.
  Context {N rty T} `(PayoffAxiomClass N rty T).

  Lemma payoff_pos i f : 0 <= payoff i f.
  Proof. apply: payoff_axiom. Qed.
End payoffLemmas.

Class payoff_game (T : finType) (N : nat) (rty : realFieldType)
      `(payoffAxiomClass : PayoffAxiomClass N rty T)
  : Type := {}.

(** End payoff game *)
(********************)

(**************************************)
(** Payoff game -> negative cost game *)

Instance negativeCostInstance_of_payoffInstance
         N rty (T : finType)
         `(payoffInstance : @PayoffClass N rty T)
  : CostClass _ _ _ | 99 :=
  fun i f => - payoff i f.

(* 0 <= payoff -> cost <= 0 *)

Instance negativeCostAxiomInstance_of_payoffAxiomInstance
         N rty (T : finType)
         `(payoffAxiomInstance : PayoffAxiomClass N rty T) :
  NegativeCostAxiomClass (negativeCostInstance_of_payoffInstance _) | 99.
Proof.
  move=> i f. rewrite /cost_fun /negativeCostInstance_of_payoffInstance.
  rewrite /PayoffAxiomClass in payoffAxiomInstance.
    by rewrite oppr_le0.
Qed.

Instance negative_cost_game_of_payoff_game
         N rty (T : finType)
         `(_ : payoff_game T N rty)
  : negative_cost_game _ | 99 :=
  Build_negative_cost_game
    (negativeCostAxiomInstance_of_payoffAxiomInstance
       N rty T payoffAxiomClass). (* payoffAxiomClass is an auto-generated name *)

(******************************************)
(** End payoff game -> negative cost game *)

Local Open Scope ring_scope.

(** An arithmetic fact that should probably be moved elsewhere, and
    also generalized. *)
Lemma ler_mull (rty : realFieldType) (x y z : rty) (Hgt0 : 0 < z) :
  x <= y -> z * x <= z * y.
Proof.
  move=> H; rewrite -ler_pdivr_mull=> //; rewrite mulrA.
  rewrite [z^(-1) * _]mulrC divff=> //; first by rewrite mul1r.
  apply/eqP=> H2; rewrite H2 in Hgt0.
  by move: (ltr0_neq0 Hgt0); move/eqP.
Qed.

(** The iff version of this was causing the apply tactic to hang 
    in the gen_smooth proof for the location residual game. *)
Lemma ler_mull2 (rty : realFieldType) (x y z : rty) (Hgt0 : 0 < z) :
  z * x <= z * y -> x <= y.
Proof.
   move=> H. rewrite -ler_pdivr_mull in H=> //. rewrite mulrA in H.
  rewrite [z^(-1) * _]mulrC divff in H=> //. rewrite mul1r in H.
  apply H. 
  apply/eqP=> H2; rewrite H2 in Hgt0.
  by move: (ltr0_neq0 Hgt0); move/eqP.
Qed.

(** A state is a finite function from player indices to strategies. *)
Definition state N T := ({ffun 'I_N -> T})%type.

Section payoffGameDefs.
  Context {T} {N} `(gameAxiomClassA : payoff_game T N)
          `(gameAxiomClassB : payoff_game T N).
  Definition Payoff (t : state N T) : rty := \sum_i (payoff i t).
End payoffGameDefs.

(** All equilibrium notions are parameterized by a [moves] relation
    (via the typeclass [Moveable T]). *)
Section gameDefs.
  Context {T} {N} `(gameAxiomClassA : game T N) `(gameAxiomClassB : game T N).

  (** We assume there's at least one strategy vector. *)
  Variable t0 : state N T. 
  
  (** [t] is a Pure Nash Equilibrium (PNE) if no player is better off
      by moving to another strategy. *)
  Definition PNE (t : state N T) : Prop :=
    forall (i : 'I_N) (t' : state N T),
      cost i t <= cost i t'.

  (** PNE is decidable. *)
  Definition PNEb (t : state N T) : bool :=
    [forall i : 'I_N,
       [forall t' : state N T, (cost i t <= cost i t')]].    

  Lemma PNE_PNEb t : PNE t <-> PNEb t.
  Proof.
    split.
    { move=> H1; apply/forallP=> x //.
      by apply/forallP=> x0; apply: H1.
    }
    by move/forallP=> H1 x t'; apply: (forallP (H1 x)).
  Qed.

  Lemma PNEP t : reflect (PNE t) (PNEb t).
  Proof.
    move: (PNE_PNEb t).
    case H1: (PNEb t).
    { by move=> H2; constructor; rewrite H2.
    }
    move=> H2; constructor=> H3.
    suff: false by [].
    by rewrite -H2.
  Qed.

  (** The social Cost of a state is the sum of all players' costs. *)
  Definition Cost (t : state N T) : rty := \sum_i (cost i t).

  (** A state is optimal if its social cost can't be improved. *)
  Definition optimal : pred (state N T) :=
    fun t => [forall t0, Cost t <= Cost t0].

  (** The Price of Anarchy for game [T] is the ratio of WORST 
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POA : rty :=
    Cost (arg_max PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  (** The Price of Stability for game [T] is the ratio of BEST
      equilibrium social cost to optimal social cost. We want the 
      ratio to be as close to 1 as possible. *)
  Definition POS : rty :=
    Cost (arg_min PNEb Cost t0) / Cost (arg_min optimal Cost t0).

  Lemma POS_le_POA (H1 : PNEb t0) (Hcost : forall t, Cost t > 0) : POS <= POA.
  Proof.
    rewrite /POS /POA.
    move: (min_le_max Cost H1); rewrite /min /max=> H2.
    rewrite ler_pdivr_mulr=> //.
    move: H2; move: (Cost _)=> x; move: (Cost _)=> y.
    have Hx: Cost (arg_min optimal Cost t0) != 0.
    { move: (Hcost (arg_min optimal Cost t0)); rewrite ltr_def.
      by case/andP=> H2 H3. }
    move: Hx; move: (Cost _)=> z Hx H2.
    have H3: (z = z / 1) by rewrite (GRing.divr1 z).
    rewrite {2}H3 mulf_div GRing.mulr1 -GRing.mulrA GRing.divff=> //.
    by rewrite GRing.mulr1.
  Qed.

  (** The expected cost (to player [i]) of a particular distribution
      over configurations.  Note that the distribution [d] need not
      be a product distribution -- in order to define Coarse
      Correlated Equilibria (below), we allow player distributions to
      be correlated with one another. *)
  Definition expectedCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty) :=
    expectedValue d (cost i).

  Definition ExpectedCost (d : dist [finType of state N T] rty) :=
    \sum_(i : 'I_N) expectedCost i d.

  Lemma ExpectedCost_linear d :
    ExpectedCost d
    = expectedValue d (fun v => \sum_(i : 'I_N) (cost i v)).
  Proof.
    rewrite /ExpectedCost /expectedCost /expectedValue.
    by rewrite -exchange_big=> /=; apply/congr_big=> //= i _; rewrite mulr_sumr.
  Qed.

  Definition expectedCondCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t_i : T) :=
    expectedCondValue
      d
      (fun t : state N T => cost i t)
      [pred tx : state N T | tx i == t_i].
  
  Definition upd (i : 'I_N) :=
    [fun t t' : (T ^ N)%type =>
       finfun (fun j => if i == j then t' j else t j)].

  (** This second version of update takes a value of type [T] rather 
      than a complete state as its second parameter. *)
  Definition upd1 (i : 'I_N) :=
    [fun t : (T ^ N)%type =>
       [fun t_i' : T => 
          finfun (fun j => if i == j then t_i' else t j)]].

  Lemma upd1_upd i (t t' : T^N) : upd1 i t (t' i) = upd i t t'.
  Proof.
    rewrite /upd1 /upd /=; apply/ffunP => x; rewrite 2!ffunE.
    case Heq: (i == x) => //.
    by move: (eqP Heq) => ->.
  Qed.      
  
  (** The expected cost of an i-unilateral deviation to strategy [t'] *)
  Definition expectedUnilateralCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t' : state N T) :=
    expectedValue d (fun t : state N T => cost i (upd i t t')).

  Lemma expectedUnilateralCost_linear d t' :
    \sum_(i < N) expectedUnilateralCost i d t'
    = expectedValue d (fun t : state N T =>
                         \sum_(i : 'I_N) cost i (upd i t t')).
  Proof.
    rewrite /expectedUnilateralCost /expectedValue.
    by rewrite -exchange_big=> /=; apply/congr_big=> //= i _; rewrite mulr_sumr.
  Qed.

  (** The expected cost of an i-unilateral deviation to strategy [t' i], 
      conditioned on current i-strategy equal [t_i]. *)
  Definition expectedUnilateralCondCost
             (i : 'I_N)
             (d : dist [finType of state N T] rty)
             (t_i t_i' : T) :=
    expectedCondValue
      d
      (fun t : state N T => cost i (upd1 i t t_i'))
      [pred tx : state N T | tx i == t_i].
  
  (** \epsilon-Approximate Coarse Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to (1 + \epsilon) times the expected cost of distribution [d].

      NOTES: 
      - [t'] must be a valid move for [i] from any state in the 
        support of [d].

      - For this definition to make sense in context, the cost function 
        for game [T] should be normalized to range [0,1].
   *)
  Definition eCCE (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t' : state N T),
      expectedCost i d <= (1 + epsilon) * expectedUnilateralCost i d t'.

  Lemma eCCE_elim
    (epsilon : rty) (d : dist [finType of state N T] rty) (H1 : eCCE epsilon d) :
    forall (i : 'I_N) (t' : state N T),
    expectedCost i d <= (1 + epsilon) * expectedUnilateralCost i d t'.
  Proof.
    rewrite /eCCE in H1 => i t'.
    by move: (H1 i t').
  Qed.

  Definition eCCE2 (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t' : state N T),
      expectedCost i d <= expectedUnilateralCost i d t' + epsilon.

  Lemma eCCE2_elim
    (epsilon : rty) (d : dist [finType of state N T] rty) (H1 : eCCE2 epsilon d) :
    forall (i : 'I_N) (t' : state N T),
    expectedCost i d <= expectedUnilateralCost i d t' + epsilon.
  Proof.
    rewrite /eCCE2 in H1 => i t'.
    by move: (H1 i t').
  Qed.

  (* FixMe: Consider a better place to put this *)
  Lemma costmax_UnilaterCost_sup i (d : dist [finType of state N T] rty) t:
    expectedUnilateralCost i d t <= costmax_fun.
  Proof.
    rewrite /expectedUnilateralCost /expectedValue /expectedCondValue.
    have H: \sum_t1 d t1 * (cost) i ((upd i t1) t) <= \sum_t costmax_fun * d t.
    {
      apply ler_sum => t' _. rewrite [costmax_fun * _] mulrC.
      apply ler_pmul. apply dist_positive. apply costAxiomClass.
      apply lerr. apply costMaxAxiomClass.
    }
    apply: ler_trans. apply H.
    have H' : \sum_t1 costmax_fun * d t1 = costmax_fun.
    {
      rewrite -big_distrr //=.
      rewrite dist_normalized mulr1 //.
    }
    rewrite H'. apply lerr.
  Qed.

  Lemma eCCE2_of_eCCE (d : dist [finType of state N T] rty) (eps1 eps2 : rty)
    (pf : 0 <= eps1) (eps2_value : eps2 = eps1 * costmax_fun):
    eCCE eps1 d -> eCCE2 eps2 d.
  Proof.
    move => H i t'. rewrite /eCCE in H. rewrite eps2_value.
    apply: ler_trans; first by apply (H i t').
    rewrite mulrDl mul1r ler_add //= ler_pmul //=.
    rewrite /expectedUnilateralCost.
    rewrite /expectedValue /expectedCondValue.
    apply big_ind; first by apply lerr. apply Num.Internals.addr_ge0.
    move => i' _. rewrite mulr_ge0 //=. apply dist_positive.
    apply costmax_UnilaterCost_sup.
  Qed.

  Lemma eCCE_of_eCCE2 (d : dist [finType of state N T] rty) (eps1 eps2 : rty)
    (pf : 0 <= eps2)
    (cost_min : rty)
    (cost_min_pos : 0 < cost_min) (cost_min_is_min : forall i s, cost_min <= (cost) i s)
    (eps1_value : eps1 = eps2 /cost_min):
    eCCE2 eps2 d -> eCCE eps1 d.
  Proof.
    move => H i t'. rewrite /eCCE2 in H.
    apply: ler_trans; first by apply (H i t').
    rewrite mulrDl mul1r ler_add //=. rewrite eps1_value.
    rewrite -mulrA. rewrite -[eps2] mulr1.
    rewrite ler_pmul //. rewrite ler01 //.
    rewrite mulr1 lerr //.
    move: (@ler_pmulr rty (cost_min^-1 * expectedUnilateralCost i d t')
            cost_min cost_min_pos) => H0.
    rewrite -H0 mulrA GRing.mulfV. rewrite mul1r.
    rewrite /expectedUnilateralCost /expectedValue /expectedCondValue.
    have H': \sum_t cost_min * d t <= \sum_t1 d t1 * (cost) i ((upd i t1) t').
    {
      apply ler_sum => t _. rewrite [cost_min * _] mulrC.
      rewrite ler_pmul //=. apply dist_positive. apply ltrW. by [].
    }
    apply: ler_trans; last first. apply H'.
    have H'' : \sum_t1 cost_min * d t1 = cost_min.
    {
      rewrite -big_distrr //=.
      rewrite dist_normalized mulr1 //.
    }
    rewrite H''. apply lerr.
    move: (@ltr_def rty 0 cost_min) => H1.
    rewrite H1 in cost_min_pos. move/andP: cost_min_pos => H2.
    inversion H2; by [].
  Qed.

  Definition eCCEb (epsilon : rty) (d : dist [finType of state N T] rty) : bool :=
    [forall i : 'I_N,
       [forall t' : state N T,
           (expectedCost i d <= (1 + epsilon) * expectedUnilateralCost i d t')]].

  Lemma eCCE_eCCEb eps d : eCCE eps d <-> eCCEb eps d.
  Proof.
    split; first by move=> H1; apply/forallP=> x; apply/forallP=> y.
    by move/forallP=> H1 x y; move: (forallP (H1 x)); move/(_ y).
  Qed.    
    
  Lemma eCCEP eps d : reflect (eCCE eps d) (eCCEb eps d).
  Proof.
    move: (eCCE_eCCEb eps d); case H1: (eCCEb eps d).
    by move=> H2; constructor; rewrite H2.
    by move=> H2; constructor; rewrite H2.
  Qed.

  (** Coarse Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to the expected cost of distribution [d]. 

      NOTES: 
      - [t'] must be a valid move for [i] from any state in the 
        support of [d].
   *)
  Definition CCE (d : dist [finType of state N T] rty) : Prop := eCCE 0 d.

  Lemma CCE_elim (d : dist [finType of state N T] rty) (H1 : CCE d) :
    forall (i : 'I_N) (t' : state N T),
    expectedCost i d <= expectedUnilateralCost i d t'.
  Proof.
    rewrite /CCE /eCCE in H1 => i t'.
    by move: (H1 i t'); rewrite addr0 mul1r.
  Qed.    

  Definition CCEb (d : dist [finType of state N T] rty) : bool := eCCEb 0 d.

  Lemma CCE_CCEb d : CCE d <-> CCEb d.
  Proof. apply: eCCE_eCCEb. Qed.
    
  Lemma CCEP d : reflect (CCE d) (CCEb d).
  Proof. apply: eCCEP. Qed.

  (** \epsilon-Approximate Correlated Equilibria
      ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i), 
      conditioned on current strategy (t i), is no greater than 
       \epsilon plus the expected cost of distribution [d].

      NOTES: 
      - [t' i] must be a valid move for [i] from [t i].
   *)
  Definition eCE (epsilon : rty) (d : dist [finType of state N T] rty) : Prop :=
    forall (i : 'I_N) (t_i t_i' : T),
      expectedCondCost i d t_i <= expectedUnilateralCondCost i d t_i t_i' + epsilon.

  Definition eCEb (epsilon : rty) (d : dist [finType of state N T] rty) : bool :=
    [forall i : 'I_N,
      [forall t_i : T,
        [forall t_i' : T, 
          expectedCondCost i d t_i <= expectedUnilateralCondCost i d t_i t_i' + epsilon]]].

  Lemma eCE_eCEb eps d : eCE eps d <-> eCEb eps d.
  Proof.
    split.
    { move=> H1; apply/forallP=> x; apply/forallP=> y; apply/forallP=> z; apply/implyP=> H2.
      by move: (H1 x y z) => H3; move: (H2 H3). }
    move => H1 x y z; move: (forallP H1).
    by move/(_ x)/forallP/(_ y)/forallP/(_ z).
  Qed.    
    
  Lemma eCEP eps d : reflect (eCE eps d) (eCEb eps d).
  Proof.
    move: (eCE_eCEb eps d); case H1: (eCEb eps d).
    by move=> H2; constructor; rewrite H2.
    by move=> H2; constructor; rewrite H2.
  Qed.
  
  Definition CE (d : dist [finType of state N T] rty) : Prop := eCE 0 d.

  Definition CEb (d : dist [finType of state N T] rty) : bool := eCEb 0 d.

  Lemma CE_CEb d : CE d <-> CEb d.
  Proof. apply: eCE_eCEb. Qed.
    
  Lemma CEP d : reflect (CE d) (CEb d).
  Proof. apply: eCEP. Qed.

  Lemma marginal_unfold (F : {ffun 'I_N -> T} -> rty) i :
    let P t (p : {ffun 'I_N -> T}) := p i == t in     
    \sum_(p : [finType of (T * {ffun 'I_N -> T})] | P p.1 p.2) (F p.2) =
    \sum_(p : {ffun 'I_N -> T}) (F p).
  Proof.
    move => P.
    set (G (x : T) y := F y).
    have ->:
      \sum_(p | P p.1 p.2) F p.2 =
      \sum_(p | predT p.1 && P p.1 p.2) G p.1 p.2 by apply: eq_big.
    rewrite -pair_big_dep /= /G /P.
    have ->:
         \sum_i0 \sum_(j : {ffun 'I_N -> T} | j i == i0) F j =
    \sum_i0 \sum_(j : {ffun 'I_N -> T} | predT j && (j i == i0)) F j.
    { by apply: eq_big. }
    rewrite -partition_big //. 
  Qed.      
  
  Lemma sum1_sum (f : state N T -> rty) i :
    \sum_(ti : T) \sum_(t : state N T | [pred tx | tx i == ti] t) f t =
    \sum_t f t.
  Proof. by rewrite -(marginal_unfold f i) pair_big_dep //. Qed.

  Lemma CE_CCE d : CE d -> CCE d.
  Proof.
    move => Hx i t_i'; rewrite /CE in Hx; move: (Hx i).
    rewrite /expectedUnilateralCost /expectedUnilateralCondCost
            /expectedCost /expectedCondCost /expectedValue /expectedCondValue.
    move => Hy.
    rewrite addr0.
    have Hz:
        \sum_(ti : T) \sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i t <=
      \sum_(ti : T) (\sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i (upd i t t_i')).
    { apply: ler_sum => tx _ //.
      move: (Hy tx (t_i' i)) => Hw.
      apply: ler_trans.
      {  admit.
          (* by apply: Hw; move => t <- Hs; apply: H2. *) }
      (* rewrite addr0. *)
    (*   apply: ler_sum => x; move/eqP => H2. *)
    (*   rewrite upd1_upd; apply: lerr. } *)
    (* have ->: \sum_t d t * (cost) i t = *)
    (*          \sum_ti \sum_(t : state N T | [pred tx | tx i == ti] t) d t * (cost) i t. *)
    (* { by rewrite -(sum1_sum _ i). } *)
    (* have ->: *)
    (*   \sum_t d t * (cost) i (((upd i) t) t_i') = *)
    (*   \sum_ti \sum_(t : state N T | [pred tx | tx i == ti] t) *)
    (*      d t * (cost) i (((upd i) t) t_i'). *)
    (* { by rewrite -(sum1_sum _ i). } *)
    (* rewrite mul1r. *)
    (* by apply: Hz. *)
  (* Qed. *)
      Admitted.
(** Mixed Nash Equilibria
      ~~~~~~~~~~~~~~~~~~~~~
      The expected cost of a unilateral deviation to state (t' i) is greater
      or equal to the expected cost of distribution [d]. 

      NOTES: 
      - [d] must be a product distribution, of the form 
        [d_0 \times d_1 \times ... \times d_{#players-1}].

      - [t'] must be a valid move for [i] from any state in the 
        support of [d].
   *)
  Definition MNE (f : {ffun 'I_N -> dist T rty}) : Prop :=
    CE (prod_dist f).
  
  Definition MNEb (f : {ffun 'I_N -> dist T rty}) : bool :=
    CEb (prod_dist f).

  Lemma MNE_MNEb d : MNE d <-> MNEb d.
  Proof. by apply: CE_CEb. Qed.
    
  Lemma MNEP d : reflect (MNE d) (MNEb d).
  Proof. by apply: CEP. Qed.
End gameDefs.