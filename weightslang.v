Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dist weights numerics bigops.

(** An extremely simple probabilistic programming language, 
    used to implement multiplicative weights update (weights.v) *)

Inductive val : Type :=
| QVal : Q -> val.

Inductive binop : Type := BPlus | BMult.

Section com.
  Variable A : Type. (* The game type *)

  Inductive expr : Type :=
  | EVal : val -> expr
  | EOpp : expr -> expr
  | EWeight : A -> expr 
  | ECost : A -> expr
  | EEps : expr            
  | EBinop : binop -> expr -> expr -> expr.

  Inductive com : Type :=
  | CSkip : com
  | CUpdate : (A -> expr) -> com
  | CRecv : com
  | CSend : com
  | CSeq : com -> com -> com
  | CRepeat : com -> com.
End com.

Arguments EVal [A] _.
Arguments EEps [A].

Arguments CSkip [A].
Arguments CRecv [A].
Arguments CSend [A].
Arguments CRepeat [A] _.

Definition mult_weights (A : Type) : com A :=
  CSeq
    (** 1. Initialize weights to uniform *)
    (CUpdate (fun a : A => EVal (QVal 1)))
    (** 2. The main MWU loop *)
    (CRepeat
       (CSeq
          CRecv
          (CSeq (CUpdate (fun a : A =>
                            (EBinop BMult
                                    (EWeight a)
                                    (EBinop BPlus
                                            (EVal (QVal 1))
                                            (EBinop BMult EEps (ECost a))))))
                CSend))).

Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)

  Record state : Type :=
    mkState
      { SCosts : {ffun A -> rat} (* the current cost vector *)
      ; SCostsOk : [forall a, 0 <= SCosts a <= 1]
        (* the history of cost vectors seen so far *)                   
      ; SPrevCosts : CMAX_costs_seq A
      ; SWeights : {ffun A -> rat} (* current weights *)
      ; SEpsilon : rat (* epsilon -- a parameter *)
      ; SEpsilonOk : 0 < SEpsilon <= 1 / 2%:R 
        (* the history of the generated distributions over actions *)                     
      ; SOutputs : seq (dist A rat_realFieldType) }.
  
  Fixpoint eval (e : expr A) (s : state) : rat :=
    match e with
    | EVal v =>
      match v with
      | QVal q => Q_to_rat q
      end
    | EOpp e' => let: v := eval e' s in - v
    | EWeight a => SWeights s a
    | ECost a => SCosts s a
    | EEps => SEpsilon s
    | EBinop b e1 e2 =>
      let: v1 := eval e1 s in
      let: v2 := eval e2 s in
      v1 + v2
    end.

  Definition CMAX_costs_seq_cons
             (c : costs A)
             (pf : [forall a, 0 <= c a <= 1])
             (cs : CMAX_costs_seq A)
    : CMAX_costs_seq A.
  Proof.
    exists (c :: projT1 cs); apply/CMAXP => c'.
    rewrite in_cons; case/orP.
    { by move/eqP => ->; apply/forallP. }
    by move => H a; apply: (CMAXP _ (projT2 cs) c' H a).
  Defined.
    
  Inductive step : com A -> state -> com A -> state -> Prop :=
  | SUpdate :
      forall f s,
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (finfun (fun a => eval (f a) s))
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s) 
        in
        step (CUpdate f) s CSkip s'
             
  | SRecv :
      forall (c : {ffun A -> rat}) (pf : [forall a, 0 <= c a <= 1]) s,
        let: s' :=
           @mkState
             c
             pf
             (@CMAX_costs_seq_cons c pf (SPrevCosts s))
             (SWeights s)
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s)
        in 
        step CRecv s CSkip s'

  | SSend :
      forall s,
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (SWeights s)
             (SEpsilon s)
             (SEpsilonOk s)             
             (pdist a0 (SEpsilonOk s) (CMAXb_CMAX (projT2 (SPrevCosts s)))
                    :: SOutputs s)
        in 
        step CSend s CSkip s'

  | SSeq1 :
      forall c2 s,
        step (CSeq CSkip c2) s c2 s
             
  | SSeq2 :
      forall c1 c1' c2 s1 s2,
        step c1 s1 c1' s2 ->
        step (CSeq c1 c2) s1 (CSeq c1' c2) s2

  | SRepeat :
      forall c s,
        step (CRepeat c) s (CSeq c (CRepeat c)) s

  | STrans :
      forall c1 c2 c3 s1 s2 s3,
        step c1 s1 c2 s2 ->
        step c2 s2 c3 s3 ->
        step c1 s1 c3 s3.
End semantics.

Require Import Reals Rpower Ranalysis Fourier.

Section semantics_lemmas.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)

  (** The number of cost vectors received from the environment *)
  Definition T (s : state A) := INR (size (projT1 (SPrevCosts s))).+1.

  (** Current append previous cost vectors *)  
  Definition all_costs (s : state A) :=
    CMAX_costs_seq_cons (SCostsOk s) (SPrevCosts s).

  (** The total expected cost of state [s] *)    
  Definition state_expCost (s : state A) :=
    big_sum (zip (projT1 (all_costs s)) (SOutputs s))
            (fun p =>
               let: (c, d) := p in
               rat_to_R (expectedValue d (fun a => c a))).

  (** The best fixed action (in hindsight) for state [s] *)      
  Definition astar (s : state A) :=
    best_action a0 (projT1 (all_costs s)).

  Definition OPT (s : state A) :=
    \sum_(c <- projT1 (all_costs s)) c (astar s).
  Definition OPTR (s : state A) := rat_to_R (OPT s).

  Definition eps (s : state A) := rat_to_R (SEpsilon s).

  Notation size_A := (rat_to_R #|A|%:R).

  Lemma MWU_epsilon_no_regret :
    forall (c' : com A) (s s' : state A),
      step a0 (mult_weights A) s c' s' ->
      ((state_expCost s' - OPTR s') / T s' <= eps s + ln size_A / (eps s * T s'))%R.
  Proof.
  Admitted. (*GS TODO*)    
End semantics_lemmas.