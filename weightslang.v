Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dist weights numerics.

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
  | CUpdate : (A -> expr) -> com
  | CRecv : com
  | CSend : com
  | CSeq : com -> com -> com
  | CRepeat : com -> com.
End com.

Arguments EVal [A] _.
Arguments EEps [A].

Arguments CRecv [A].
Arguments CSend [A].
Arguments CRepeat [A] _.

Definition mult_weights (A : Type) : com A :=
  CRepeat
    (CSeq
       CRecv
       (CSeq (CUpdate (fun a : A =>
                         (EBinop BMult
                              (EWeight a)
                              (EBinop BPlus
                                      (EVal (QVal 1))
                                      (EBinop BMult EEps (ECost a))))))
             CSend)).

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
    
  Inductive step : com A -> state -> state -> Prop :=
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
        step (CUpdate f) s s'
             
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
        step CRecv s s'

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
        step CSend s s

  | SSeq :
      forall c1 c2 s1 s2 s3,
        step c1 s1 s2 ->
        step c2 s2 s3 ->
        step (CSeq c1 c2) s1 s3

  | SRepeat :
      forall c s s',
        step (CSeq c (CRepeat c)) s s' ->
        step (CRepeat c) s s'.
End semantics.
