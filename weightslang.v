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

  Fixpoint size_com (c : com) : nat :=
    match c with
    | CSkip => 0
    | CUpdate _ => 0
    | CRecv => 0
    | CSend => 0
    | CSeq c1 c2 => 1 + size_com c1 + size_com c2
    | CRepeat c' => 2 + size_com c'
    end.
End com.

Arguments EVal [A] _.
Arguments EEps [A].

Arguments CSkip [A].
Arguments CRecv [A].
Arguments CSend [A].
Arguments CRepeat [A] _.

Lemma val_eq_dec (v1 v2 : val) : {v1=v2}+{v1<>v2}.
Proof.
  decide equality.
  case: q; case: q0 => x y x' y'.
  case: (positive_eq_dec y y').
  { move => ->.
    case: (Z_eq_dec x x').
    { move => ->.
      by left. }
    move => H; right => H2; inversion H2; subst => //. }
  by move => H; right; inversion 1; subst.
Qed.    

Lemma eqType_eq_dec (A : eqType) (a s : A) : {a=s}+{a<>s}.
Proof.                                                         
  case H: (a == s).
  { by move: (eqP H) => ->; left. }
  { by right => H2; subst a; rewrite eq_refl in H. }
Qed.
                                                         
Lemma expr_eq_dec (A : eqType) (e1 e2 : expr A) : {e1=e2}+{e1<>e2}.
Proof.
  decide equality.
  apply: val_eq_dec.
  apply: eqType_eq_dec.
  apply: eqType_eq_dec.
  decide equality.
Qed.  

(** Commands aren't decidable in general, because they allow 
    embedded Coq functions in CUpdate. *)

Lemma com_Repeat_dec A (c : com A) :
  (exists c1, c=CRepeat c1) \/ forall c1, c<>CRepeat c1.
Proof.
  case: c; try solve[right => c0 H; congruence].
  { move => c c0; right => c3; congruence. }
  by move => c; left; exists c.
Qed.  

Definition mult_weights_body (A : Type) : com A :=
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

Definition mult_weights_init (A : Type) : com A :=
  CUpdate (fun a : A => EVal (QVal 1)).

Definition mult_weights (A : Type) : com A :=
  CSeq
    (** 1. Initialize weights to uniform *)
    (mult_weights_init A)
    (** 2. The main MWU loop *)
    (mult_weights_body A).

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

  (** The small-step semantics *)
  
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
             (@CMAX_costs_seq_cons (SCosts s) (SCostsOk s) (SPrevCosts s))
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

  | SSkip :
      forall s,
        step CSkip s CSkip s
             
  | SSeq1 :
      forall c2 s,
        step (CSeq CSkip c2) s c2 s
             
  | SSeq2 :
      forall c1 c1' c2 s1 s2,
        step c1 s1 c1' s2 ->
        step (CSeq c1 c2) s1 (CSeq c1' c2) s2

  | SRepeat :
      forall c s,
        step (CRepeat c) s (CSeq c (CRepeat c)) s.

  Inductive step_star : com A -> state -> com A -> state -> Prop :=
  | step_refl :
      forall c s, step_star c s c s
  | step_trans :
      forall c s c'' s'' c' s',
        step c s c'' s'' ->
        step_star c'' s'' c' s' -> 
        step_star c s c' s'.

  (** Here's the corresponding big-step semantics. Note that it's 
      index by a nat [n], to break the nonwellfounded recursion 
      in the [CRepeat] case. *)
  
  Inductive stepN : nat -> com A -> state -> state -> Prop :=
  | NUpdate :
      forall n f s,
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
        stepN n (CUpdate f) s s'
             
  | NRecv :
      forall n (c : {ffun A -> rat}) (pf : [forall a, 0 <= c a <= 1]) s,
        let: s' :=
           @mkState
             c
             pf
             (@CMAX_costs_seq_cons (SCosts s) (SCostsOk s) (SPrevCosts s))
             (SWeights s)
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s)
        in 
        stepN n CRecv s s'

  | NSend :
      forall n s,
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
        stepN n CSend s s'

  | NSeq :
      forall n c1 c2 s1 s1' s2,
        stepN n c1 s1 s1' ->
        stepN n c2 s1' s2 ->        
        stepN (S n) (CSeq c1 c2) s1 s2

  | NRepeat :
      forall n c s s',
        stepN n (CSeq c (CRepeat c)) s s' -> 
        stepN (S n) (CRepeat c) s s'.

  Lemma step_star_CSkip c1 s1 c1' s1' :
    step_star c1 s1 c1' s1' ->
    c1 = CSkip ->     
    s1 = s1' /\ c1' = CSkip.
  Proof.
    induction 1; first by split.
    move => H2; subst c; inversion H; subst.
    by apply: IHstep_star.
  Qed.

  Lemma step_star_trans c1 c2 c3 s1 s2 s3 :
    step_star c1 s1 c2 s2 ->
    step_star c2 s2 c3 s3 ->
    step_star c1 s1 c3 s3.
  Proof.
    move => H H1; induction H; subst => //.
    apply: step_trans; first by apply: H.
    by apply: IHstep_star.
  Qed.    

  Lemma step_star_seq c1 c1' c2 s s' :
    step_star c1 s c1' s' -> 
    step_star (CSeq c1 c2) s (CSeq c1' c2) s'.
  Proof.
    induction 1; first by constructor.
    apply: step_star_trans.
    apply: step_trans.
    constructor.
    apply: H.
    apply: IHstep_star.
    constructor.
  Qed.

  Lemma stepN_step_repeat n c s s' :
    stepN n c s s' ->
    step_star c s CSkip s'.
  Proof.
    move: n c s s'; apply: (well_founded_ind lt_wf) => n IH c.
    case: (com_Repeat_dec c) => [[]c1 H|].
    { (* c = CRepeat ... *)
      move => s s'; subst c; inversion 1; subst.
      inversion H; subst.
      inversion H3; subst.
      apply: step_trans.
      constructor.
      apply: step_star_trans.
      apply: step_star_seq.
      apply: (IH n); first by omega.
      apply: H5.
      apply: step_trans.
      constructor.
      by apply: (IH n); first by omega. }
    case: c.
    { move => H s s'; inversion 1. }
    { move => e H s s'; inversion 1; subst.
      apply: step_trans; constructor. }
    { move => H s s'; inversion 1; subst.
      apply: step_trans; constructor. }
    { move => H s s'; inversion 1; subst.
      apply: step_trans; constructor. }
    { move => c c0 H s s'; inversion 1; subst.
      have Hx: step_star c s CSkip s1'.
      { apply: (IH n0) => //. }
      have Hy: step_star c0 s1' CSkip s'.
      { apply: (IH n0) => //. }
      apply: step_star_trans.
      apply: step_star_seq.
      apply: Hx.
      apply: step_trans.
      constructor.
      apply: Hy. }
    by move => c; move/(_ c).
  Qed.
End semantics.

Section mult_weights_refinement.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A.
  
  (* Show that 

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

      is refined by the following functional program: *)

  (** One loop of the functional implementation *)
  Definition mult_weights'_one
             (c : {ffun A -> rat})
             (pf : [forall a, 0 <= c a <= 1])
             (s : state A)
    : state A :=
    @mkState A
      c
      pf
      (@CMAX_costs_seq_cons _ (SCosts s) (SCostsOk s) (SPrevCosts s))
      (update_weights (SEpsilon s) (SWeights s) c)
      (SEpsilon s)
      (SEpsilonOk s)
      (pdist a0 (SEpsilonOk s) (CMAXb_CMAX (projT2 (SPrevCosts s)))
             :: SOutputs s).

  (** [length cs] loops of the functional implementation *)
  Fixpoint mult_weights'
           (cs : seq {c : {ffun A -> rat} | [forall a, 0 <= c a <= 1]})
           (s : state A)
    : state A :=
    if cs is [:: c & cs'] then mult_weights'_one (projT2 c) (mult_weights' cs' s)
    else s.

  (* HERE

  Lemma mult_weights_refines_mult_weights'_one :
    forall s s' : state A,
      SWeights s = init_weights A -> 
      stepN a0 (size_com (mult_weights_body A)) (mult_weights_body A) s s' ->
      exists (c : {ffun A -> rat}) (pf : [forall a, 0 <= c a <= 1]),
        mult_weights'_one pf s = s'.
  Proof.
    simpl; rewrite !add1n.
    rewrite /mult_weights_body. 
    move => s s' H; inversion 1; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H6; subst.
    inversion H10; subst.
    inversion H7; subst.
    inversion H12; subst.
    simpl in *.
  Qed.

  Lemma mult_weights_init_init :
    forall (s s' : state A),
      stepN a0 (size_com (mult_weights_init A)) (mult_weights_init A) s s' ->
      SWeights s' = init_weights A.
  Proof. by move => s s'; inversion 1; subst. Qed.
  
  Lemma mult_weights_refines_mult_weights'_one :
    forall n (s s' : state A),
      let: n' :=
         (size_com (mult_weights_init A) +
          size_com (mult_weights_body A) * n)%coq_nat
      in 
      stepN a0 n' (mult_weights A) s s' ->
      exists (c : {ffun A -> rat}) (pf : [forall a, 0 <= c a <= 1]),
        mult_weights' pf s = s'.
  Proof.
  Admitted.*)
End mult_weights_refinement.
    
Require Import Reals Rpower Ranalysis Fourier.

Section semantics_lemmas.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)

  (** Current append previous cost vectors *)  
  Definition all_costs (s : state A) :=
    CMAX_costs_seq_cons (SCostsOk s) (SPrevCosts s).

  (** The number of cost vectors received from the environment *)
  Definition T (s : state A) := INR (size (projT1 (all_costs s))).

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
  
  Lemma mult_weights_refines_MWU :
    forall (c' : com A) (s s' : state A),
      step a0 (mult_weights A) s c' s' ->
      state_expCost s' =
      expCostsR a0 (CMAXb_CMAX (projT2 (all_costs s'))) (SEpsilonOk s).
  Proof.
    rewrite /expCostsR /state_expCost /expCostR /expCost.
    move => c' s s' H; apply: big_sum_ext'.
    { admit. }
    
    rewrite /pdist /weights.p /p_aux.
    
    
  Admitted. (*GS TODO*)
  
  Lemma mult_weights_epsilon_no_regret :
    forall (c' : com A) (s s' : state A),
      step a0 (mult_weights A) s c' s' ->
      ((state_expCost s' - OPTR s') / T s' <= eps s + ln size_A / (eps s * T s'))%R.
  Proof.
    move => c' s s' H.
    rewrite (mult_weights_refines_MWU H) /OPTR /OPT /astar /T /eps.
    have H2: (0 < size (projT1 (all_costs s')))%N by [].
    by apply: perstep_weights_noregret.
  Qed.
End semantics_lemmas.