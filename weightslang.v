Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.
Require Import ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dist weights numerics bigops.

(** An extremely simple probabilistic programming language, 
    used to implement multiplicative weights update (weights.v) *)

Inductive val : Type :=
| QVal : Q -> val.

Inductive binop : Type := BPlus | BMinus | BMult.

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
    | CUpdate _ => 1
    | CRecv => 1
    | CSend => 1
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
  CSeq
    CRecv
    (CSeq (CUpdate (fun a : A =>
                      (EBinop BMult
                              (EWeight a)
                              (EBinop BMinus
                                      (EVal (QVal 1))
                                      (EBinop BMult EEps (ECost a))))))
          CSend).

Definition mult_weights_init (A : Type) : com A :=
  CSeq
    (CUpdate (fun a : A => EVal (QVal 1)))
    CSend.

Definition mult_weights (A : Type) : com A :=
  CSeq
    (** 1. Initialize weights to uniform *)
    (mult_weights_init A)
    (** 2. The main MWU loop *)
    (CRepeat (mult_weights_body A)).

Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)

  Record state : Type :=
    mkState
      { SCosts : {ffun A -> rat} (* the current cost vector *)
      ; SCostsOk : forall a, 0 <= SCosts a <= 1
        (* the history of cost vectors seen so far *)                   
      ; SPrevCosts : CMAX_costs_seq A
      ; SWeights : {ffun A -> rat} (* current weights *)
      ; SWeightsOk : forall a, 0 < SWeights a
      ; SEpsilon : rat (* epsilon -- a parameter *)
      ; SEpsilonOk : 0 < SEpsilon <= 1 / 2%:R 
        (* the history of the generated distributions over actions *)                     
      ; SOutputs : seq (dist A rat_realFieldType) }.

  Definition eval_binop (b : binop) (v1 v2 : rat) :=
    match b with
    | BPlus => v1 + v2
    | BMinus => v1 - v2                      
    | BMult => v1 * v2
    end.
  
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
      eval_binop b v1 v2
    end.

  Definition CMAX_costs_seq_cons
             (c : costs A)
             (pf : forall a, 0 <= c a <= 1)
             (cs : CMAX_costs_seq A)
    : CMAX_costs_seq A.
  Proof.
    exists (c :: projT1 cs); apply/CMAXP => c'.
    rewrite in_cons; case/orP.
    { by move/eqP => ->. }
    by move => H a; apply: (CMAXP _ (projT2 cs) c' H a).
  Defined.

  Lemma CMAX_nil :
    forall c, c \in (nil : seq (costs A)) -> forall a, 0 <= c a <= 1.
  Proof. by []. Qed.
  
  (** The small-step semantics *)
  
  Inductive step : com A -> state -> com A -> state -> Prop :=
  | SUpdate :
      forall f s pf,
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (finfun (fun a => eval (f a) s))
             pf
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s) 
        in
        step (CUpdate f) s CSkip s'
             
  | SRecv :
      forall (c : {ffun A -> rat}) (pf : forall a, 0 <= c a <= 1) s,
        let: s' :=
           @mkState
             c
             pf
             (@CMAX_costs_seq_cons (SCosts s) (SCostsOk s) (SPrevCosts s))
             (SWeights s)
             (SWeightsOk s)
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
             (SWeightsOk s)
             (SEpsilon s)
             (SEpsilonOk s)             
             (p_aux_dist
                a0
                (SEpsilonOk s)
                (SWeightsOk s)
                CMAX_nil (*Important that [cs := nil] here! 
                           [p_aux_dist] applied to the empty sequence
                           of cost functions specializes to the distribution formed
                           by: SWeights w / \Gamma. *)
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

  Inductive step_plus : com A -> state -> com A -> state -> Prop :=
  | step_trans :
      forall c s c'' s'' c' s',
        step c s c'' s'' ->
        step_plus c'' s'' c' s' -> 
        step_plus c s c' s'.

  Inductive final_com : com A -> Prop :=
  | final_skip :
      final_com CSkip
  | final_repeat :
      forall c, final_com (CRepeat c).

  (** Here's the corresponding big-step semantics. Note that it's 
      index by a nat [n], to break the nonwellfounded recursion 
      in the [CRepeat] case. *)
  
  Inductive stepN : nat -> com A -> state -> state -> Prop :=
  | N0 :
      forall n s, stepN n CSkip s s
    
  | NUpdate :
      forall n f s pf,
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (finfun (fun a => eval (f a) s))
             pf
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s) 
        in
        stepN (S n) (CUpdate f) s s'
             
  | NRecv :
      forall n (c : {ffun A -> rat}) (pf : forall a, 0 <= c a <= 1) s,
        let: s' :=
           @mkState
             c
             pf
             (@CMAX_costs_seq_cons (SCosts s) (SCostsOk s) (SPrevCosts s))
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s)
        in 
        stepN (S n) CRecv s s'

  | NSend :
      forall n s,
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)
             (SEpsilonOk s)
             (p_aux_dist
                a0
                (SEpsilonOk s)
                (SWeightsOk s)
                CMAX_nil 
                    :: SOutputs s)
        in 
        stepN (S n) CSend s s'

  | NSeq :
      forall n c1 c2 s1 s1' s2,
        stepN n c1 s1 s1' ->
        stepN n c2 s1' s2 ->        
        stepN (S n) (CSeq c1 c2) s1 s2
              
  | NRepeat :
      forall n c s s',
        stepN n (CSeq c (CRepeat c)) s s' -> 
        stepN (S n) (CRepeat c) s s'.

  Lemma step_plus_CSkip c1 s1 c1' s1' :
    step_plus c1 s1 c1' s1' ->
    c1 = CSkip ->     
    s1 = s1' /\ c1' = CSkip.
  Proof.
    induction 1; subst.
    move => H2; subst c; inversion H; subst.
    by apply: IHstep_plus.
  Qed.

  Lemma step_plus_trans c1 c2 c3 s1 s2 s3 :
    step_plus c1 s1 c2 s2 ->
    step_plus c2 s2 c3 s3 ->
    step_plus c1 s1 c3 s3.
  Proof.
    move => H H1; induction H; subst => //.
    apply: step_trans; first by apply: H.
    by apply: IHstep_plus.
  Qed.    

  Lemma step_plus_seq c1 c1' c2 s s' :
    step_plus c1 s c1' s' -> 
    step_plus (CSeq c1 c2) s (CSeq c1' c2) s'.
  Proof.
    induction 1.
    apply: step_trans.
    constructor.
    apply: H.
    apply: IHstep_plus.
  Qed.

  Lemma stepN_weaken c s s' n n' :
    (n' >= n)%coq_nat ->
    stepN n c s s' ->
    stepN n' c s s'.
  Proof.
    set P := fun n => forall c s s' n', (n' >= n)%coq_nat -> stepN n c s s' -> stepN n' c s s'.
    move: c s s' n'; change (P n).
    apply (well_founded_ind lt_wf); move {n}; case.
    { move => ?; rewrite /P => c s s' n' _; inversion 1; constructor. }
    move => n IH; rewrite /P => c s s' n' H.
    inversion 1; subst.
    { constructor. }
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor. }
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor. }
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor. }
    { rewrite /P in IH; move {P}.
      case: n' H IH; try solve[move => X; elimtype False; omega].
      move => n0 H4 IH.
      have H5: (n0 >= n)%coq_nat by omega.                
      apply: NSeq.
      apply: (IH n); try omega. apply: H2.
      apply: (IH n); try omega. apply: H3. }
    rewrite /P in IH; move {P}.
    case: n' H IH; try solve[move => X; elimtype False; omega].
    move => n0 H4 IH.
    constructor.
    apply: (IH n); try omega.
    apply: H2.
  Qed.        
  
  Lemma step_stepN c s c'' s'' s' n :
    step c s c'' s'' ->
    stepN n c'' s'' s' ->
    exists n', (n' > n)%coq_nat /\ stepN n' c s s'.
  Proof.
    move => H; move: H s'; induction 1; subst;
      try solve[inversion 1; subst; eexists; split => //; constructor].
    { move => H; exists n.+1; split => //.
      by apply: NSeq; first by constructor. }
    { inversion 1; subst c0 c3 s0 s3 n.
      have H8: (n0.+1 >= n0)%coq_nat by omega.
      case: (IHstep _ (stepN_weaken H8 H4)) => n []H1 H2.
      exists n.+1; split; try omega.
      have H9: (n >= n0)%coq_nat by omega.
      apply: NSeq.
      apply: H2.
      apply: stepN_weaken.
      apply: H9.
      apply: H7. }
    move => s' H; exists n.+1; split; try omega.
    by constructor.
  Qed.
  
  Lemma step_plus_stepN c s c' s' :
    step_plus c s c' s' ->
    final_com c' -> 
    exists n, stepN n c s s'.
  Proof.
    move => H H2; inversion H2; subst; move {H2}; induction H.
    inversion H; subst.
    { case: IHstep_plus => n; inversion 1; subst.
      exists (S n); constructor. }
    { case: IHstep_plus => n; inversion 1; subst.
      exists (S n); constructor. }
    { case: IHstep_plus => n; inversion 1; subst.
      exists (S n); constructor. }
    { case: IHstep_plus => n; inversion 1; subst.
      exists (S n); constructor. }
    { inversion H.
      subst c'' s''.
      case: IHstep_plus => n H5.
      exists (S n).
      apply: NSeq.
      constructor.
      apply: H5.
      subst c'' s''.
      case IHstep_plus => n H7.
      exists (S n).
      apply: NSeq.
      constructor.
      rewrite -H4 in H7.
      apply: H7. }
    { inversion H.
      { subst c1 c2 s0 s''.
        case: IHstep_plus => n H6.
        exists n.+1.
        apply: NSeq.
        constructor.
        apply: H6. }
      subst c0 c3 s1 c1'0 s2.
      case: IHstep_plus => n H8.
      clear - H1 H8.
      inversion H8; subst.
      case: (step_stepN H1 H3) => n []H9 H10.
      exists n.+1.
      apply: NSeq.
      apply: H10.
      apply: stepN_weaken; last by apply: H6.
      omega. }
    { case: IHstep_plus => n H2.
      case: (step_stepN H H2) => n' []H3 H4.
      exists n'.+1.
      constructor.
      apply: stepN_weaken; last by apply: H2.
      omega. }
    case: IHstep_plus => n H1.
    case: (step_stepN H H1) => n' []H2 H3.
    exists n'.
    apply: H3.
  Qed.      
End semantics.

Section mult_weights_refinement.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A.
  
  (* REFINEMENT 1: 
     Show that 

    Definition mult_weights (A : Type) : com A :=
    CSeq
    (** 1. Initialize weights to uniform, then sample *)
    (CSeq (CUpdate (fun a : A => EVal (QVal 1))) CSend)
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

      refines the following functional program: *)

  (** One loop of the functional implementation *)
  Definition mult_weights1_one
             (c : {ffun A -> rat})
             (pf : forall a, 0 <= c a <= 1)
             (s : state A)
    : state A :=
    let: old_costs := @CMAX_costs_seq_cons _ (SCosts s) (SCostsOk s) (SPrevCosts s)
    in 
    @mkState A
      c
      pf
      old_costs
      (update_weights (SEpsilon s) (SWeights s) c)
      (update_weights_gt0 (SEpsilonOk s) pf (SWeightsOk s))
      (SEpsilon s)
      (SEpsilonOk s)
      (p_aux_dist
         a0
         (SEpsilonOk s)
         (update_weights_gt0 (SEpsilonOk s) pf (SWeightsOk s))         
         (CMAX_nil (A:=A))
         :: SOutputs s).

  (** [length cs] loops of the functional implementation. 
      *** NOTE ***  In this implementation of the algorithm, the sequence
      of cost functions [cs] is given in CHRONOLOGICAL (earliest first) 
      rather than reverse chronological order, as was done in [weights_of],
      the Ssreflect spec given in weights.v. *)
  Fixpoint mult_weights1_loop_left
           (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1})
           (s : state A)
    : state A :=
    if cs is [:: c & cs'] then mult_weights1_loop_left cs' (mult_weights1_one (projT2 c) s)
    else s.

  (** Here's a fold-right implementation. *)
  Fixpoint mult_weights1_loop_right
           (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1})
           (s : state A)
    : state A :=
    if cs is [:: c & cs'] then mult_weights1_one (projT2 c) (mult_weights1_loop_right cs' s)
    else s.

  Lemma mult_weights1_loop_right_app cs1 cs2 s :
    mult_weights1_loop_right (cs1 ++ cs2) s =
    mult_weights1_loop_right cs1 (mult_weights1_loop_right cs2 s).
  Proof. by elim: cs1 cs2 s => // c cs1' IH cs2 s /=; rewrite IH. Qed.

  Lemma mult_weights1_loop_leftright cs s :
    mult_weights1_loop_left cs s =
    mult_weights1_loop_right (rev cs) s.
  Proof.
    elim: cs s => // c cs' IH s /=.
    by rewrite /rev /= catrevE mult_weights1_loop_right_app IH.
  Qed.
    
  Definition mult_weights1_init
             (s : state A)
    : state A :=
    @mkState A
      (SCosts s)
      (SCostsOk s)
      (SPrevCosts s)
      (init_weights A)
      (init_weights_gt0 (A:=A))
      (SEpsilon s)
      (SEpsilonOk s)
      (p_aux_dist
         a0
         (SEpsilonOk s)
         (init_weights_gt0 (A:=A))
         (CMAX_nil (A:=A))
         :: SOutputs s).

  Definition mult_weights1
             (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1})
             (s : state A)
    : state A :=
    mult_weights1_loop_left cs (mult_weights1_init s).

  (** Now the proof: *)
  
  Lemma stepN_mult_weights_refines_mult_weights1_one :
    forall n (s s' : state A),
      stepN a0 n (mult_weights_body A) s s' ->
      exists (c : {ffun A -> rat}) (pf : forall a, 0 <= c a <= 1),
        mult_weights1_one pf s = s'.
  Proof.
    move => n s s'.
    inversion 1; subst. clear H.
    inversion H3; subst. clear H3.
    inversion H6; subst. clear H6.
    inversion H2; subst. simpl in *. clear H2.
    inversion H5; subst. simpl in *. clear H5.
    exists c, pf.
    rewrite /mult_weights1_one.
    f_equal.
    apply: proof_irrelevance.
    f_equal.
    f_equal.
    apply: proof_irrelevance.
  Qed.      
  
  Lemma stepN_mult_weights_refines_mult_weights1_loop :
    forall n (s s' : state A),
      stepN a0 n (CRepeat (mult_weights_body A)) s s' ->
      exists (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}),
        mult_weights1_loop_left cs s = s'.
  Proof.
    set P := fun (n : nat) =>
               forall (s s' : state A),
                 stepN a0 n (CRepeat (mult_weights_body A)) s s' ->
                 exists cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1},
                   mult_weights1_loop_left cs s = s'.
    move => n; change (P n).
    apply: (well_founded_ind lt_wf); case.
    { move => _; rewrite /P => s s'; inversion 1. }
    rewrite /P => m IH s s'; inversion 1; subst. clear H.
    inversion H2; subst. clear H2.
    case: (stepN_mult_weights_refines_mult_weights1_one H3) => c []pf H2.
    have Hn0: (n0 < n0.+2)%coq_nat by omega.
    case: (IH n0 Hn0 s1' s' H6) => cs H7.
    by exists [:: existT _ c pf & cs]; rewrite -H2 in H7.
  Qed.      
  
  Lemma stepN_mult_weights_refines_mult_weights1_init :
    forall n (s s' : state A),
      stepN a0 n (mult_weights_init A) s s' ->
      mult_weights1_init s = s'.
  Proof.
    move => n s s'; inversion 1; subst.
    inversion H6; subst.
    inversion H3; subst.
    simpl in *.
    rewrite /mult_weights1_init; f_equal.
    apply: proof_irrelevance.
    f_equal.
    f_equal.
    apply: proof_irrelevance.
  Qed.

  Lemma stepN_mult_weights_refines_mult_weights1 :
    forall n (s s' : state A),
      stepN a0 n (mult_weights A) s s' ->
      exists (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}),
        mult_weights1 cs s = s'.
  Proof.
    move => n s s'; inversion 1; subst.
    move: (stepN_mult_weights_refines_mult_weights1_init H3) => H7.
    rewrite -H7 in H6.
    rewrite /mult_weights1.
    apply: stepN_mult_weights_refines_mult_weights1_loop.
    apply: H6.
  Qed.

  Lemma step_plus_mult_weights_refines_mult_weights1 :
    forall (s s' : state A) c',
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' -> 
      exists (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}),
        mult_weights1 cs s = s'.
  Proof.
    move => s s' c'; move/step_plus_stepN => H H2; case: (H H2) => n H3.
    apply: stepN_mult_weights_refines_mult_weights1.
    apply: H3.
  Qed.

  (** REFINEMENT 2:
      Show that [mult_weights1] refines the Ssreflect spec in weights.v. *)

  Lemma CMAX_all 
    (cs : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}) :
    forall c, c \in map (fun p => projT1 p) cs -> forall a : A, 0 <= c a <= 1.
  Proof.
    elim: cs => // [][]c pf l IH c0.
    rewrite /in_mem /=; case /orP; first by move/eqP => -> a; apply: pf.
    by move => H a; apply: IH.
  Qed.    

  Lemma mult_weights1_loop_right_eps cs s :
    SEpsilon (mult_weights1_loop_right cs s) = SEpsilon s.
  Proof. by elim: cs. Qed.
  
  Lemma mult_weights1_loop_right_refines_weights_of :
    forall s cs,
      let: eps := SEpsilon s in
      SWeights (mult_weights1_loop_right cs s) =
      weights_of eps [seq projT1 x | x <- cs] (SWeights s).
  Proof.
    move => s cs; elim: cs s => // c' cs IH s.
    simpl; f_equal; last by apply: IH.
    by rewrite mult_weights1_loop_right_eps.
  Qed.                 
  
  Lemma mult_weights1_one_hd
        (c : {c : {ffun A -> rat} & forall a, 0 <= c a <= 1})
        cs
        (s : state A)
        d :
    List.hd_error
      (SOutputs (mult_weights1_loop_right cs s)) = Some d ->
    let: s' := mult_weights1_loop_right cs s
    in
    List.hd_error
      (SOutputs (mult_weights1_one (c:=projT1 c) (projT2 c) s')) = 
    List.hd_error
      (SOutputs
         (mult_weights1_one
            (c:=projT1 c) (projT2 c)
            (mkState
               (SCostsOk s')
               (SPrevCosts s')
               (SWeightsOk s')
               (SEpsilonOk s')
               (d :: SOutputs s)))).
  Proof. by case H: (mult_weights1_loop_right cs s). Qed.
  
  Lemma mult_weights1_loop_right_refines_p_aux_dist :
    forall s cs1 cs2 (w : weights A) (pf : forall a : A, 0 < w a),
      List.hd_error (SOutputs s) =
      Some (@p_aux_dist _ a0 _ (SEpsilonOk s) w pf _ (@CMAX_all cs2)) ->
      SWeights s = weights_of (A:=A) (SEpsilon s) [seq projT1 p | p <- cs2] w ->
      let: s' := mult_weights1_loop_right cs1 s
      in List.hd_error (SOutputs s') =
         Some (p_aux_dist a0 (SEpsilonOk s) pf (@CMAX_all (cs1 ++ cs2))).
  Proof.
    move => s cs1 cs2; elim: cs1 s cs2.
    { move => s cs2 w pf /= -> //. }
    move => a cs1' IH s cs2 w pf H Hw; move: (IH _ _ _ _ H Hw) => H2; move {H}.
    rewrite /mult_weights1_loop_right -/mult_weights1_loop_right.
    rewrite (@mult_weights1_one_hd
               a cs1' s
               (p_aux_dist (A:=A) a0 (eps:=SEpsilon s) 
                           (SEpsilonOk s) (w:=w) pf
                           (cs:=[seq projT1 p | p <- cs1' ++ cs2])
                           (CMAX_all (cs:=cs1' ++ cs2)))) => //.
    rewrite /= /p_aux_dist /= /p_aux /=; f_equal.
    move: (p_aux_dist_axiom _ _ _ _).
    move: (p_aux_dist_axiom _ _ _ _).
    rewrite mult_weights1_loop_right_eps.    
    rewrite mult_weights1_loop_right_refines_weights_of.
    have ->:
        update_weights (A:=A) (SEpsilon s)
                         (weights_of (A:=A) (SEpsilon s)
                            [seq projT1 x | x <- cs1'] 
                            (SWeights s)) (projT1 a) =
        update_weights (A:=A) (SEpsilon s)
                         (weights_of (A:=A) (SEpsilon s)
                            [seq projT1 p | p <- cs1' ++ cs2] w)
                         (projT1 a).
    { by rewrite map_cat weights_of_app; f_equal; f_equal; apply: Hw. }
    move => Hx Hy; f_equal.
    apply: proof_irrelevance.
  Qed.

  (** The initial distribution *)
  Program Definition init_dist eps (pf : 0 < eps <= 1/2%:R) :=
    @p_aux_dist A a0 eps pf (init_weights A) _ [::] (CMAX_all (cs:=[::])).
  Next Obligation. apply: init_weights_gt0. Defined.

  (** Given:
        - a sequence of cost vectors [cs]
        - an initial state [s];
      Running [mult_weights1] over [cs], in state [s], 
      results in final output distribution equal to that 
      calculated by [pdist]. *)
  Lemma mult_weights1_refines_pdist :
    forall cs (s : state A),
      List.hd_error (SOutputs (mult_weights1 cs s)) = 
        Some (pdist a0 (SEpsilonOk s) (@CMAX_all (rev cs))).
  Proof.
    move => cs s; rewrite /mult_weights1 mult_weights1_loop_leftright.
    rewrite (@mult_weights1_loop_right_refines_p_aux_dist _ _ nil (init_weights A)).
    { apply: init_weights_gt0. }
    { move => H1; f_equal; rewrite /pdist /p_aux_dist /p cats0; f_equal => /=.
      by apply: proof_irrelevance. }
    { by move => H1 /=; f_equal; f_equal; apply: proof_irrelevance. }
    by [].
  Qed.

  (** Connect the refinements: *)
  Lemma step_plus_mult_weights_refines_pdist :
    forall s c' s',
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' ->
      exists cs,
        List.hd_error (SOutputs s') =
        Some (pdist a0 (SEpsilonOk s) (@CMAX_all (rev cs))).
  Proof.
    move => s c' s' H H2.
    case: (step_plus_mult_weights_refines_mult_weights1 H H2) => cs H3.
    exists cs; rewrite -H3.
    by rewrite mult_weights1_refines_pdist.
  Qed.      
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