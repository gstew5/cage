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
      ; SPrevCosts : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}
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
             (existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s)
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
  | step1 :
      forall c s c' s',
        step c s c' s' ->
        step_plus c s c' s'
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
             (existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s)
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
    by split.
    move => H1; subst c.
    inversion H; subst.
    by apply: IHstep_plus.
  Qed.

  Lemma step_plus_trans c1 c2 c3 s1 s2 s3 :
    step_plus c1 s1 c2 s2 ->
    step_plus c2 s2 c3 s3 ->
    step_plus c1 s1 c3 s3.
  Proof.
    move => H H1; induction H.
    apply: step_trans; first by apply: H. apply: H1.
    apply: step_trans. apply: H. by apply IHstep_plus.
  Qed.    

  Lemma step_plus_seq c1 c1' c2 s s' :
    step_plus c1 s c1' s' -> 
    step_plus (CSeq c1 c2) s (CSeq c1' c2) s'.
  Proof.
    induction 1.
    constructor.
    by constructor.
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

  Lemma step_stepN_final c s c' s' :
    step c s c' s' ->
    final_com c' -> 
    exists n, stepN n c s s'.
  Proof.        
    move => H H2; inversion H2; subst; move {H2}.
    { inversion H; subst; try solve[exists (S O); constructor].
      exists (S (S O)). apply: NSeq. constructor. constructor. }
    move: H; remember (CRepeat c0) as cx; induction 1 => //.
    exists (S (S O)). apply: NSeq. constructor. constructor.
    
  Lemma step_plus_stepN c s c' s' :
    step_plus c s c' s' ->
    final_com c' -> 
    exists n, stepN n c s s'.
  Proof.
    move => H H2; inversion H2; subst; move {H2}; induction H.
    inversion H; subst; try solve[exists (S O); constructor].


    
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
    let: old_costs := existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s
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
      mult_weights1_one (SCostsOk s') s = s'.
  Proof.
    move => n s s'.
    inversion 1; subst. clear H.
    inversion H3; subst. clear H3.
    inversion H6; subst. clear H6.
    inversion H2; subst. simpl in *. clear H2.
    inversion H5; subst. simpl in *. clear H5.
    rewrite /mult_weights1_one.
    f_equal.
    apply: proof_irrelevance.
    f_equal.
    f_equal.
    apply: proof_irrelevance.
  Qed.      

  Definition all_costs (s : state A) :=
    [:: existT _ _ (SCostsOk s) & SPrevCosts s].

  Lemma all_costs_CMAX' (l : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}) :
    forall c, c \in map (fun c => projT1 c) l ->
                    forall a : A, 0 <= c a <= 1.
  Proof.    
    move => c; rewrite /in_mem /=; elim: l => // a l IH; case/orP.
    { move/eqP => ->; apply: (projT2 a). }
    by move => H; apply: IH.
  Qed.
  
  Lemma all_costs_CMAX (s : state A) :
    forall c, c \in map (fun c => projT1 c) (all_costs s) ->
                    forall a : A, 0 <= c a <= 1.
  Proof. apply: all_costs_CMAX'. Qed.
  
  Lemma mult_weights1_one_all_costs s s' : 
    mult_weights1_one (c:=SCosts s') (SCostsOk s') s = s' ->
    all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s].
  Proof. by rewrite /mult_weights1_one; case: s'; inversion 1; subst. Qed.

  Lemma cat_cons' T (x : T) l1 l2 : l1 ++ x :: l2 = rcons l1 x ++ l2.
  Proof. by elim: l1 l2 x => // a l IH l2 x /=; rewrite IH. Qed.

  Lemma rcons_inj T (x y : T) l1 l2 :
    rcons l1 x = rcons l2 y -> l1 = l2 /\ x = y.
  Proof.
    elim: l1 l2.
    { case => /=; first by case => ->; split.
      move => a l2 /=; case => ->; case: l2 => //. }
    move => a l1 IH; case => /=.
    { case => ->; case: l1 IH => //. }
    by move => a1 l2; case => -> H2; case: (IH _ H2) => -> ->.
  Qed.
    
  Lemma cat_inj T (l : list T) l0 s :
    l ++ s = l0 ++ s -> l = l0.
  Proof.
    elim: s l0 l; first by move => l0 l; rewrite 2!cats0.
    move => a l IH l0 l1; rewrite 2!cat_cons' => H.
    by move: (IH _ _ H) => H2; case: (rcons_inj H2) => ->.
  Qed.

  Lemma size_rev_cat1 T (a : T) l s :
    (0 < size (rev l ++ [:: a & s]))%N.
  Proof.
    rewrite size_cat; elim: l => // a1 l IH.
    by rewrite size_rev.
  Qed.      

  Lemma rev_nil T : rev (T:=T) nil = nil.
  Proof. by []. Qed.

  Lemma rcons_nil_inv T (l : list T) x :
    [::] = rcons l x -> False.
  Proof. by elim: l. Qed.
  
  Lemma rev_inj T (l : list T) l0 :
    rev l = rev l0 -> l = l0.
  Proof.
    elim: l l0.
    { case => // a l0 /=; rewrite rev_cons rev_nil => H.
      by move: (rcons_nil_inv H). }
    move => a l IH l0; rewrite rev_cons; case: l0.
    { rewrite rev_nil => H.
      by symmetry in H; move: (rcons_nil_inv H). }
    move => a1 l0; rewrite rev_cons => H.
    case: (rcons_inj H) => H2 ->.
    by rewrite (IH _ H2).
  Qed.    
                        
  Lemma catrev_cons_inv T (l : list T) s l0 x :
    catrev l s = catrev l0 [:: x & s] ->
    l = [:: x & l0].
  Proof. by rewrite 2!catrevE -cat_rcons -rev_cons; move/cat_inj/rev_inj. Qed.

  Lemma catrev_repeat n c s s' :
    (forall m s s', stepN a0 m c s s' ->
                    exists x, all_costs s' = x :: all_costs s) ->
    stepN a0 n (CRepeat c) s s' -> 
   exists l0 : seq {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1},
     all_costs s' = catrev l0 (all_costs s).
  Proof.
    set (P :=
           fun (n : nat) =>
             forall s,
               (forall m s s', stepN a0 m c s s' ->
                               exists x, all_costs s' = x :: all_costs s) ->
               stepN a0 n (CRepeat c) s s' -> 
               exists l0 : seq {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1},
                 all_costs s' = catrev l0 (all_costs s)).
    move: s; change (P n).
    apply: (well_founded_ind lt_wf); case.
    { rewrite /P => H s H2; inversion 1. }
    rewrite /P => n0 IH s H; inversion 1; subst.
    destruct n0; first by inversion H3.
    inversion H3; subst.
    case: (H _ _ _ H5) => x => H9.
    have H10: (n0 < n0.+2)%coq_nat by omega.
    case: (IH _ H10 s1' H H8) => l => H11.
    by exists [:: x & l]; rewrite H11 H9.
  Qed.    
  
  Lemma stepN_repeat_fold :
    forall n (s s' : state A) l c
           (f : forall c : {ffun A -> rat},
               (forall a, 0 <= c a <= 1) ->
               state A -> state A),
      (forall n s s', stepN a0 n c s s' -> f (SCosts s') (SCostsOk s') s = s') ->
      (forall n s s',
          stepN a0 n c s s' ->
          all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) -> 
      stepN a0 n (CRepeat c) s s' ->
      catrev l (all_costs s) = all_costs s' -> 
      foldl (fun s c => f (projT1 c) (projT2 c) s) s l = s'.
  Proof.
    set P :=
      fun (n : nat) =>               
        forall (s s' : state A) l c
               (f : forall c : {ffun A -> rat},
                   (forall a, 0 <= c a <= 1) ->
                   state A -> state A),
          (forall n s s', stepN a0 n c s s' -> f (SCosts s') (SCostsOk s') s = s') ->
          (forall n s s',
              stepN a0 n c s s' ->
              all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) -> 
          stepN a0 n (CRepeat c) s s' ->
          catrev l (all_costs s) = all_costs s' -> 
          foldl (fun s c => f (projT1 c) (projT2 c) s) s l = s'.
    move => n; change (P n).
    apply: (well_founded_ind lt_wf); case.
    { move => _; rewrite /P => s s' l c f H H2; inversion 1. }
    rewrite /P => m IH s s' l c f H H2; inversion 1; subst.
    clear H0 => H0.
    inversion H4; subst. clear H4 P.
    have Hn0: (n0 < n0.+2)%coq_nat by omega.
    move: (H2 _ _ _ H6) => H7.
    have H10: l = [:: existT _ _ (SCostsOk s1') & behead l].
    { have H11: exists l0, all_costs s' = catrev l0 (all_costs s1').
      { apply: catrev_repeat; last by apply: H9.
        move => m sx sx' H10.
        exists (existT _ _ (SCostsOk sx')).
        by rewrite (H2 _ _ _ H10). }
      case: H11 => l0 H11.
      rewrite H11 H7 /= in H0.
      move: (catrev_cons_inv H0).
      by clear H0; case: l => // a l' /=; case => -> ->. }
    rewrite H10 /=.
    have H11: f (SCosts s1') (SCostsOk s1') s = s1'.
    { by apply: H; apply: H6. }
    rewrite (IH _ Hn0 (f (SCosts s1') (SCostsOk s1') s) s' (behead l) c) => //.
    by rewrite H11; apply: H9.
    by rewrite H11 H7 -H0 H10.
  Qed.

  Lemma mult_weights1_loop_left_foldl
        (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}) (s : state A) :
    mult_weights1_loop_left cs s =
    foldl (fun s c => mult_weights1_one (projT2 c) s) s cs.
  Proof. by elim: cs s => // c cs' IH s /=; rewrite IH. Qed.
  
  Lemma stepN_mult_weights_refines_mult_weights1_loop :
    forall n (s s' : state A) l,
      stepN a0 n (CRepeat (mult_weights_body A)) s s' ->
      catrev l (all_costs s) = all_costs s' ->
      mult_weights1_loop_left l s = s'.
  Proof.
    move => n s s' l H H2.
    rewrite mult_weights1_loop_left_foldl.
    apply: (stepN_repeat_fold (n:=n) (c:=mult_weights_body A)) => //.
    { move => m sx sx' H3.
      apply: stepN_mult_weights_refines_mult_weights1_one.
      apply: H3. }
    move => m sx sx' H3.
    apply: mult_weights1_one_all_costs.
    apply: stepN_mult_weights_refines_mult_weights1_one.
    apply: H3.
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
    forall n (s s' : state A) l,
      stepN a0 n (mult_weights A) s s' ->
      catrev l (all_costs s) = all_costs s' -> 
      mult_weights1 l s = s'.
  Proof.
    move => n s s'; inversion 1; subst.
    move: (stepN_mult_weights_refines_mult_weights1_init H3) => H7.
    rewrite -H7 in H6.
    rewrite /mult_weights1 => H8.
    apply: stepN_mult_weights_refines_mult_weights1_loop.
    apply: H6.
    apply: H8.
  Qed.

  Lemma step_plus_mult_weights_refines_mult_weights1 :
    forall (s s' : state A) c' l,
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' ->
      catrev l (all_costs s) = all_costs s' ->       
      mult_weights1 l s = s'.
  Proof.
    move => s s' c' l; move/step_plus_stepN => H H2; case: (H H2) => n H3.
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
    forall s c' s' l,
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' ->
      catrev l (all_costs s) = all_costs s' ->       
      List.hd_error (SOutputs s') =
      Some (pdist a0 (SEpsilonOk s) (@CMAX_all (rev l))).
  Proof.
    move => s c' s' l H H2 H3.
    rewrite -(step_plus_mult_weights_refines_mult_weights1 H H2 H3).
    by rewrite mult_weights1_refines_pdist.
  Qed.      
End mult_weights_refinement.

Require Import Reals Rpower Ranalysis Fourier.

Section semantics_lemmas.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)

  (** The total expected cost of state [s] *)    
  Definition state_expCost
             (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1})
             (s : state A) :=
    big_sum (zip l (SOutputs s))
            (fun p =>
               let: (c, d) := p in
               rat_to_R (expectedValue d (fun a => projT1 c a))).

  Fixpoint state_expCost1
           (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1})
           (ds : seq (dist.dist A rat_realFieldType)) :=
    match l, ds with
    | [:: c & l'], [:: d & ds'] =>
      (rat_to_R (expectedValue d (fun a => projT1 c a)) +
      state_expCost1 l' ds')%R
    | _, _ => 0%R
    end.

  Fixpoint state_expCost2
           eps
           (EpsOk : 0 < eps <= 1 / 2%:R)
           (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}) :=
    match l with 
    | [:: c & l'] =>
      (rat_to_R
         (expectedValue
            (pdist a0 EpsOk (@CMAX_all _ l))
            (fun a => projT1 c a)) +
       state_expCost2 EpsOk l')%R
    | _ => 0%R
    end.
  
  Definition all_costs' (s : state A) := map (fun c => projT1 c) (all_costs s).
  
  (** The best fixed action (in hindsight) for state [s] *)      
  Definition astar (s : state A) := best_action a0 (all_costs' s).
  Definition OPT (s : state A) := \sum_(c <- all_costs' s) c (astar s).
  Definition OPTR (s : state A) := rat_to_R (OPT s).

  Definition eps (s : state A) := rat_to_R (SEpsilon s).

  Notation size_A := (rat_to_R #|A|%:R).

  Lemma state_expCost12 :
    forall (c' : com A) (s s' : state A) l,
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' ->
      catrev (rev l) (all_costs s) = all_costs s' ->             
      state_expCost1 l (SOutputs s') = state_expCost2 (SEpsilonOk s) l.
  Proof.
    move => c' s s' l; elim: l c' s' => // cs cs' IH c' s' H H2 H3.
    move: (step_plus_mult_weights_refines_pdist H H2 H3).
    case Hx: (SOutputs s') => // [d ds]; rewrite /List.hd_error; case => -> /=.
    rewrite revK; f_equal.
    have [c'' [s'' [H4 H5]]]:
      exists c'' s'',
        [/\ step_plus a0 (mult_weights A) s c'' s''
          , final_com c''
          , catrev (rev cs') (all_costs s) = all_costs s''
          & SOutputs s'' = ds].
    { clear - H H2 H3 Hx.
      rewrite catrevE revK /= in H3; rewrite catrevE revK.
      move: H; move: (mult_weights A) => c; elim.
      move => cx sx c'' s'' cx' sx' Hy Hz; case => xc; case => xs.
      case => H4 H5 H6 <-; exists xc, xs.
      split => //.

      move: cs H3; induction H.
      case: IHstep_plus => //.

    by move => H6 H7; move: (IH _ _ H4 H5 H6); rewrite H7 => ->.
  Admitted.      

  Lemma mult_weights_refines_MWU :
    forall (c' : com A) (s s' : state A) l,
      step_plus a0 (mult_weights A) s c' s' ->
      final_com c' ->
      catrev l (all_costs s) = all_costs s' ->             
      state_expCost (rev l) s' = expCostsR a0 (@all_costs_CMAX' _ (rev l)) (SEpsilonOk s).
  Proof.
    move => c' s s' l; move: s; elim: l.
    { move => s H H2 /= H3.
      rewrite /expCostsR /state_expCost /expCostR /expCost /=.
      have zip_nil T U (l : list T): zip ([::] : list U) l = [::] by elim l.
      by rewrite zip_nil. }
    move => a l IH s H H2 H3.
    rewrite /expCostsR /state_expCost /expCostR /expCost.
    move: (step_plus_mult_weights_refines_pdist H H2 H3).
    case: (SOutputs s') => // x l0 /=; case => ->.
    rewrite IH.

      
      apply: big_sum_ext' => //.
      Focus 2.
      simpl.
      rewrite /zip.
      
      
      

  (** The number of cost vectors received from the environment *)
  Definition T (s : state A) := INR (size (all_costs s)).


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