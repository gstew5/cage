Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith NArith.
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
  | CIter : N.t -> com -> com.
End com.

Arguments EVal [A] _.
Arguments EEps [A].

Arguments CSkip [A].
Arguments CRecv [A].
Arguments CSend [A].
Arguments CIter [A] _ _.

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

Lemma com_Iter_dec A (c : com A) :
  (exists c1 n, c=CIter n c1) \/ forall c1 n, c<>CIter c1 n.
Proof.
  case: c; try solve[right => c0 H; congruence].
  { move => c c0; right => c3; congruence. }
  by move => n c; left; exists c, n.
Qed.  

Lemma com_Skip_dec A (c : com A) : {c=CSkip}+{c<>CSkip}.
Proof. case: c; try solve[left => // | right => H; congruence]. Qed.

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

Definition mult_weights (A : Type) (n : N.t) : com A :=
  CSeq
    (** 1. Initialize weights to uniform *)
    (mult_weights_init A)
    (** 2. The main MWU loop *)
    (CIter n (mult_weights_body A)).

Section client_oracle.
  Local Open Scope ring_scope.
  
  (* Client oracle *)
  Class ClientOracle T oracle_chanty :=
    mkOracle { oracle_recv : forall A : finType,
                 T -> oracle_chanty -> {ffun A -> rat} -> T -> Prop
             ; oracle_send : forall A : Type,
                 T -> A -> oracle_chanty -> T -> Prop
             ; oracle_recv_ok : forall (A : finType) st ch f t' (a : A),
                 @oracle_recv _ st ch f t' -> 
                 0 <= f a <= 1
             }.
End client_oracle.  

Section semantics.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)
  Context T `{Hco : ClientOracle T}.

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
      ; SOutputs : seq (dist A rat_realFieldType)
      ; SChan : oracle_chanty
      ; SOracleSt : T }.

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
    by move => Hx a; apply: (CMAXP _ (projT2 cs) c' Hx a).
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
             (SChan s)
             (SOracleSt s)
        in
        step (CUpdate f) s CSkip s'
             
  | SRecv :
      forall s f t' (Hrecv : oracle_recv (SOracleSt s) (SChan s) f t') pf,
        let: s' :=
           @mkState
             f
             pf
             (existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s)
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)
             (SEpsilonOk s)
             (SOutputs s)
             (SChan s)
             t'
        in 
        step CRecv s CSkip s'

  | SSend :
      forall s ch t',
        let: d:=
           p_aux_dist
             a0
             (SEpsilonOk s)
             (SWeightsOk s)
             CMAX_nil (*Important that [cs := nil] here! 
                        [p_aux_dist] applied to the empty sequence
                        of cost functions specializes to the distribution formed
                        by: SWeights w / \Gamma. *) in
        oracle_send (SOracleSt s) d ch t' -> 
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)
             (SEpsilonOk s)             
             (d :: SOutputs s)
             ch
             t'
        in 
        step CSend s CSkip s'
             
  | SSeq1 :
      forall c2 s,
        step (CSeq CSkip c2) s c2 s
             
  | SSeq2 :
      forall c1 c1' c2 s1 s2,
        step c1 s1 c1' s2 ->
        step (CSeq c1 c2) s1 (CSeq c1' c2) s2

  | SIter0 :
      forall c s,
        step (CIter N0 c) s CSkip s
             
  | SIterS :
      forall c s (n : N.t),
        (0 < n)%N -> 
        step (CIter n c) s (CSeq c (CIter (N.pred n) c)) s.

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
      final_com CSkip.

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
             (SChan s)
             (SOracleSt s)
        in
        stepN (S n) (CUpdate f) s s'
             
  | NRecv :
      forall n s f t' (Hrecv : oracle_recv (SOracleSt s) (SChan s) f t') pf,
        let: s' :=
           @mkState
             f
             pf
             (existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s)
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)             
             (SEpsilonOk s)
             (SOutputs s)
             (SChan s)
             t'
        in 
        stepN (S n) CRecv s s'

  | NSend :
      forall n s ch t',
        let: d:=
           p_aux_dist
             a0
             (SEpsilonOk s)
             (SWeightsOk s)
             CMAX_nil in
        oracle_send (SOracleSt s) d ch t' -> 
        let: s' :=
           @mkState
             (SCosts s)
             (SCostsOk s)
             (SPrevCosts s)
             (SWeights s)
             (SWeightsOk s)
             (SEpsilon s)
             (SEpsilonOk s)
             (d :: SOutputs s)
             ch
             t'
        in 
        stepN (S n) CSend s s'

  | NSeq :
      forall n c1 c2 s1 s1' s2,
        stepN n c1 s1 s1' ->
        stepN n c2 s1' s2 ->        
        stepN (S n) (CSeq c1 c2) s1 s2

  | NIter0 :
      forall n c s,
        stepN n (CIter N0 c) s s
              
  | NIterS :
      forall n (n' : N.t) c s s',
        (0 < nat_of_bin n')%N -> 
        stepN n (CSeq c (CIter (N.pred n') c)) s s' -> 
        stepN (S n) (CIter n' c) s s'.

  Lemma step_plus_trans c1 c2 c3 s1 s2 s3 :
    step_plus c1 s1 c2 s2 ->
    step_plus c2 s2 c3 s3 ->
    step_plus c1 s1 c3 s3.
  Proof.
    move => H H1; induction H.
    apply: step_trans; first by apply: H. apply: H1.
    apply: step_trans. apply: H. by apply IHstep_plus.
  Qed.

  Lemma step_plus_trans2 c1 c2 c3 s1 s2 s3 :
    step_plus c1 s1 c2 s2 ->
    step c2 s2 c3 s3 ->
    step_plus c1 s1 c3 s3.
  Proof.
    move => H H2; induction H.
    { apply: step_trans; first by apply: H. constructor. apply: H2. }
    apply: step_trans. apply: H. by apply: IHstep_plus.
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

  Lemma step_plus_CSkip s c' s' :
    step_plus CSkip s c' s' -> False.
  Proof.
    remember CSkip as c.
    move => H; revert Heqc.
    induction H.
    { move => H2; subst c; inversion H. }
    move => H2; subst c. inversion H.
  Qed.    

  Lemma nat_of_bin_to_nat b : nat_of_bin b = N.to_nat b.
  Proof.
    rewrite /nat_of_bin.
    case: b => //.
    elim => //.
    { move => p /= H; rewrite /Pos.to_nat /=; f_equal.
      rewrite ZL6 NatTrec.doubleE H -muln2 mulnC -multE /=.
      by rewrite -plus_n_O. }
    move => p /= H; rewrite /Pos.to_nat /=; f_equal.
    rewrite ZL6 NatTrec.doubleE H -muln2 mulnC -multE /=.
    by rewrite -plus_n_O.
  Qed.
  
  Lemma step_plus_CIter0 c s c' s' :
    step_plus (CIter 0 c) s c' s' -> s = s'.
  Proof.
    remember (CIter 0 c) as c0.
    move => H; revert c Heqc0.
    induction H.
    { move => c0 H2; subst c.
      inversion H; subst; auto. }
    move => c0 H2; subst c.
    inversion H; subst.
    { destruct (step_plus_CSkip H0). }
    inversion H; subst.
    rewrite nat_of_bin_to_nat in H4.
      by [].
  Qed.      

  Lemma step_seq_inv :
    forall c1 c2 s c' s',
      step (CSeq c1 c2) s c' s' ->
      [/\ c1=CSkip, c'=c2 & s'=s] \/
      exists c1' s'',
        [/\ step c1 s c1' s'', c'=CSeq c1' c2, s'=s'' & c1<>CSkip].
  Proof.
    move => c1 c2 s c' s'; inversion 1; subst; clear H.
    { by left; split. }
    right; exists c1', s'; split => //.
    inversion H5; subst; try solve[inversion 1].
  Qed.

  Lemma step_plus_seq_inv1 :
    forall c1 c2 s c' s',
      step_plus (CSeq c1 c2) s c' s' ->
      final_com c' ->
      c1<>CSkip -> 
      exists s'',
        step_plus c1 s CSkip s'' /\
        step_plus (CSeq CSkip c2) s'' c' s'.
  Proof.
    move => c1 c2 s c' s'.
    remember (CSeq c1 c2) as c => H.
    revert c1 c2 Heqc.
    induction H.
    { move => c1 c2 H2; subst c; inversion 1; subst. clear H0.
      move => H2.
      case: (step_seq_inv H).
      { case => H3 H4 H5.
        subst c1.
        congruence. }
      case => c1' [] s0 []H3 H4 H5 H6.
      exists s0.
      split => //. }
    move => c1 c2 H2; subst c. inversion 1; subst. clear H1.
    move => H2.
    case: (step_seq_inv H).
    { case => H3 H4 H5.
      subst c1.
      congruence. }
    case => c1' [] s0 []H3 H4 H5 H6.
    subst.
    case: (com_Skip_dec c1').
    { move => H7. subst c1'.
      exists s0.
      split => //.
      constructor => //. }
    move => H7.
    case: (IHstep_plus c1' c2 erefl) => // sx [] H8 H9.
    exists sx.
    split => //.
    apply: step_trans.
    apply: H3.
    apply: H8.
  Qed.    
  
  Lemma step_plus_seq_skip :
    forall c s c' s',
      step_plus (CSeq CSkip c) s c' s' ->
      s=s' \/ step_plus c s c' s'.
  Proof.
    move => c s c' s'; remember (CSeq _ _) as c0; induction 1.
    { subst c0; inversion H; subst; first by left.
      by inversion H5; subst; clear H5; left. }
    subst c0; inversion H; subst; clear H; first by right.
    inversion H6; subst; clear H6.
  Qed.
  
  Lemma step_plus_seq_skip_final :
    forall c s c' s',
      final_com c' -> 
      step_plus (CSeq CSkip c) s c' s' ->
      (s=s' /\ final_com c) \/ step_plus c s c' s'.
  Proof.
    move => c s c' s' Hx; remember (CSeq _ _) as c0; induction 1.
    { subst c0; inversion H; subst; first by left; split.
      by inversion H5; subst; clear H5; left. }
    subst c0; inversion H; subst; clear H; first by right.
    inversion H6; subst; clear H6.
  Qed.
  
  Lemma step_plus_CIter_inv n c s c' s' :
    final_com c' ->
    (0 < n)%num -> 
    step_plus (CIter n c) s c' s' ->
    exists s0,
      [/\ step_plus (CSeq c (CIter (N.pred n) c)) s (CIter (N.pred n) c) s0
        & step_plus (CIter (N.pred n) c) s0 c' s'].
  Proof.
    move => H H2.
    remember (CIter n c) as c0.
    move => H0.
    revert c Heqc0 H H2.
    destruct H0.
    { move => c0 H2; subst c. inversion 1; subst. move => H2.
      inversion H; subst => //. }
    move => c0 H2; subst c. inversion 1; subst. clear H1 => H2.
    inversion H; subst => //.
    destruct (com_Skip_dec c0).
    { subst c0.
      inversion H0; subst. clear H0.
      { inversion H1. }
      move: (step_seq_inv H1).
      case; last first.
      { case => x; case => y []; inversion 1. }
      case => _ H4 H5; subst.
      clear H H1.
      exists s''; split => //.
      constructor.
      constructor. }
    case: (step_plus_seq_inv1 H0) => // sx [] H3 H4.
    have H5:
      step_plus (CSeq c0 (CIter (N.pred n) c0)) s''
                (CSeq CSkip (CIter (N.pred n) c0)) sx.
    { apply: step_plus_seq => //. }
    exists sx; split.
    { apply: step_plus_trans; first by apply: H5.
      constructor. constructor. }
    case: (step_plus_seq_skip_final _ H4) => // [][]H6 H8.
    subst sx.
    inversion H8.
  Qed.    

  Lemma step_plus_CIter_skip_split n1 n2 s c' s'' s' :
    step_plus (CIter n1 CSkip) s CSkip s'' ->
    step_plus (CIter n2 CSkip) s'' c' s' ->
    step_plus (CIter (n1+n2) CSkip) s c' s'.
  Proof.
    move: n2 s c' s'' s'.
    set (P (n : N.t) :=
           forall (n2 : N.t) (s : state) (c' : com A) (s'' s' : state),
             step_plus (CIter n CSkip) s CSkip s'' ->
             step_plus (CIter n2 CSkip) s'' c' s' ->
             step_plus (CIter (n + n2) CSkip) s c' s').
    apply: (N.peano_ind P _ _ n1) => //.
    { rewrite /P => n2 s c' s'' s' H H2.
      move: (step_plus_CIter0 H) => ->.
      rewrite N.add_0_l; apply: H2. }
    rewrite /P => n IH n2 s c' s'' s' H H2.
    have Hx: (0 < N.succ n)%num.
    { apply: N.lt_0_succ. }
    have Hy: (0 < N.succ (n + n2))%N.
    { apply/ltP; rewrite nat_of_bin_to_nat N2Nat.inj_succ; omega. }
    case: (step_plus_CIter_inv _ _ H) => //.
    move => x []H3 H4.
    rewrite N.add_succ_l.
    case: (step_plus_seq_skip H3).
    { move => ->.
      apply: step_plus_trans.
      { constructor. constructor => //. }
      rewrite N.pred_succ in H4.
      apply: step_plus_trans; last first.
      { apply: (IH _ _ _ _ _ H4 H2). }
      rewrite N.pred_succ.
      constructor.
      constructor. }
    rewrite N.pred_succ in H3, H4|-* => H5.
    apply: step_plus_trans.
    { constructor. constructor => //. }
    apply: step_plus_trans; last first.
    { have H6: step_plus (CIter n CSkip) s CSkip s''.
      { apply: step_plus_trans; first by apply: H5.
        apply: H4. }
      apply: (IH _ _ _ _ _ H6 H2). }
    rewrite N.pred_succ.
    constructor.
    constructor.
  Qed.    

  Lemma bwahaha (c c1 : com A) : c = CSeq c1 c -> False.
  Proof.
    elim: c c1 => // c IH c' H c1; inversion 1.
    by move: (H _ H3).
  Qed.

  Lemma step_same_false c s c' s' :
    step c s c' s' ->
    c = c' ->
    False.
  Proof.
    induction 1; try solve[inversion 1].
    { move => H2; symmetry in H2; apply: (bwahaha H2). }
    by inversion 1; subst; apply: IHstep.
  Qed.
  
  Lemma step_plus_seq_inv2 c1 c2 s x :
    c1 <> CSkip ->
    (forall s s', step_plus c2 s c2 s' -> False) -> 
    step_plus (CSeq c1 c2) s c2 x -> 
    step_plus c1 s CSkip x.
  Proof.
    remember (CSeq c1 c2) as c.
    move => H Hx H2; revert c1 H Heqc.
    induction H2.
    { move => c1 H3 H4; subst c.
      case: (step_seq_inv H).
      { case => H4; subst c1; congruence. }
      case => c1' []s1' []H4 H5 H6 H7.
      subst s1'.
      case: (com_Skip_dec c1').
      { move => H8. subst c1'.
        constructor; apply: H4. }
      elimtype False; apply: (bwahaha H5). }
    move => c1 H3 H4; subst c.
    case: (step_seq_inv H).
    { case => H4; subst c1; congruence. }
    case => c1' []s1' []H4 H5 H6 H7; subst.
    case: (com_Skip_dec c1').
    { move => H8; subst.
      have ->: s' = s1'.
      { case: (step_plus_seq_skip H2); first by move => ->.
        move => H5.
        elimtype False.
        apply: (Hx _ _ H5). }
      apply: step1.
      apply: H4. }
    move => Hnskip.
    apply: step_trans; first by apply: H4.
    apply: IHstep_plus => //.
  Qed.

  (*the kinds of traces generated by CIter*)
  Inductive iter_step : nat -> com A -> nat -> com A -> Prop :=
  | iter_step0 :
      forall c,
        iter_step 0 (CIter 0 c) 0 CSkip
  | iter_step_unfold :
      forall c n,
        (0 < n)%num -> 
        iter_step (N.to_nat n) (CIter n c) (N.to_nat n) (CSeq c (CIter (N.pred n) c))
  | iter_step1 :
      forall c c' c2 n,
        iter_step (S (N.to_nat n)) (CSeq c (CIter n c2)) (S (N.to_nat n)) (CSeq c' (CIter n c2))
  | iter_step_done :
      forall c n,
        iter_step (S (N.to_nat n)) (CSeq CSkip (CIter n c)) (N.to_nat n) (CIter n c).

  (*control continuations derived from CIter*)
  Inductive is_iter : nat -> com A -> Prop :=
  | is_iter_CSkip : is_iter 0 CSkip
  | is_iter_CIter :
      forall c n, is_iter (N.to_nat n) (CIter n c)
  | is_iter_CSeq_CIter :
      forall c c' n, is_iter (S (N.to_nat n)) (CSeq c (CIter n c')).
  
  Lemma step_iter_step c s c' s' n :
    step c s c' s' ->
    is_iter n c ->
    exists n', iter_step n c n' c' /\ is_iter n' c'.
  Proof.
    induction 1;
    try solve[inversion 1|
              inversion 1; subst; eexists; split; try constructor].
    inversion 1; subst.
    exists (S (N.to_nat (N.pred n0))).
    split; try constructor.
    have Hx: (0 < n0)%num.
    { clear - H; rewrite /N.lt N2Nat.inj_compare.
      rewrite nat_of_bin_to_nat in H.
      by rewrite -nat_compare_lt /lt; apply/leP. }
    have ->: (N.to_nat (N.pred n0)).+1 = N.to_nat n0.
    { rewrite -N2Nat.inj_succ N.succ_pred_pos => //. }
    constructor => //.
  Qed.

  Inductive iter_plus : nat -> com A -> nat -> com A -> Prop :=
  | iter1 :
      forall n c n' c',
        iter_step n c n' c' ->
        iter_plus n c n' c'
  | iter_trans :
      forall n c n'' c'' n' c',
        iter_step n c n'' c'' -> 
        iter_plus n'' c'' n' c' ->
        iter_plus n c n' c'.
  
  Lemma step_plus_iter_plus n c s c' s' :
    step_plus c s c' s' ->    
    is_iter n c ->
    exists n', iter_plus n c n' c' /\ is_iter n' c'.
  Proof.
    move => H.
    revert n.
    induction H.
    { move => n H2; case: (step_iter_step H H2) => n' []H3 H4.
      exists n'; split; auto.
      constructor; auto. }
    move => n H2.
    case: (step_iter_step H H2) => n'' []H3 H4.
    case: (IHstep_plus _ H4) => n' []H5 H6.
    exists n'. split; auto.
    apply: iter_trans; first by apply: H3.
    apply: H5.
  Qed.    

  Definition is_literal_iter (c : com A) :=
    match c with
    | CIter _ _ => True
    | _ => False
    end.

  Lemma iter_step_literal_ord n c n' c' :
    iter_step n c n' c' ->
    (is_literal_iter c' /\ (n' < n)%coq_nat) \/
    (~is_literal_iter c' /\ n' = n).
  Proof.
    induction 1; try solve[right; split => //].
    left; split => //.
  Qed.    

  Lemma iter_plus_literal_ord n c n' c' :
    iter_plus n c n' c' ->
    (is_literal_iter c' /\ (n' < n)%coq_nat) \/
    (~is_literal_iter c' /\ (n' <= n)%coq_nat).
  Proof.
    induction 1.
    { case: (iter_step_literal_ord H) => [][]H1 H2.
      left => //.
      subst n'; right => //. }
    case: IHiter_plus => [][]H1 H2.
    { case: (iter_step_literal_ord H) => [][]H3 H4.
      { left.
        split => //.
        omega. }
      left.
      split => //.
      omega. }
    case: (iter_step_literal_ord H) => [][]H3 H4.
    { right; split => //. omega. }
    subst n''.
    right; split => //.
  Qed.    

  Lemma step_plus_iter_same_false n c s s' :
    step_plus (CIter n c) s (CIter n c) s' -> False.
  Proof.
    move/step_plus_iter_plus; move/(_ (N.to_nat n)); case; first by constructor.
    move => n' []H H2.
    case: (iter_plus_literal_ord H) => [][]H1 H3.
    { inversion H2; subst. omega. }
    by apply: H1.
  Qed.

  Lemma step_plus_seq_iter_inv p c s x :
    c <> CSkip -> 
    step_plus (CSeq c (CIter p c)) s (CIter p c) x -> 
    step_plus c s CSkip x.
  Proof.
    move => H H2.
    apply: step_plus_seq_inv2 => //.
    { apply: (@step_plus_iter_same_false p c). }
    apply: H2.
  Qed.    
  
  Lemma step_plus_iter_split n1 n2 c s s'' c' s' :
    step_plus (CIter n1 c) s CSkip s'' ->
    step_plus (CIter n2 c) s'' c' s' ->
    step_plus (CIter (n1+n2) c) s c' s'.
  Proof.
    case (com_Skip_dec c).
    { move => H; subst c => H2 H3.
      apply: (step_plus_CIter_skip_split H2 H3). }
    move: n2 c s s'' c' s'.
    set (P (n : N.t) :=
      forall (n2 : N.t) (c : com A) (s s'' : state) (c' : com A) (s' : state),
        c <> CSkip ->
        step_plus (CIter n c) s CSkip s'' ->
        step_plus (CIter n2 c) s'' c' s' ->
        step_plus (CIter (n + n2) c) s c' s').
    apply: (N.peano_ind P _ _ n1).
    { move => n2 c s s'' c' s' Hnskip; move/step_plus_CIter0 => -> H.
        by rewrite N.add_0_l. }
    rewrite /P; move => p IH n2 c s s'' c' s' Hnskip H H2.
    rewrite N.add_succ_l.
    case: (step_plus_CIter_inv _ _ H) => //.
    { apply: N.lt_0_succ. }
    move => x []H3 H4.
    rewrite N.pred_succ in H3, H4.    
    apply: step_plus_trans.
    { apply: step_plus_trans.
      { constructor.
        constructor.
        rewrite nat_of_bin_to_nat.
        apply/ltP; rewrite N2Nat.inj_succ; omega. }
      rewrite N.pred_succ.
      move: (IH _ _ _ _ _ _ Hnskip H4 H2) => H5.
      apply: step_plus_seq.
      have H6: step_plus c s CSkip x.
      { apply: step_plus_seq_iter_inv => //.
        apply: H3. }
      apply: H6. }
    apply: step_plus_trans.
    { constructor.
      constructor. }
    apply: (IH _ _ _ _ _ _ Hnskip H4 H2).
  Qed.

  Lemma step_plus_iter1 c s s' :
    step_plus c s CSkip s' -> 
    step_plus (CIter 1 c) s CSkip s'.
  Proof.
    move => H.
    apply: step_trans.
    constructor => //.
    apply: step_plus_trans.
    apply: step_plus_seq.
    apply: H.
    apply: step_trans.
    constructor.
    have ->: N.pred 1 = 0%num by [].
    constructor.
    constructor.
  Qed.    
  
  Lemma step_plus_iter_flip_aux n c s c0 s0 cx sx :
    (0 < n)%num -> 
    final_com c0 ->
    final_com cx -> 
    step_plus (CIter (N.pred n) c) s c0 s0 ->
    step_plus c s0 cx sx -> 
    step_plus (CIter n c) s cx sx.
  Proof.
    move => H H1 H2 H3 H4.
    have ->: n = (N.pred n + 1)%num.
    { rewrite N.add_pred_l.
      { by rewrite N.add_1_r N.pred_succ. }
      move => H5; subst n.
        by apply: (N.nlt_0_r 0). }
    apply: (@step_plus_iter_split (N.pred n) 1); last first.
    { inversion H2; subst.
      apply: step_plus_iter1.
      apply: H4. }
    inversion H1; subst.
    apply: H3.
  Qed.    
  
  Lemma step_plus_iter_flip n c s c0 s0 cx sx :
    final_com c0 ->
    final_com cx -> 
    step_plus (CIter n c) s c0 s0 ->
    step_plus c s0 cx sx -> 
    step_plus (CSeq c (CIter n c)) s cx sx.
  Proof.
    inversion 1; subst; inversion 1; subst.
    move => H1 H2. clear H H0.
    destruct n.
    { move: (step_plus_CIter0 H1) => H4; subst.
      have H4: step_plus (CSeq c (CIter 0 c)) s0 (CSeq CSkip (CIter 0 c)) sx.
      { apply: step_plus_seq => //. }
      apply: step_plus_trans; first by apply: H4.
      apply: step_trans.
      constructor.
      constructor.
      constructor. }
    case: (step_plus_CIter_inv _ _ H1) => // sy []H4 H5. 
    have H3: step_plus (CSeq c (CIter (N.pred (N.pos p)) c)) s CSkip s0.
    { apply: step_plus_trans; first by apply: H4.
      apply: H5. }
    case: (com_Skip_dec c).
    { move => H6; subst c.
      apply: step_trans; first by constructor.
      apply: step_plus_trans; last by apply: H2.
        by []. }
    move => H6.
    case: (step_plus_seq_inv1 H3) => // sz []H7 H8.
    have H9: step_plus (CSeq c (CIter (N.pos p) c)) s
                       (CSeq CSkip (CIter (N.pos p) c)) sz.
    { apply: step_plus_seq => //. }
    apply: step_plus_trans.
    { apply: H9. }
    apply: step_trans.
    { constructor. }
    case: (step_plus_seq_skip_final _ H8) => //.
    { case => H10 H11; subst. inversion H11. }
    move => H10.
    clear - H10 H2.
    apply: step_plus_iter_flip_aux => //.
    apply: H10.
    apply: H2.
  Qed.
  
  Lemma stepN_weaken c s s' n n' :
    (n' >= n)%coq_nat ->
    stepN n c s s' ->
    stepN n' c s s'.
  Proof.
    set P := fun n => forall c s s' n', (n' >= n)%coq_nat -> stepN n c s s' -> stepN n' c s s'.
    move: c s s' n'; change (P n).
    apply (well_founded_ind lt_wf); move {n}; case.
    { move => ?; rewrite /P => c s s' n' _; inversion 1; try solve[constructor]. }
    move => n IH; rewrite /P => c s s' n' H.
    inversion 1; subst.
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor. }
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor. }
    { move {IH}; case: n' H P; try solve[move => X; elimtype False; omega].
      constructor => //. }
    { rewrite /P in IH; move {P}.
      case: n' H IH; try solve[move => X; elimtype False; omega].
      move => n0 H4 IH.
      have H5: (n0 >= n)%coq_nat by omega.
      constructor => //. }
    { rewrite /P in IH; move {P}.
      case: n' H IH; try solve[move => X; elimtype False; omega].
      move => n0 H4 IH.
      have H5: (n0 >= n)%coq_nat by omega.                
      apply: NSeq.
      apply: (IH n); try omega. apply: H2.
      apply: (IH n); try omega. apply: H3. }
    { rewrite /P in IH; move {P}.
      case: n' H IH; try solve[move => X; elimtype False; omega].
      move => n0 H4 IH; constructor => //. }
    rewrite /P in IH; move {P}.
    case: n' H IH; try solve[move => X; elimtype False; omega].
    move => n0 H4 IH; constructor => //.
    apply: (IH n); try solve[omega].
    by [].
  Qed.        
  
  Lemma step_stepN c s c'' s'' s' n :
    step c s c'' s'' ->
    stepN n c'' s'' s' ->
    exists n', (n' > n)%coq_nat /\ stepN n' c s s'.
  Proof.
    move => H; move: H s'; induction 1; subst;
      try solve[inversion 1; subst; eexists; split => //; constructor => //].
    { move => s' H; exists n.+1; split => //.
      apply: NSeq; first by constructor.
      by []. }
    inversion 1; subst c0 c3 s0 s3 n.
    have H8: (n0.+1 >= n0)%coq_nat by omega.
    case: (IHstep _ (stepN_weaken H8 H4)) => n []H1 H2.
    exists n.+1; split; try omega.
    have H9: (n >= n0)%coq_nat by omega.
    apply: NSeq.
    apply: H2.
    apply: stepN_weaken.
    apply: H9.
    apply: H7.
  Qed.

  Lemma step_stepN_final c s c' s' :
    step c s c' s' ->
    final_com c' -> 
    exists n, stepN n c s s'.
  Proof.        
    move => H H2; inversion H2; subst; move {H2}.
    inversion H; subst; try solve[exists (S O); constructor => //].
    exists (S (S O)). apply: NSeq. constructor. constructor.
  Qed.    
    
  Lemma step_plus_stepN c s c' s' :
    step_plus c s c' s' ->
    final_com c' -> 
    exists n, stepN n c s s'.
  Proof.
    move => H H2; inversion H2; subst; induction H.
    { apply: step_stepN_final => //. inversion H2; subst => //. }
    inversion H2; subst. clear H2.
    inversion H; subst.
    { case: IHstep_plus => // n; inversion 1; subst. exists (S n); constructor. }
    { case: IHstep_plus => // n; inversion 1; subst. exists (S n); constructor => //. }
    { case: IHstep_plus => // n; inversion 1; subst. exists (S n); constructor => //. }
    { case: IHstep_plus => // n H2.
      exists (S n).
      apply: NSeq; first by constructor.
      by []. }
    { inversion H.
      { subst c1 c2 s0 s''.
        case: IHstep_plus => // n H6.
        exists n.+1.
        apply: NSeq.
        constructor.
        apply: H6. }
      subst c0 c3 s1 c1'0 s2.
      case: IHstep_plus => // n H8.
      clear - H1 H8.
      inversion H8; subst.
      case: (step_stepN H1 H3) => n []H9 H10.
      exists n.+1.
      apply: NSeq.
      apply: H10.
      apply: stepN_weaken; last by apply: H6.
      omega. }
    { case: IHstep_plus => // n H2.
      case: (step_stepN H H2) => n' []H3 H4.
      exists n' => //. }
    case: IHstep_plus => // n' H1'.
    case: (step_stepN H H1') => n'' []H2 H3.
    exists n''.
    apply: H3.
  Qed.      
End semantics.

Section mult_weights_refinement.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A.
  Context T oracle_chanty `{Hco : ClientOracle T oracle_chanty}.

  Notation "'state' A" := (@state A T oracle_chanty) (at level 50).
  
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
    let: old_costs := existT _ (SCosts s) (SCostsOk s) :: SPrevCosts s in
    let: d := p_aux_dist
                a0
                (SEpsilonOk s)
                (update_weights_gt0 (SEpsilonOk s) pf (SWeightsOk s))         
                (CMAX_nil (A:=A))
    in 
    @mkState A T oracle_chanty
      c
      pf
      old_costs
      (update_weights (SEpsilon s) (SWeights s) c)
      (update_weights_gt0 (SEpsilonOk s) pf (SWeightsOk s))
      (SEpsilon s)
      (SEpsilonOk s)
      (d :: SOutputs s)
      (** The functional implementation doesn't even bother to simulate 
          the oracle state -- it doesn't matter once we've extracted the 
          cost vector history from a particular stepN execution. *)
      (SChan s)
      (SOracleSt s).

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
             (s : state A) (ch : oracle_chanty) (t : T)
    : state A :=
    @mkState A T oracle_chanty
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
         :: SOutputs s)
      ch
      t.

  Definition mult_weights1
             (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1})
             (s : state A) ch t
    : state A :=
    mult_weights1_loop_left cs (mult_weights1_init s ch t).

  (** Now the proof: *)

  Definition upto_oracle_eq (s s' : state A) : Prop :=
    [/\ SCosts s = SCosts s'
     , SPrevCosts s = SPrevCosts s'                          
     , SWeights s = SWeights s'
     , SEpsilon s = SEpsilon s'
     & SOutputs s = SOutputs s'].                        

  Lemma upto_oracle_eq_refl s : upto_oracle_eq s s.
  Proof. by rewrite /upto_oracle_eq; split. Qed.

  Lemma upto_oracle_eq_sym s s' :
    upto_oracle_eq s s' -> upto_oracle_eq s' s.
  Proof. by move => H; split; case: H. Qed.

  Lemma upto_oracle_eq_trans s1 s2 s3 :
    upto_oracle_eq s1 s2 ->
    upto_oracle_eq s2 s3 ->
    upto_oracle_eq s1 s3.
  Proof.
    case => H1 H2 H3 H4 H5.
    case => H1' H2' H3' H4' H5'.
    split; first by rewrite H1 H1'.
    by rewrite H2 H2'.
    by rewrite H3 H3'.
    by rewrite H4 H4'.
    by rewrite H5 H5'.
  Qed.      
  
  Lemma stepN_mult_weights_refines_mult_weights1_one :
    forall n (s s' : state A),
      stepN a0 n (mult_weights_body A) s s' ->
      upto_oracle_eq (mult_weights1_one (SCostsOk s') s) s'.
  Proof.
    move => n s s'.
    inversion 1; subst. clear H.
    inversion H3; subst. clear H3.
    inversion H6; subst. clear H6.
    inversion H2; subst. simpl in *. clear H2.
    inversion H5; subst. simpl in *. clear H5.
    rewrite /mult_weights1_one /upto_oracle_eq; split => //=.
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

  Lemma step_all_costs_cat :
    forall c s c' s',
      step a0 c s c' s' ->
      exists l, all_costs s' = l ++ all_costs s.
  Proof.
    move => c s c' s'; induction 1; try solve[exists nil => //].
    { exists [:: existT (fun c1 : {ffun A->rat} => forall a, 0 <= c1 a <= 1) f
                 (fun a => oracle_recv_ok (A:=A) a Hrecv)].
      rewrite /all_costs /=; f_equal; f_equal.
      apply: proof_irrelevance. }
    by case: IHstep => l ->; exists l.                    
  Qed.
  
  Lemma mult_weights1_one_all_costs s s' : 
    upto_oracle_eq (mult_weights1_one (c:=SCosts s') (SCostsOk s') s) s' ->
    all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s].
  Proof.
    rewrite /all_costs; case => H H1 H2 H3 H4.
    by f_equal; rewrite -H1.
  Qed.

  Lemma cat_cons' Tx (x : Tx) l1 l2 : l1 ++ x :: l2 = rcons l1 x ++ l2.
  Proof. by elim: l1 l2 x => // a l IH l2 x /=; rewrite IH. Qed.

  Lemma rcons_inj Tx (x y : Tx) l1 l2 :
    rcons l1 x = rcons l2 y -> l1 = l2 /\ x = y.
  Proof.
    elim: l1 l2.
    { case => /=; first by case => ->; split.
      move => a l2 /=; case => ->; case: l2 => //. }
    move => a l1 IH; case => /=.
    { case => ->; case: l1 IH => //. }
    by move => a1 l2; case => -> H2; case: (IH _ H2) => -> ->.
  Qed.
    
  Lemma cat_inj Tx (l : list Tx) l0 s :
    l ++ s = l0 ++ s -> l = l0.
  Proof.
    elim: s l0 l; first by move => l0 l; rewrite 2!cats0.
    move => a l IH l0 l1; rewrite 2!cat_cons' => H.
    by move: (IH _ _ H) => H2; case: (rcons_inj H2) => ->.
  Qed.

  Lemma size_rev_cat1 Tx (a : Tx) l s :
    (0 < size (rev l ++ [:: a & s]))%N.
  Proof.
    rewrite size_cat; elim: l => // a1 l IH.
    by rewrite size_rev.
  Qed.      

  Lemma rev_nil Tx : rev (T:=Tx) nil = nil.
  Proof. by []. Qed.

  Lemma rcons_nil_inv Tx (l : list Tx) x :
    [::] = rcons l x -> False.
  Proof. by elim: l. Qed.
  
  Lemma rev_inj Tx (l : list Tx) l0 :
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
                        
  Lemma catrev_cons_inv Tx (l : list Tx) s l0 x :
    catrev l s = catrev l0 [:: x & s] ->
    l = [:: x & l0].
  Proof. by rewrite 2!catrevE -cat_rcons -rev_cons; move/cat_inj/rev_inj. Qed.

  Lemma catrev_iter n c s s' nx :
    (forall m s s', stepN a0 m c s s' ->
                    exists x, all_costs s' = x :: all_costs s) ->
    stepN a0 n (CIter nx c) s s' -> 
    exists l0 : seq {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1},
     all_costs s' = catrev l0 (all_costs s).
  Proof.
    set (P :=
           fun (n : nat) =>
             forall s nx,
               (forall m s s', stepN a0 m c s s' ->
                               exists x, all_costs s' = x :: all_costs s) ->
               stepN a0 n (CIter nx c) s s' -> 
               exists l0 : seq {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1},
                 all_costs s' = catrev l0 (all_costs s)).
    move: s nx; change (P n).
    apply: (well_founded_ind lt_wf); case.
    { rewrite /P => H s nx H2. inversion 1. subst. by exists [::]. }
    rewrite /P => n0 IH s nx H; inversion 1; subst; first by exists [::].
    destruct n0; first by inversion H7. inversion H7; subst.
    case: (H _ _ _ H5) => x => H10.
    have H11: (n0 < n0.+2)%coq_nat by omega.
    case: (IH _ H11 s1' _ H H9) => l => H12.
    by exists [:: x & l]; rewrite H12 H10.
  Qed.    

  Lemma catrev_inj_nil Tx (l : list Tx) x : catrev l x = x -> l = [::].
  Proof.
    rewrite catrevE -(cat0s x); move/cat_inj.
    by rewrite -(revK [::]) => /rev_inj => ->.
  Qed.
  
  Lemma stepN_iter_foldR :
    forall n nx (s s' : state A) l c (R : state A -> state A -> Prop)
           (Hrefl : forall s, R s s)
           (Hsym : forall s s', R s s' -> R s' s)           
           (Htrans : forall s1 s2 s3, R s1 s2 -> R s2 s3 -> R s1 s3)
           (f : forall c : {ffun A -> rat},
               (forall a, 0 <= c a <= 1) ->
               state A -> state A)
           (Hf : forall c pf s1 s2,
               R s1 s2 ->
               R (f c pf s1) (f c pf s2)),
      (forall n s s', stepN a0 n c s s' -> R (f (SCosts s') (SCostsOk s') s) s') ->
      (forall n s s',
          stepN a0 n c s s' ->
          all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) ->
      stepN a0 n (CIter nx c) s s' ->
      catrev l (all_costs s) = all_costs s' ->
      exists s0,
        [/\ R s0 s
         & R (foldl (fun s c => f (projT1 c) (projT2 c) s) s0 l) s'].
  Proof.
    set P :=
      fun (n : nat) =>               
        forall nx (s s' : state A) l c (R : state A -> state A -> Prop)
               (Hrefl : forall s, R s s)
               (Hsym : forall s s', R s s' -> R s' s)
               (Htrans : forall s1 s2 s3, R s1 s2 -> R s2 s3 -> R s1 s3)
               (f : forall c : {ffun A -> rat},
                   (forall a, 0 <= c a <= 1) ->
                   state A -> state A)
               (Hf : forall c pf s1 s2,
                   R s1 s2 ->
                   R (f c pf s1) (f c pf s2)),
          (forall n s s', stepN a0 n c s s' ->
                          R (f (SCosts s') (SCostsOk s') s) s') ->
          (forall n s s',
              stepN a0 n c s s' ->
              all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) ->
          stepN a0 n (CIter nx c) s s' ->
          catrev l (all_costs s) = all_costs s' ->
          exists s0,
            [/\ R s0 s
             & R (foldl (fun s c => f (projT1 c) (projT2 c) s) s0 l) s'].
    move => n; change (P n).
    apply (well_founded_ind lt_wf); case.
    { move => _; rewrite /P => nx s s' l c R Hrefl Hsym Htrans f Hf H H2.
      inversion 1; subst.
      move => Hx; have ->: l = [::] by move: (catrev_inj_nil Hx).
      exists s'; split => //. }
    rewrite /P => m IH nx s s' l c R Hrefl Hsym Htrans f Hf H H2.
    inversion 1; subst.
    { move => Hx; have ->: l = [::] by apply: (catrev_inj_nil Hx).
      by exists s'. }
    clear H0 => H0.
    inversion H8; subst. clear H8 P.
    have Hn0: (n0 < n0.+2)%coq_nat by omega.
    move: (H2 _ _ _ H6) => H7.
    have Hx: l = [:: existT _ _ (SCostsOk s1') & behead l].
    { have H11: exists l0, all_costs s' = catrev l0 (all_costs s1').
      { apply: catrev_iter; last by apply: H10.
        move => m sx sx' Hx.
        exists (existT _ _ (SCostsOk sx')).
        by rewrite (H2 _ _ _ Hx). }
      case: H11 => l0 H11.
      rewrite H11 H7 /= in H0.
      move: (catrev_cons_inv H0).
      by clear H0; case: l => // a l' /=; case => -> ->. }
    rewrite Hx /=.
    have H11: R (f (SCosts s1') (SCostsOk s1') s) s1'.
    { by apply: H; apply: H6. }
    case: (IH _ Hn0 (N.pred nx) s1' s' (behead l) c R Hrefl Hsym Htrans f) => //.
    by rewrite H7 Hx -H0 Hx.
    move => sx []Hr Hs.
    exists s; split => //=.
    move: Hs.
    set (F := (fun (s0 : state A)
           (c0 : {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1}) =>
                 f (projT1 c0) (projT2 c0) s0)).
    have Hr': R sx (f (SCosts s1') (SCostsOk s1') s).
    { apply: Htrans; first by apply: Hr.
      by apply: Hsym. }
    clear - Hf Hr' Htrans Hsym Hrefl.
    move: (behead l) Hr' => lx.
    have <-: rev (rev lx) = lx by rewrite revK.
    rewrite 2!foldl_rev; move: (rev lx) => ly.
    set (G := foldr
         (fun x : {c : {ffun A -> rat} & forall a0 : A, 0 <= c a0 <= 1} =>
            F^~ x)).
    set (sy := f (SCosts s1') (SCostsOk s1') s).
    clear - R Hsym Htrans Hrefl Hf lx; elim: ly sx sy s'.
    { move => sx sy s' H /= Hr.
      apply: Htrans; last by apply: Hr.
        by apply: Hsym. }
    move => a l IH sx sy s' Hr /=.
    rewrite /F => Hr'; apply: Htrans; last by apply: Hr'.
    by apply: Hf; apply: IH; first by apply: Hr.
  Qed.

  Lemma stepN_iter_fold_upto :
    forall n nx (s s' : state A) l c 
           (f : forall c : {ffun A -> rat},
               (forall a, 0 <= c a <= 1) ->
               state A -> state A)
           (Hf : forall c pf s1 s2,
               upto_oracle_eq s1 s2 ->
               upto_oracle_eq (f c pf s1) (f c pf s2)),
      (forall n s s',
          stepN a0 n c s s' ->
          upto_oracle_eq (f (SCosts s') (SCostsOk s') s) s') ->
      (forall n s s',
          stepN a0 n c s s' ->
          all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) ->
      stepN a0 n (CIter nx c) s s' ->
      catrev l (all_costs s) = all_costs s' ->
      upto_oracle_eq (foldl (fun s c => f (projT1 c) (projT2 c) s) s l) s'.
  Proof.
    move => n nx s s' l c f Hf H H2 H3 H4.
    case:
      (@stepN_iter_foldR
         n nx s s' l c
         upto_oracle_eq
         upto_oracle_eq_refl upto_oracle_eq_sym upto_oracle_eq_trans
         f) => //.
    move => x []H5.
    set (F := (fun (s0 : state A)
           (c0 : {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1}) =>
                 f (projT1 c0) (projT2 c0) s0)).
    have <-: rev (rev l) = l by apply: revK.
    rewrite 2!foldl_rev; move: (rev l) => lx.
    set (G := (fun x0 : {c0 : {ffun A -> rat} & forall a : A, 0 <= c0 a <= 1} =>
         F^~ x0)).
    clear H3 H4; elim: lx x s s' H5.
    { move => x s s' H3 /= H4.
      apply: upto_oracle_eq_trans.
      { apply: upto_oracle_eq_sym; apply: H3. }
      apply: H4. }
    move => a ly IH /= x s s' H3 H4.
    apply: upto_oracle_eq_trans; last by apply: H4.
    apply: Hf; apply: upto_oracle_eq_trans.
    { apply: IH.
      apply: H3.
      apply: upto_oracle_eq_refl. }
    apply: upto_oracle_eq_refl.
  Qed.    
    
  (** FIXME: This lemma is provable from the foldR version above *)
  Lemma stepN_iter_fold :
    forall n nx (s s' : state A) l c
           (f : forall c : {ffun A -> rat},
               (forall a, 0 <= c a <= 1) ->
               state A -> state A),
      (forall n s s', stepN a0 n c s s' -> f (SCosts s') (SCostsOk s') s = s') ->
      (forall n s s',
          stepN a0 n c s s' ->
          all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) -> 
      stepN a0 n (CIter nx c) s s' ->
      catrev l (all_costs s) = all_costs s' -> 
      foldl (fun s c => f (projT1 c) (projT2 c) s) s l = s'.
  Proof.
    set P :=
      fun (n : nat) =>               
        forall nx (s s' : state A) l c
               (f : forall c : {ffun A -> rat},
                   (forall a, 0 <= c a <= 1) ->
                   state A -> state A),
          (forall n s s', stepN a0 n c s s' -> f (SCosts s') (SCostsOk s') s = s') ->
          (forall n s s',
              stepN a0 n c s s' ->
              all_costs s' = [:: existT _ _ (SCostsOk s') & all_costs s]) -> 
          stepN a0 n (CIter nx c) s s' ->
          catrev l (all_costs s) = all_costs s' -> 
          foldl (fun s c => f (projT1 c) (projT2 c) s) s l = s'.
    move => n; change (P n).
    apply (well_founded_ind lt_wf); case.
    { move => _; rewrite /P => nx s s' l c f H H2; inversion 1. subst.
      move => Hx; have ->: l = [::] by apply: (catrev_inj_nil Hx). by []. }
    rewrite /P => m IH nx s s' l c f H H2. inversion 1; subst.
    { move => Hx; have ->: l = [::] by apply: (catrev_inj_nil Hx). by []. }
    clear H0 => H0.
    inversion H8; subst. clear H8 P.
    have Hn0: (n0 < n0.+2)%coq_nat by omega.
    move: (H2 _ _ _ H6) => H7.
    have Hx: l = [:: existT _ _ (SCostsOk s1') & behead l].
    { have H11: exists l0, all_costs s' = catrev l0 (all_costs s1').
      { apply: catrev_iter; last by apply: H10.
        move => m sx sx' Hx.
        exists (existT _ _ (SCostsOk sx')).
        by rewrite (H2 _ _ _ Hx). }
      case: H11 => l0 H11.
      rewrite H11 H7 /= in H0.
      move: (catrev_cons_inv H0).
      by clear H0; case: l => // a l' /=; case => -> ->. }
    rewrite Hx /=.
    have H11: f (SCosts s1') (SCostsOk s1') s = s1'.
    { by apply: H; apply: H6. }
    rewrite (IH _ Hn0 (N.pred nx) (f (SCosts s1') (SCostsOk s1') s) s' (behead l) c) => //.
    by rewrite H11; apply: H10.
    by rewrite H11 H7 -H0 Hx.
  Qed.
  
  Lemma mult_weights1_loop_left_foldl
        (cs : seq {c : {ffun A -> rat} & forall a, 0 <= c a <= 1}) (s : state A) :
    mult_weights1_loop_left cs s =
    foldl (fun s c => mult_weights1_one (projT2 c) s) s cs.
  Proof. by elim: cs s => // c cs' IH s /=; rewrite IH. Qed.
  
  Lemma stepN_mult_weights_refines_mult_weights1_loop :
    forall n nx (s s' : state A) l,
      stepN a0 n (CIter nx (mult_weights_body A)) s s' ->
      catrev l (all_costs s) = all_costs s' ->
      upto_oracle_eq (mult_weights1_loop_left l s) s'.
  Proof.
    move => n nx s s' l H H2.
    rewrite mult_weights1_loop_left_foldl.
    apply: (stepN_iter_fold_upto (n:=n) (nx:=nx)
                                 (c:=mult_weights_body A) (s':=s')) => //.
    { move => c pf s1 s2 H3.
      case: H3 => H1 H2' H3 H4 H5.
      split => //.
      { simpl; f_equal => //.
        move: (SCostsOk s1) (SCostsOk s2); rewrite H1 => pf1 pf2.
        f_equal.
        apply: proof_irrelevance. }
      by rewrite /= H3 H4.
      rewrite /mult_weights1_one /= H5; f_equal.
      move: (SEpsilonOk s1) (SEpsilonOk s2); rewrite H4 => pf1 pf2.
      move: (SWeightsOk s1) (SWeightsOk s2); rewrite H3 => pf3 pf4.
      f_equal; first by apply: proof_irrelevance.
      f_equal; first by apply: proof_irrelevance.
      apply: proof_irrelevance. }
    { move => m sx sx' H3.
      apply: stepN_mult_weights_refines_mult_weights1_one.
      apply: H3. }
    move => m sx sx' H3.
    apply: mult_weights1_one_all_costs.
    apply: stepN_mult_weights_refines_mult_weights1_one.
    apply: H3.
  Qed.

  Lemma stepN_mult_weights_refines_mult_weights1_init :
    forall n (s s' : state A) pf,
      let: d := p_aux_dist (A:=A) a0 (eps:=SEpsilon s) (SEpsilonOk s)
                           (w:=[ffun=> Q_to_rat 1]) pf (cs:=[::]) (CMAX_nil (A:=A)) in
      stepN a0 n (mult_weights_init A) s s' ->
      exists ch t',
      mult_weights1_init s ch t' = s'.
  Proof.
    move => n s s' pf; inversion 1; subst.
    inversion H6; subst.
    inversion H3; subst.
    simpl in *.
    exists ch, t'.    
    rewrite /mult_weights1_init; f_equal.
    apply: proof_irrelevance.
    f_equal.
    f_equal.
    apply: proof_irrelevance.
  Qed.
  
  Lemma stepN_mult_weights_refines_mult_weights1 :
    forall n nx (s s' : state A) l pf,
      let: d := p_aux_dist (A:=A) a0 (eps:=SEpsilon s) (SEpsilonOk s)
                           (w:=[ffun=> Q_to_rat 1]) pf (cs:=[::]) (CMAX_nil (A:=A)) in
      let: p := oracle_send (SOracleSt s) d in
      stepN a0 n (mult_weights A nx) s s' ->
      catrev l (all_costs s) = all_costs s' ->
      exists ch t',
      upto_oracle_eq (mult_weights1 l s ch t') s'.
  Proof.
    move => n nx s s' l pf; inversion 1; subst.
    move: (stepN_mult_weights_refines_mult_weights1_init pf H3) => []ch []t' H7.
    rewrite -H7 in H6.
    rewrite /mult_weights1 => H8.
    exists ch, t'.
    apply: stepN_mult_weights_refines_mult_weights1_loop.
    apply: H6.
    apply: H8.
  Qed.

  Lemma step_plus_mult_weights_refines_mult_weights1 :
    forall nx (s s' : state A) c' l pf,
      let: d := p_aux_dist (A:=A) a0 (eps:=SEpsilon s) (SEpsilonOk s)
                           (w:=[ffun=> Q_to_rat 1]) pf (cs:=[::]) (CMAX_nil (A:=A)) in
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' ->
      catrev l (all_costs s) = all_costs s' ->
      exists ch t',
      upto_oracle_eq (mult_weights1 l s ch t') s'.
  Proof.
    move => nx s s' c' l pf; move/step_plus_stepN => H H2; case: (H H2) => n H3 H4.
    apply: stepN_mult_weights_refines_mult_weights1 => //.
    apply: H3.
  Qed.
  
  Lemma step_plus_send_all_costs :
    forall s c' s',
      step_plus a0 CSend s c' s' ->
      all_costs s' = all_costs s /\ c'=CSkip.
  Proof.
    move => s c' s'.
    inversion 1; subst.
    { inversion H0; subst => //. }
    clear H.
    inversion H0; subst; clear H0.
    inversion H1; subst.
    { inversion H0. }
    inversion H0; subst.
  Qed.    

  Lemma step_plus_all_costs_cat :
    forall c s c' s',
      step_plus a0 c s c' s' ->
      exists l, all_costs s' = l ++ all_costs s.
  Proof.
    move => c s c' s'; elim; first by apply: step_all_costs_cat.
    move => cx sx cx' sx' cx'' sx'' H H2 []l ->.
    case: (step_all_costs_cat H) => l' ->.
    by exists (l ++ l'); rewrite catA.
  Qed.    
    
  Lemma step_plus_mult_weights_body_size_all_costs :
    forall nx s c' s',
      step_plus a0 (CIter nx (mult_weights_body A)) s c' s' ->
      final_com c' -> 
      size (all_costs s') = (N.to_nat nx + size (all_costs s))%N.
  Proof.
    move => nx s c' s' H H2.
    case: (step_plus_stepN H H2) => n H3; clear H H2.
    move: s s' nx H3.
    set P := fun n =>
               forall (s s' : state A) nx,
                 stepN a0 n (CIter nx (mult_weights_body A)) s s' ->
                 size (all_costs s') = (N.to_nat nx + size (all_costs s))%N.
    change (P n).                                                                         
    apply (well_founded_ind lt_wf); move {n}; case.
    { by rewrite /P => IH s s'; inversion 1; subst; rewrite add0n. }
    rewrite /P => n IH s s'; inversion 1; subst; first by rewrite add0n.
    inversion H6; subst.
    inversion H6; subst.
    have H7: (n0 < n0.+2)%coq_nat by omega.
    rewrite (IH _ H7 s1'0 _ (N.pred nx)) => //.
    rewrite N2Nat.inj_pred.
    have H11: size (all_costs s1'0) = (size (all_costs s)).+1.
    { clear - H5.
      inversion H5; subst. clear H5.
      inversion H6; subst. clear H6.
      inversion H3; subst. clear H3.
      inversion H2; subst. simpl in *. clear H2.
      inversion H7; subst. simpl in *. clear H7.
      by []. }
    rewrite H11.
    have H12: (0 < N.to_nat nx)%N.
    { by rewrite nat_of_bin_to_nat in H3. }
    clear - H12.
    move: H12; move: (N.to_nat nx) => n; clear nx.
    move: (size (all_costs s)) => m.
    rewrite -plusE => H.
    rewrite Nat.add_pred_l.
    by rewrite -plus_n_Sm.
    by move => H2; rewrite H2 in H.
  Qed.  
  
  Lemma step_plus_mult_weights_init_breakdown :
    forall nx s c' s',
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' -> 
      exists s0 : state A,
        [/\ step_plus a0 (mult_weights_init A) s CSkip s0
          & step_plus a0 (CSeq CSkip (CIter nx (mult_weights_body A))) s0 c' s'].
  Proof.
    move => nx s c' s' H H2.
    case: (step_plus_seq_inv1 H H2) => // s0 []H3 H4.
    by exists s0; split.
  Qed.
  
  Lemma step_plus_mult_weights_init_size :
    forall s c' s',
      step_plus a0 (mult_weights_init A) s c' s' ->
      size (all_costs s') = size (all_costs s).
  Proof.
    move => s c' s'; inversion 1; subst; clear H.
    { inversion H0; subst; clear H0.
      inversion H5; subst; clear H5 => //. }
    inversion H0; subst; clear H0.
    inversion H6; subst; clear H6.
    inversion H1; subst; clear H1.
    { inversion H; subst; clear H => //.
      inversion H5; subst; clear H5 => //. }
    inversion H; subst; clear H.
    { inversion H0; subst; clear H0.
      inversion H; subst; clear H; simpl => //.
      inversion H; subst; clear H; simpl in * => //.
      inversion H1; subst.
      { inversion H. }
      inversion H. }
    inversion H6; subst; clear H6.
  Qed.    

  Lemma step_plus_mult_weights_size_all_costs :
    forall nx s c' s',
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' -> 
      size (all_costs s') = (N.to_nat nx + size (all_costs s))%N.
  Proof.
    move => nx s c' s' H H2.
    case: (step_plus_mult_weights_init_breakdown H H2) => s0 []H3 H4.
    inversion H4; subst; clear H4.
    { inversion H0; subst; clear H0.
      inversion H2.
      inversion H2. }
    inversion H0; subst; clear H0; try solve[inversion H9].
    move: (step_plus_mult_weights_body_size_all_costs H1 H2).
    have H5: (size (all_costs s'') = size (all_costs s))%N.
    { apply: (step_plus_mult_weights_init_size H3). }
    by rewrite H5 => -> /=; rewrite addnS.
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
        (c : {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1})
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
               (d :: SOutputs s)
               (SChan s')
               (SOracleSt s')))).
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
    forall cs (s : state A) ch t,
      List.hd_error (SOutputs (mult_weights1 cs s ch t)) = 
        Some (pdist a0 (SEpsilonOk s) (@CMAX_all (rev cs))).
  Proof.
    move => cs s ch t; rewrite /mult_weights1 mult_weights1_loop_leftright.
    rewrite (@mult_weights1_loop_right_refines_p_aux_dist _ _ nil (init_weights A)).
    { apply: init_weights_gt0. }
    { move => H1; f_equal; rewrite /pdist /p_aux_dist /p cats0; f_equal => /=.
      by apply: proof_irrelevance. }
    { by move => H1 /=; f_equal; f_equal; apply: proof_irrelevance. }
    by [].
  Qed.

  (** Connect the refinements: *)
  Lemma step_plus_mult_weights_refines_pdist :
    forall nx s c' s' l,
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' ->
      catrev l (all_costs s) = all_costs s' ->       
      List.hd_error (SOutputs s') =
      Some (pdist a0 (SEpsilonOk s) (@CMAX_all (rev l))).
  Proof.
    move => nx s c' s' l H H2 H3.
    have pf: forall a : A, 0 < [ffun=> Q_to_rat 1] a.
    { by move => a; rewrite ffunE. }
    case: (step_plus_mult_weights_refines_mult_weights1 pf H H2 H3)=> ch []t' Hx.
    by case: Hx => _ _ _ _ <-; rewrite mult_weights1_refines_pdist.
  Qed.      
End mult_weights_refinement.
  
Lemma zip_nil T U (l : list T) : zip ([::] : list U) l = [::].
Proof. by elim l. Qed.

Lemma removelast_cat T (l1 l2 : list T) :
  (0 < size l2)%N -> 
  List.removelast (l1 ++ l2) = l1 ++ List.removelast l2.
Proof.
  elim: l1 => // a l1' IH H /=; rewrite IH => //.
  case H2: (l1' ++ l2) => //.
  move {IH}; elim: l1' H2 => //.
  by rewrite cat0s => H2; rewrite H2 in H.
Qed.    

Lemma size_removelast T (l : list T) :
  size (List.removelast l) = (size l).-1.
Proof.
  elim: l => // a l IH.
  by case: l IH => // b l /= ->.
Qed.  

Require Import Reals Rpower Ranalysis Fourier.

Section semantics_lemmas.
  Local Open Scope ring_scope.
  Variable A : finType.
  Variable a0 : A. (*A must be inhabited.*)
  Context T oracle_chanty `{Hco : ClientOracle T oracle_chanty}.

  Notation "'state' A" := (@state A T oracle_chanty) (at level 50).
  
  (** The total expected cost of state [s].
    Assuming costs are (in fold-right form):
                 c_1 :: c_2 :: ... :: c_T :: c_(T+1)
    and actions are:
       d_init :: d_1 :: d_2 :: ... :: d_T :: d_(T+1)
    the expected cost at time (T+1) is the expected cost of c_(T+1) given 
    action distribution d_T. The expected cost at time 1 is the 
    cost of c_1 given d_init. *)

  Fixpoint state_expCost1_aux
           (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1})
           (ds : seq (dist.dist A rat_realFieldType)) :=
    match l, ds with
    | [:: c & l'], [:: d, d' & ds'] =>
      (rat_to_R (expectedValue d' (fun a => projT1 c a)) +
       state_expCost1_aux l' [:: d' & ds'])%R
    | _, _ => 0%R
    end.

  Definition state_expCost1 l (s : state A) := state_expCost1_aux l (SOutputs s).
    
  Fixpoint state_expCost2
           eps
           (EpsOk : 0 < eps <= 1 / 2%:R)
           (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}) :=
    match l with 
    | [:: c & l'] =>
      (rat_to_R
         (expectedValue
            (pdist a0 EpsOk (@CMAX_all _ l'))
            (fun a => projT1 c a)) +
       state_expCost2 EpsOk l')%R
    | _ => 0%R
    end.

  Lemma state_expCost1_aux2_mult_weights1_loopright :
    forall ds1 ds2 cs1 cs2 (s s' : state A) w pf d0,
      List.hd_error (SOutputs s) =
      Some
        (p_aux_dist (A:=A) a0 (eps:=SEpsilon s) (SEpsilonOk s) (w:=w) pf
                    (cs:=[seq projT1 p | p <- cs2]) (CMAX_all (A:=A) (cs:=cs2))) ->
      SWeights s = weights_of (A:=A) (SEpsilon s) [seq projT1 p | p <- cs2] w ->
      w = init_weights A -> 
      state_expCost1_aux cs2 (last d0 ds1 :: ds2) = state_expCost2 (SEpsilonOk s) cs2 ->
      upto_oracle_eq (mult_weights1_loop_right a0 cs1 s) s' ->
      SOutputs s' = ds1 ++ ds2 ->
      (size cs1).+1 = size ds1 -> 
      state_expCost1_aux (cs1++cs2) (ds1++ds2) =
      state_expCost2 (SEpsilonOk s) (cs1++cs2).
  Proof.
    elim => //.
    move => d ds1' IH ds2 cs1 cs2 s s' w pf d0 H H2 Hinit H3.
    case => Hc Hd He Hf Hg; rewrite -Hg /=.
    case: cs1 Hc Hd He Hf Hg => //; first by case: ds1' IH H3.
    move => cx cs1' Ha Hb Hc Hd He H4 /=; case => H6.
    have [d' [ds1'' H7]]: exists d' ds1'', ds1' = [:: d' & ds1''].
    { case: ds1' IH H3 H4 H6 => // dx ds1''.
      by exists dx, ds1''. }
    rewrite H7 /=.
    move: (mult_weights1_loop_right_refines_p_aux_dist cs1' H H2) => H8.
    move: (mult_weights1_one_hd cx H8) => H9; subst ds1'; f_equal.
    { f_equal.
      f_equal.
      subst w.
      simpl in H4. inversion H4.
      rewrite H5 /= in H8; inversion H8.
      rewrite /p_aux_dist /pdist /p.
      f_equal.
      apply: proof_irrelevance. }
    apply: (IH _ _ _ _ _ _ _ d0) => //.
    inversion H4.
    by rewrite H5. 
  Qed.    

  Lemma mult_weights1_loop_right_outputs_size :
    forall cs (s s' : state A),
      upto_oracle_eq (mult_weights1_loop_right a0 cs s) s' ->
      (size (SOutputs s') = size cs + size (SOutputs s))%N.
  Proof.
    move => cs s s'; case => _ _ _ _ <-.
    by elim: cs => // a l /= ->.
  Qed.
    
  Lemma state_expCost12_mult_weights1 :
    forall cs s s' ch t,
      SOutputs s = [::] -> 
      upto_oracle_eq (mult_weights1 a0 (rev cs) s ch t) s' ->
      state_expCost1 cs s' = state_expCost2 (SEpsilonOk s) cs.
  Proof.
    rewrite /mult_weights1 => cs s s' ch t.
    rewrite mult_weights1_loop_leftright revK.
    set s0 := mult_weights1_init a0 s ch t.
    set w :=
      p_aux_dist (A:=A) a0 (eps:=SEpsilon s) (SEpsilonOk s)
                 (w:=init_weights A)
                 (init_weights_gt0 (A:=A))
                 (cs:=[seq projT1 p | p <- [::]]) (CMAX_all (A:=A) (cs:=[::])).
    have H2:
      List.hd_error (SOutputs s0) = Some w.
    { rewrite /w /=.
      f_equal.
      f_equal.
      apply: proof_irrelevance. }
    move: (state_expCost1_aux2_mult_weights1_loopright
             (ds1:=SOutputs s') (ds2:=[::])
             (cs1:=cs) (cs2:=[::])
             (s':=s') (d0:=w) H2).
    rewrite !cats0 /state_expCost1 => H H3 H4; rewrite H //.
    have H5: size (SOutputs s0) = 1%N by rewrite /= H3.
    by rewrite (mult_weights1_loop_right_outputs_size H4) H5 addn1.
  Qed.    

  Lemma state_expCost12 :
    forall nx (c' : com A) (s s' : state A) l,
      SOutputs s = [::] -> 
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' -> 
      catrev (rev l) (all_costs s) = all_costs s' ->             
      state_expCost1 l s' = state_expCost2 (SEpsilonOk s) l.
  Proof.
    move => nx c' s s' l H0 H H2 H3.
    have pf: forall a : A, 0 < [ffun=> Q_to_rat 1] a.
    { by move => a; rewrite ffunE. }
    case: (step_plus_mult_weights_refines_mult_weights1 pf H H2 H3)=> ch []t' Hx.
    apply: state_expCost12_mult_weights1 => //.
    apply: Hx.
  Qed.

  Lemma state_expCost2_expCostsR
        eps
        (EpsOk : 0 < eps <= 1 / 2%:R)
        (l : seq {c : {ffun A -> rat} & forall a : A, 0 <= c a <= 1}) :
    state_expCost2 EpsOk l =
    expCostsR (A:=A) a0 (cs:=[seq projT1 c | c <- l])
              (all_costs_CMAX' (A:=A) (l:=l))
              EpsOk.
  Proof.
    elim: l => // x l' IH.
    simpl.
    rewrite /expCostsR /=.
    f_equal.
    rewrite IH /expCostsR.
    apply: big_sum_ext => //.
    rewrite /subSeqs.
    f_equal.
    apply: proof_irrelevance.
  Qed.

  Definition init_costs : {ffun A -> rat} :=
    finfun (fun _ => 1).

  Lemma init_costs_ok : forall a, 0 <= init_costs a <= 1.
  Proof. by rewrite /init_costs => a; rewrite ffunE. Qed.

  Definition init_weights := init_costs.

  Lemma init_weights_ok : forall a, 0 < init_weights a.
  Proof. by move => a; rewrite ffunE. Qed.
  
  Variable eps : rat.
  Variable epsOk : 0 < eps <= 1/2%:R.
  Notation epsR := (rat_to_R eps).
  
  Definition init_state (ch : oracle_chanty) (t : T) :=
    @mkState
      _ _ _ 
      init_costs (** The initial cost function is never used -- 
                     we only include it because the type [state] forces 
                     an [SCost] projection. *)
      init_costs_ok
      [::]
      init_weights
      init_weights_ok
      eps
      epsOk
      [::]
      ch
      t.

  Lemma size_all_costs_init_state ch t : size (all_costs (init_state ch t)) = 1%N.
  Proof. by []. Qed.
  
  (** Because the last cost vector is bogus, we remove it using 
      [List.removelast]. *)
  Definition all_costs0 (s : state A) := List.removelast (all_costs s).
  Definition all_costs' (s : state A) := map (fun c => projT1 c) (all_costs0 s).

  (** The best fixed action (in hindsight) for state [s] *)      
  Definition astar (s : state A) := best_action a0 (all_costs' s).
  Definition OPT (s : state A) := \sum_(c <- all_costs' s) c (astar s).
  Definition OPTR (s : state A) := rat_to_R (OPT s).

  Notation size_A := (rat_to_R #|A|%:R).

  Lemma mult_weights_refines_MWU :
    forall nx (c' : com A) (s s' : state A) l,
      SOutputs s = [::] -> 
      step_plus a0 (mult_weights A nx) s c' s' ->
      final_com c' ->
      catrev (rev l) (all_costs s) = all_costs s' ->             
      state_expCost1 l s' = expCostsR a0 (@all_costs_CMAX' _ l) (SEpsilonOk s).
  Proof.
    move => nx c' s s' l H0 H H2 H3; move: (state_expCost12 H0 H H2 H3) => ->.
    by rewrite state_expCost2_expCostsR.
  Qed.

  (** The number of cost vectors received from the environment *)
  Definition num_costs (s : state A) := INR (size (all_costs' s)).

  Lemma mult_weights_T :
    forall nx (c' : com A) (s' : state A) ch t,
      (0 < size (all_costs s'))%N ->       
      step_plus a0 (mult_weights A nx) (init_state ch t) c' s' ->
      final_com c' -> 
      num_costs s' = INR (N.to_nat nx).
  Proof.    
    move => nx c' s' ch t Hsz H H2.
    move: (step_plus_mult_weights_size_all_costs H H2).
    rewrite /num_costs /all_costs' /all_costs0 size_map size_all_costs_init_state.
    rewrite size_removelast => H3; rewrite H3 in Hsz|-*; move: Hsz.
    by case: (N.to_nat nx) => // n _; f_equal => /=; rewrite -addnE addn1.
  Qed.    

  Definition Tx nx := INR (N.to_nat nx).
  
  Lemma mult_weights_epsilon_no_regret :
    forall nx (c' : com A) (s' : state A) (ch : oracle_chanty) (t : T),
      step_plus a0 (mult_weights A nx) (init_state ch t) c' s' ->
      final_com c' ->
      (0 < size (all_costs' s'))%N -> 
      let: eCost := state_expCost1 (all_costs0 s') s'
      in ((eCost - OPTR s') / Tx nx <= epsR + ln size_A / (epsR * Tx nx))%R.
  Proof.
    move => nx c' s' ch t H H2 Hsize.
    have H3: SOutputs (init_state ch t) = [::] by [].
    have H4: catrev (rev (all_costs0 s')) (all_costs (init_state ch t)) = all_costs s'.
    { case: (step_plus_all_costs_cat H) => l; rewrite /all_costs0 => ->.
      rewrite removelast_cat => //.
      by rewrite catrevE revK -catA. }
    rewrite (mult_weights_refines_MWU H3 H H2 H4) /OPTR /OPT /astar /Tx.
    have Hsize': (0 < size (all_costs s'))%N.
    { clear - Hsize; move: Hsize; rewrite /all_costs' size_map /all_costs0.
      rewrite size_removelast => //. }
    rewrite -(mult_weights_T Hsize' H H2).
    by apply: perstep_weights_noregret.
  Qed.
End semantics_lemmas.

Print Assumptions mult_weights_epsilon_no_regret.