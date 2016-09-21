Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.
Require Import ProofIrrelevance.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import weights weightslang compile dist numerics.

(** Here's a description of the compilation algorithm: 

  Source Language
  Binary Arithmetic Operations
    b ::= + | - | *
  Expressions
    e ::= q            (* rationals *)
        | -e           (* arithmetic negation *)
        | weight a     (* weight of action [a] *)
        | cost a       (* cost of action [a] *)
        | eps          (* the epsilon parameter *)
        | e b e        (* binary operations *)
  Commands
    c ::= skip
        | update f     (* update weights by (f : A -> e) *) 
        | recv         (* receive a cost vector from the environment *)
        | send         (* send an action ~ w / (\sum_(a : A) w a) *)
        | c1; c2       
        | iter n c     (* iterate c n-times *)

  Target Language (over game type A):
    The same as the source language, but with new semantics operating
    over compilable states. 
      s := { (* Compilable: *)
             cur_costs : M.t A Q     (* the current cost vector, mapping actions to costs *)   
           ; prev_costs : seq (M.t A Q)
           ; weights : M.t A Q       (* the weights table, mapping actions to weights *)
           ; eps : Q                 (* the parameter \epsilon *)

             (* Logical: *)
           ; outputs : seq (dist A rat_realFieldType) }.
    
    We make a few assumptions about the game type A, in order to use 
    actions as keys in the maps [cur_costs] and [weights]: 
      - It has an order that satisfies: OrderedType.OrderedType.   

    The semantics of [CSend] changes: Previously, [CSend] modeled drawing
    an action from the distribution generated by the weights table by 
    storing the distribution in the trace [SOutputs]. At this language level,
    we execute the draw by calling an axiomatized function [drawFrom], 
    implemented in OCaml by discrete inverse transform.
 *)

Module Type OrderedFinType.
   Parameter t : finType.
   Parameter eq : t -> t -> Prop.
   Parameter lt : t -> t -> Prop.
   Parameter eq_refl : forall x : t, eq x x.
   Parameter eq_sym : forall x y : t, eq x y -> eq y x.
   Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
   Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
   Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
   Parameter compare : forall x y : t, Compare lt eq x y.
   Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
End OrderedFinType.                               

Module OrderedType_of_OrderedFinType (A : OrderedFinType)
  <: OrderedType.OrderedType.
      Definition t : Type := A.t.
      Definition eq := A.eq.
      Definition lt := A.lt.
      Definition eq_refl := A.eq_refl.
      Definition eq_sym := A.eq_sym.
      Definition eq_trans := A.eq_trans.
      Definition lt_trans := A.lt_trans.
      Definition lt_not_eq := A.lt_not_eq.
      Definition compare := A.compare.
      Definition eq_dec := A.eq_dec.
End OrderedType_of_OrderedFinType.                                

Module CompilableWeights (A : OrderedFinType).
  Module A':= OrderedType_of_OrderedFinType A.  
  Module M := Make A'.
  Module MFacts := Facts M.
  Module MProps := Properties M.

  Definition cGamma (weights : M.t Q) :=
    M.fold (fun a q acc => q + acc) weights 0.

  (** Draw from a distribution, communicating the resulting action 
      to the network. *)
  Axiom drawFrom :
    forall weights : M.t Q, dist A.t rat_realFieldType.
  Axiom drawFrom_ok :
    forall weights : M.t Q,
      pmf (drawFrom weights) =
      finfun (fun a =>
                match M.find a weights with
                | None => 0%R (* bogus *)
                | Some q => (Q_to_rat q / Q_to_rat (cGamma weights))%R
                end).
  (* Receive a cost vector (a map) from the network. *)
  Axiom recv : unit -> M.t Q.
  Axiom recv_ok :
    forall a,
    exists q,
      [/\ M.find a (recv tt) = Some q
        & 0 <= q <= 1].
  
  Record cstate : Type :=
    mkCState
      { SCosts : M.t Q (* the current cost vector *)
      ; SPrevCosts : list (M.t Q)
      ; SWeights : M.t Q
      ; SEpsilon : Q (* epsilon -- a parameter *)
      (* the history of the generated distributions over actions *)                     
      ; SOutputs : list (dist A.t rat_realFieldType) }.

  Definition match_maps
             (s : {ffun A.t -> rat})
             (m : M.t Q) : Prop :=
    forall a,
    exists q, M.find a m = Some q /\ Qred q = rat_to_Q (s a).
  
  Definition match_costs
             (s : {c : {ffun A.t -> rat} & forall a : A.t, (0 <= c a <= 1)%R})
             (m : M.t Q) : Prop :=
    match_maps (projT1 s) m.
  
  Inductive match_costs_seq :
    seq {c : {ffun A.t -> rat} & forall a : A.t, (0 <= c a <= 1)%R} ->
    list (M.t Q) ->
    Prop :=
  | match_costs_nil :
      match_costs_seq nil nil
  | match_costs_cons :
      forall s ss m mm,
        match_costs s m ->
        match_costs_seq ss mm ->
        match_costs_seq [:: s & ss] [:: m & mm].
  
  Inductive match_states : state A.t -> cstate -> Prop :=
  | mkMatchStates :
      forall s m s_ok ss mm w w_ok wc eps eps_ok epsc outs,
        match_maps s m ->
        match_costs_seq ss mm ->
        match_maps w wc ->
        rat_to_Q eps = epsc -> 
        match_states
          (@mkState _ s s_ok ss w w_ok eps eps_ok outs)
          (@mkCState m mm wc epsc outs).

  Definition eval_binopc (b : binop) (v1 v2 : Q) :=
    match b with
    | BPlus => v1 + v2
    | BMinus => v1 - v2                      
    | BMult => v1 * v2
    end.
  
  Fixpoint evalc (e : expr A.t) (s : cstate) : option Q :=
    match e with
    | EVal v =>
      match v with
      | QVal q => Some q
      end
    | EOpp e' =>
      match evalc e' s with
      | Some v' => Some (- v')
      | None => None
      end
    | EWeight a => M.find a (SWeights s)
    | ECost a => M.find a (SCosts s)
    | EEps => Some (SEpsilon s)
    | EBinop b e1 e2 =>
      let: v1 := evalc e1 s in
      let: v2 := evalc e2 s in
      match v1, v2 with
      | Some v1', Some v2' => Some (eval_binopc b v1' v2')
      | _, _ => None
      end
    end.

  Lemma match_maps_gamma_cGamma s m :
    match_maps s m ->
    gamma s = Q_to_rat (cGamma m).
  Proof.
    rewrite /gamma /cGamma.
    set P :=
      fun m r =>
        forall s,
        match_maps s m -> 
        (\sum_a (s a) = Q_to_rat r)%R.
    move: s; change (P m  (M.fold (fun (_ : M.key) (q : Q) => [eta Qplus q]) m 0)).
    apply: MProps.fold_rec_weak.
    { move => mx m' a H; rewrite /P => H2 s H3.
      have H4: match_maps s mx.
      { move => x; case: (H3 x) => y []; rewrite -H => H4 H5.
        exists y; rewrite H4; split => //. }
      apply: (H2 _ H4). }
    { rewrite /P /match_maps => s H2.
      admit. (*no a exists*) }
    move => k e a mx H; rewrite /P => H2 s H3.
    (*I need an inductive version of [match_maps] -- it's currently 
      too global.*)
  Admitted.

  (*NOTE: This code is much complicated by the fact that [evalc] can
    fail -- otherwise, we could just use [M.mapi].*)
  Definition update_weights
             (f : A.t -> expr A.t) (s : cstate)
    : option (M.t Q) :=
    M.fold
      (fun a _ acc =>
         match acc with
         | None => None
         | Some acc' =>
           match evalc (f a) s with
           | None => None
           | Some q =>
             if Qle_bool q 0 then None
             else Some (M.add a q acc')
           end
         end)
      (SWeights s)
      (Some (M.empty Q)).
  
  Lemma match_maps_update_weights f r s m :
    match_maps (weightslang.SWeights r) (SWeights s) ->
    update_weights f s = Some m ->
    match_maps [ffun a => eval (f a) r] m /\
    (forall a, 0 < eval (f a) r)%R.
  Proof.
  Admitted. (*TODO*)
    
  Fixpoint interp (c : com A.t) (s : cstate) : option cstate :=
    match c with
    | CSkip => Some s
    | CUpdate f =>
      let w := update_weights f s
      in match w with
         | None => None
         | Some w' => 
           Some (mkCState
                   (SCosts s)
                   (SPrevCosts s)
                   w'
                   (SEpsilon s)
                   (SOutputs s))
         end
    | CRecv =>
      let c := recv tt
      in Some (mkCState
                 c
                 (SCosts s :: SPrevCosts s)
                 (SWeights s)
                 (SEpsilon s)
                 (SOutputs s))
    | CSend =>
      let d := drawFrom (SWeights s)
      in Some (mkCState
                 (SCosts s)
                 (SPrevCosts s)
                 (SWeights s)
                 (SEpsilon s)
                 (d :: SOutputs s))
    | CSeq c1 c2 =>
      match interp c1 s with
      | None => None
      | Some s' => interp c2 s'
      end
    | CIter n c =>
      (*NOTE: We could further short-circuit this iteration -- in practice, 
        it shouldn't matter for performance since [interp] should never
        fail on MWU, starting in appropriate initial state.*)
      N.iter
        n
        (fun s =>
           match s with
           | None => None
           | Some s' => interp c s'
           end)
        (Some s)
    end.

  Variable a0 : A.t.
  
  Lemma interp_step_plus :
    forall (s : state A.t) (t t' : cstate) (c : com A.t),
      interp c t = Some t' ->
      match_states s t ->       
      exists c' s',
        final_com c' /\
        ((c=CSkip /\ s=s') \/ step_plus a0 c s c' s') /\
        match_states s' t'.
  Proof.
    intros s t t' c H; revert s t t' H; induction c; simpl.
    { intros s t t'; inversion 1; subst.
      intros H2.
      exists CSkip, s.
      split; [solve[constructor; auto]|].
      split; auto. }
    { intros s t t' H H2.
      move: (@match_maps_update_weights e s t) H.
      case: (update_weights e t) => // m; move/(_ m) => H3.
      inversion 1; subst; clear H.
      inversion H2; subst; simpl in *; clear H2.
      move: (H3 H1 erefl) => H4; clear H3.
      exists CSkip.
      eexists.
      split => //.
      split.
      { right.
        constructor.
        constructor. }
      simpl.
      case: H4 => H4 H5.
      constructor => //.
      Unshelve. by case: H4 => H4 H5 a; move: (H5 a); rewrite ffunE. }
    { intros s t t'; inversion 1; subst. clear H.
      intros H2.
      set c := recv tt.
      set f :=
        finfun
          (fun a =>
             match M.find a c with
             | None => 0%R (*bogus*)
             | Some q => Q_to_rat (Qred q)
             end).
      have pf: forall a, (0 <= f a <= 1)%R.
      { move => a. rewrite /f ffunE. clear f.
        case: (recv_ok a) => q [] -> [] H H3.
        apply/andP; split.
        { rewrite -Q_to_rat0; apply: Q_to_rat_le.
          have H4: Qeq (Qred q) q by apply: Qred_correct.
          by rewrite H4. }
        rewrite -Q_to_rat1; apply: Q_to_rat_le.
        by move: (Qred_correct q) ->. }
      exists CSkip.
      exists 
        (@mkState
           _ 
           f
           pf
           (existT
              _
              (weightslang.SCosts s)
              (weightslang.SCostsOk s) :: weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)             
           (weightslang.SEpsilonOk s)
           (weightslang.SOutputs s)).
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor. }
      inversion H2; subst.
      constructor; try solve[auto | constructor; auto].
      rewrite /match_maps => a.
      case: (recv_ok a) => q []; rewrite /f ffunE => -> _.
      exists q.
      split; auto.
      by rewrite rat_to_QK. }
    { intros s t; inversion 1; subst; clear H.
      intros H2.
      exists CSkip.
      exists 
        (@mkState
           _ 
           (weightslang.SCosts s)
           (weightslang.SCostsOk s)
           (weightslang.SPrevCosts s)
           (weightslang.SWeights s)
           (weightslang.SWeightsOk s)
           (weightslang.SEpsilon s)
           (weightslang.SEpsilonOk s)             
           (p_aux_dist
              a0
              (weightslang.SEpsilonOk s)
              (weightslang.SWeightsOk s)
              (@CMAX_nil A.t)
              :: weightslang.SOutputs s)).
      split; first by constructor.
      split.
      { right.
        constructor.
        constructor. }
      inversion H2; subst.
      simpl.
      have H3:
        p_aux_dist (A:=A.t) a0 (eps:=eps) eps_ok
                   (w:=w) w_ok (cs:=[::]) 
                   (CMAX_nil (A:=A.t)) =
        drawFrom wc.
      { rewrite /p_aux_dist.
        case H3: (drawFrom wc) => [pmf2 pf2].
        move: (drawFrom_ok wc). rewrite H3 /= => H4. subst pmf2. clear H3.
        generalize
          (p_aux_dist_axiom (A:=A.t) a0 (eps:=eps) eps_ok (cs:=[::])
                            (w:=w) w_ok (CMAX_nil (A:=A.t))) => pf1.
        revert pf1 pf2.
        have ->:
             [ffun a => match M.find (elt:=Q) a wc with
                        | Some q => (Q_to_rat q / Q_to_rat (cGamma wc))%R
                        | None => 0%R
                        end] = p_aux (A:=A.t) eps [::] w.
        { rewrite /p_aux; apply/ffunP => a; rewrite 2!ffunE.
          move: (match_maps_gamma_cGamma H1) => H1'.
          rewrite /match_maps in H1; case: (H1 a) => y []H3 H4. clear H1.
          rewrite H3 /= H1'; f_equal. clear - H4.
          rewrite rat_to_Q_red in H4.
          have H5: Qeq y (rat_to_Q (w a)).
          { by rewrite -(Qred_correct y) -(Qred_correct (rat_to_Q (w a))) H4. }
            by apply: rat_to_QK2. }
        move => pf1 pf2.
        f_equal.
        apply: proof_irrelevance. }
      rewrite H3.
      constructor; auto. }
    { move => s t t'.
      case H: (interp c1 t) => [t''|].
      { move => H2 H3.
        case: (IHc1 _ _ _ H H3) => cx []tx []H4 []H5 H6.
        case: (IHc2 _ _ _ H2 H6) => cy []ty []H7 []H8 H9.
        case: H5.
        { case => -> ->. 
          case: H8.
          { case => -> ->.
            exists cy, ty.
            split; auto.
            split; auto.
            right; auto.
            constructor.
            inversion H7; subst.
            apply: SSeq1. }
          move => H10.
          exists cy, ty.
          split; auto.
          split; auto.
          right; auto.
          apply: step_trans.
          constructor.
          apply: H10. }
        move => H10.
        case: H8.
        { case => -> H11. subst ty.
          exists CSkip, tx.
          split; first by constructor.
          split; auto.
          right.
          apply: step_plus_trans.
          apply: step_plus_seq.
          apply: H10.
          inversion H4; subst.
          constructor.
          constructor. }
        move => H11.
        exists cy, ty.
        split => //.
        split => //.
        right.
        apply: step_plus_trans.
        apply: step_plus_seq.
        apply: H10.
        inversion H4; subst.
        apply: step_trans.
        constructor.
        inversion H7; subst.
        apply: H11. }
      inversion 1. }
    move => s t0 t'.
    rewrite N2Nat.inj_iter.
    move H: (N.to_nat t) => n.
    move: s t0 t t' H; elim: n.
    { move => s t0 t t' H; inversion 1; subst. clear H0 => H2.
      exists CSkip, s; split => //.
      split => //.
      right.
      constructor.
      have H3: t = Coq.Numbers.BinNums.N0.
      { case: t H => //= p H.
        move: (PosN0 p).
          by rewrite H. }
      rewrite H3.
      constructor. }
    move => n IH s t0 t t' H H2 H3.
    have [x [H4 H5]]: exists x, [/\ t = N.succ x & N.to_nat x = n].
    { clear - H.
      exists (N.pred t).
      rewrite N.succ_pred.
      { split => //.
          by rewrite N2Nat.inj_pred H. }
      move => H2; rewrite H2 /= in H; discriminate. }
    subst t n. clear H.
    move: H2 => /=.
    case H4: (Nat.iter (N.to_nat x)
                       (fun s0 : option cstate =>
                          match s0 with
                          | Some s' => interp c s'
                          | None => None
                          end) (Some t0)) => [tx|].
    { move => H5.
      case: (IH _ _ _ _ erefl H4 H3) => c0 []s0 []H6 []H7 H8.
      case: (IHc _ _ _ H5 H8) => cx []sx []H9 []H10 H11.
      case: H7.
      { case.
        inversion 1. }
      move => H12.
      case: H10.
      { case => H13 H14. subst c s0.
        exists c0, sx.
        split => //.
        split => //.
        right.
        apply: step_trans.
        { apply SIterS.
          rewrite nat_of_bin_to_nat.
            by rewrite N2Nat.inj_succ. }
        apply: step_trans.
        constructor.
        rewrite N.pred_succ.
        apply: H12. }
      move => H13.
      exists cx, sx.
      split => //.
      split => //.
      right.
      apply: step_trans.
      constructor.
      { by rewrite nat_of_bin_to_nat N2Nat.inj_succ. }
      rewrite N.pred_succ.
      apply: step_plus_iter_flip => //.
      inversion H6; subst.
      apply: H12.
      apply: H13. }
    inversion 1.
  Qed.
End CompilableWeights.

(** Test extraction: *)

Extraction "interp" CompilableWeights.
  