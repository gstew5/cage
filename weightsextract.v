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
   Parameter eqP : forall x y, x = y <-> eq x y.
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
        rat_to_Q eps = Qred epsc -> 
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

  Fixpoint cGamma'_aux (l : list (M.key * Q)) :=
    match l with
    | nil => 0
    | a :: l' => a.2 + cGamma'_aux l' 
    end.

  Lemma cGamma_cGamma'_aux l :
    fold_right
      (fun y : M.key * Q => [eta Qplus y.2])      
      0
      l =
    cGamma'_aux l.
  Proof. elim: l => // a l IH /=; rewrite IH. Qed.

  Definition cGamma' m :=
    cGamma'_aux (List.rev (M.elements m)).
  
  Lemma cGamma_cGamma' m :
    cGamma m = cGamma' m.
  Proof.
    rewrite /cGamma /cGamma' M.fold_1 -fold_left_rev_right.
    by rewrite cGamma_cGamma'_aux.
  Qed.
  
  Definition gamma' (l : seq A.t) (s : {ffun A.t -> rat}) : rat :=
    \sum_(a <- l) (s a)%R.

  Lemma gamma'_cons x l s :
    (gamma' (x :: l) s = s x + gamma' l s)%R.
  Proof. by rewrite /gamma' big_cons. Qed.

  Lemma gamma_gamma' w : gamma' (index_enum A.t) w = gamma w.
  Proof. by []. Qed.
    
  Lemma match_maps_gamma_cGamma'_aux
        (s : {ffun A.t -> rat})
        (l : list (M.key * Q)) :
    (forall a q, In (a, q) l -> rat_to_Q (s a) = Qred q) -> 
    gamma' (List.map (fun x => x.1) l) s = Q_to_rat (cGamma'_aux l).
  Proof.
    elim: l s => //.
    { by move => s /= IH; rewrite /gamma' /= big_nil Q_to_rat0. }
    case => a q l IH s /= H.
    rewrite gamma'_cons Q_to_rat_plus IH.
    { have ->: s a = Q_to_rat q.
      { move: (H _ _ (or_introl erefl)) => H2.
        rewrite (rat_to_QK2 (r:=s a)) => //.
        by rewrite -(Qred_correct q) H2. }
      by []. }
    move => ax qx H2.
    by apply: (H _ _ (or_intror H2)).
  Qed.

  Lemma InA_notin a l : ~InA A.eq a l -> a \notin l.
  Proof.
    elim: l a => // a l IH ax H; rewrite /in_mem /=; apply/negP; case/orP.
    { by move/eqP => H2; subst ax; apply: H; left; rewrite -A.eqP. }
    move => H2; apply: H; right.
    case: (InA_dec A.eq_dec ax l) => // H3; move: (IH _ H3).
    by rewrite /in_mem /= H2.
  Qed.
    
  Lemma InA_not_InA_eq x y l : InA A.eq x l -> ~InA A.eq y l -> x<>y.
  Proof.
    elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H.
    { move => H2 H3; subst y.
        by apply: H2; left. }
    move => H2 H3; subst x.
    by apply: H2; right.
  Qed.    

  Lemma InA_map A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) x l (f : A -> B) :
    (forall x y, Aeq x y -> Beq (f x) (f y)) ->
    InA Aeq x l ->
    InA Beq (f x) (List.map f l).
  Proof.
    move => H; elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H0.
    { by left; apply: H. }
      by simpl; right; apply: (IH H2).
  Qed.    

  Lemma InA_map' A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) x l (f : A -> B) :
    (forall x y, Beq (f x) (f y) -> Aeq x y) ->
    InA Beq (f x) (List.map f l) ->     
    InA Aeq x l.
  Proof.
    move => H; elim: l; first by inversion 1.
    move => a l IH.
    inversion 1; subst; clear H0.
    { by left; apply: H. }
      by simpl; right; apply: (IH H2).
  Qed.    
  
  Lemma NoDupA_map A B (Aeq : A -> A -> Prop) (Beq : B -> B -> Prop) l (f : A -> B) :
    (forall x y, Beq (f x) (f y) -> Aeq x y) ->
    NoDupA Aeq l ->
    NoDupA Beq (List.map f l).
  Proof.
    move => H; induction 1; first by constructor.
    simpl; constructor => // H2; apply: H0.
    by apply: (InA_map' H).
  Qed.    
      
  Lemma match_maps_find1 x m q : 
    M.find (elt:=Q) x m = Some q -> 
    (count_mem x) (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))) = 1%N.
  Proof.
    move: (M.elements_3w m); move/NoDupA_rev => H H2.
    have H3: InA A.eq x (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))).
    { have H3: M.find (elt:=Q) x m <> None.
      { move => H3; rewrite H3 in H2; congruence. }
      clear H2; move: H3; rewrite -MProps.F.in_find_iff MProps.F.elements_in_iff.
      case => e; move: (M.elements _) => l; clear H => H.
      have ->: x = fst (x, e) by [].
      have H2: InA (M.eq_key_elt (elt:=Q)) (x, e) (List.rev l).
      { by rewrite InA_rev. }
      have H3: forall x y : M.key * Q, M.eq_key_elt x y -> A.eq x.1 y.1.
      { by case => x1 x2; case => y1 y2; case. }
      by apply (InA_map H3 H2). }
    have H4: NoDupA A.eq (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))).
    { move: (H2); rewrite -MProps.F.find_mapsto_iff MProps.F.elements_mapsto_iff => H4.
      clear - H; apply: (NoDupA_map _ H); case => x1 x2; case => y1 y2 //. }
    clear H.
    move: H3 H4; move: (List.map _ _) => l.
    clear H2 m q.
    elim: l => //.
    { inversion 1. }
    move => a l' IH; inversion 1; subst.
    { clear H3.
      inversion 1; subst.
      simpl.
      move: H0; rewrite -A.eqP => ->.
      have ->: (count_mem a) l' = 0%N.
      { have H5: a \notin l' by apply: InA_notin.
        apply: (count_memPn H5). }
      by rewrite addn0 eq_refl. }
    inversion 1; subst => /=.
    have ->: a == x = false.
    { move: (InA_not_InA_eq H0 H2) => H6.
      case H7: (a == x) => //.
      move: (eqP H7) => H8; subst x; contradiction. }
    rewrite IH => //.
  Qed.
  
  Lemma match_maps_enum_count_mem s m :
    match_maps s m ->
    forall x : A.t,
    (count_mem x) (index_enum A.t) =
    (count_mem x) (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))).
  Proof.
    move => H x; case: (H x) => q []H1 H2; move {H}; rewrite (@enumP A.t x).
    by rewrite (match_maps_find1 H1).
  Qed.
  
  Lemma match_maps_enum_perm_eq s m :
    match_maps s m -> 
    perm_eq (index_enum A.t)
            (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))).
  Proof.
    move => H; rewrite /perm_eq; apply/allP => x.
    by rewrite mem_cat; case/orP => /= H2;
       apply/eqP; apply: match_maps_enum_count_mem.
  Qed.
  
  Lemma match_maps_gamma'_elements s m : 
    match_maps s m -> 
    gamma' (index_enum A.t) s =
    gamma' (List.map [eta fst] (List.rev (M.elements (elt:=Q) m))) s.
  Proof.
    rewrite /gamma' /match_maps => H; apply: eq_big_perm.
    by apply: (match_maps_enum_perm_eq H).
  Qed.
    
  Lemma match_maps_gamma_cGamma s m :
    match_maps s m ->
    gamma s = Q_to_rat (cGamma m).
  Proof.
    rewrite cGamma_cGamma' -(gamma_gamma' s).
    move => H; rewrite -(match_maps_gamma_cGamma'_aux (s:=s)).
    { apply: match_maps_gamma'_elements => //. }
    move => a q H2.
    case: (H a) => q' []H3 H4.
    have H5: In (a,q) (M.elements (elt:=Q) m).
    { by rewrite in_rev. }
    clear H2; have ->: q = q'.
    { move: H3; rewrite -MProps.F.find_mapsto_iff => H3.
      have H6: InA (M.eq_key_elt (elt:=Q)) (a, q) (M.elements (elt:=Q) m).
      { apply: In_InA => //. }
      move: H6; rewrite -MProps.F.elements_mapsto_iff => H6.
      apply: MProps.F.MapsTo_fun; first by apply: H6.
      apply: H3. }
    by rewrite H4. 
  Qed.

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
             match 0 ?= q with
             | Lt => Some (M.add a q acc')
             | _ => None
             end
           end
         end)
      (SWeights s)
      (Some (M.empty Q)).

  Fixpoint update_weights'_aux
             (f : A.t -> expr A.t) (s : cstate) w l
    : option (M.t Q) :=
    match l with
    | nil => Some w
    | a :: l' =>
      match evalc (f a) s with
      | None => None
      | Some q =>
        match 0 ?= q with
        | Lt => 
          match (update_weights'_aux f s w l') with
             | None => None
             | Some m => Some (M.add a q m)
          end
        | _ => None
        end
      end
    end.

  Lemma update_weights'_aux_app f s w l1 l2 :
    update_weights'_aux f s w (l1 ++ l2) =
    match update_weights'_aux f s w l2 with
    | None => None
    | Some w' => update_weights'_aux f s w' l1
    end.
  Proof. 
    elim: l1 l2 w => //=.
    { move => l2 w; case: (update_weights'_aux _ _ _ _) => //. }
    move => a l IH l2 w; move: IH.
    case H2: (update_weights'_aux _ _ _ l2) => [w'|].
    { move => IH.
      case: (evalc (f a) s) => // x.
      case: (0 ?= x) => //.
      by rewrite IH H2. }
    move => ->; rewrite H2.
    case: (evalc (f a) s) => //.
    move => a0; case: (0 ?= a0) => //.
  Qed.   
  
  Definition update_weights'
             (f : A.t -> expr A.t) (s : cstate) 
    : option (M.t Q) :=
    update_weights'_aux f s (M.empty Q)
      (List.map (fun x => x.1) (List.rev (M.elements (SWeights s)))).

  Lemma update_weights'_aux_inv f s m l m' :
    update_weights'_aux f s m l = Some m' ->
    forall a,
      In a l ->
      exists q, 
        [/\ M.find a m' = Some q
          , evalc (f a) s = Some q
          & Qlt 0 q].
  Proof.
    elim: l m m' => // a l IH m m' /=.
    case H: (evalc _ _) => // [q].
    case H2: (0 ?= q) => //.
    case H3: (update_weights'_aux _ _ _ _) => // [m''] H4 a' H5.
    case: H5.
    { move => H6; subst a'; inversion H4; subst.
      rewrite MProps.F.add_eq_o; last by rewrite -A.eqP.
      { exists q.
        split => //. } }
    move => H5.
    case: (IH _ _ H3 _ H5) => q' []H6 H7 H8.
    case: (A.eq_dec a a').
    { rewrite -A.eqP => H9. subst a'.
      exists q; split => //.
      inversion H4; subst.
      rewrite MProps.F.add_eq_o; last by rewrite -A.eqP.      
        by []. }
    move => H9.
    exists q'.
    split => //.
    inversion H4; subst.
    rewrite MProps.F.add_neq_o => //.
  Qed.    

  Lemma update_weights'_inv1 f s m : 
    (forall a, exists q, M.find a (SWeights s) = Some q) -> 
    update_weights' f s = Some m ->
    forall a,
    exists q,
      [/\ M.find a m = Some q
        , evalc (f a) s = Some q
        & Qlt 0 q].
  Proof.
    rewrite /update_weights' => H H2 a.
    have H3: In a (List.map [eta fst] (List.rev (M.elements (elt:=Q) (SWeights s)))).
    { clear - H.
      case: (H a) => q H2.
      have H3: M.find (elt:=Q) a (SWeights s) <> None.
      { move => H4; rewrite H4 in H2; congruence. }
      move: H3; rewrite -MProps.F.in_find_iff MProps.F.elements_in_iff.
      case => q'; move: (M.elements _) => l.
      elim: l => //=.
      { inversion 1. }
      case => []a' b l IH /=.
      inversion 1; subst.
      { destruct H1; simpl in *; subst.
        move: H0; rewrite -A.eqP => H3; subst a'.
        have ->: a = (a, b).1 by [].
        apply: in_map.
        apply: in_or_app.
        right.
        left => //. }
      move: (IH H1).
      rewrite in_map_iff; case; case => a'' b' /=; case => -> H3.
      have ->: a = (a, b').1 by [].
      apply: in_map.
        by apply: in_or_app; left. }
    apply: (update_weights'_aux_inv H2 H3).
  Qed.    

  Lemma update_weights_weights'_aux f s l w :
    fold_right
     (fun (y : M.key * Q) (x : option (M.t Q)) =>
      match x with
      | Some acc' =>
          match evalc (f y.1) s with
          | Some q =>
            match 0 ?= q with
            | Lt => Some (M.add y.1 q acc')
            | _ => None
            end
          | None => None
          end
      | None => None
      end) (Some w) l =
    update_weights'_aux f s w (List.map [eta fst] l).
  Proof.
    move: w; elim: l => // [][]a b l IH.
    move => w /=; rewrite IH.
    case: (update_weights'_aux _ _ _ _) => //.
    case: (evalc _ _) => // q''.
    case: (0 ?= q'') => //.
  Qed.
    
  Lemma update_weights_weights' f s :
    update_weights f s = update_weights' f s.
  Proof.
    rewrite /update_weights /update_weights' M.fold_1 -fold_left_rev_right.
    apply: update_weights_weights'_aux.
  Qed.
    
  Lemma update_weights_inv1 f s m :
    (forall a, exists q, M.find a (SWeights s) = Some q) -> 
    update_weights f s = Some m ->
    forall a,
    exists q,
      [/\ M.find a m = Some q
        , evalc (f a) s = Some q
        & Qlt 0 q].
  Proof.
    rewrite update_weights_weights'.
    apply: update_weights'_inv1.
  Qed.

  Lemma match_eval f (r : state A.t) (s : cstate) q :
    match_maps (weightslang.SWeights r) (SWeights s) ->
    match_maps (weightslang.SCosts r) (SCosts s) ->
    rat_to_Q (weightslang.SEpsilon r) = Qred (SEpsilon s) ->
    forall a : A.t, 
      evalc (f a) s = Some q ->
      Qred q = rat_to_Q (eval (f a) r).
  Proof.
    move => H Hx Hy a; move: (f a) => e.
    elim: e q.
    { move => v q /=.
      case: v => // q'.
      inversion 1; subst.
        by rewrite rat_to_QK1. }
    { move => e IH q /=.
      case H2: (evalc e s) => // [q']; inversion 1; subst.
      rewrite Qred_opp.
      rewrite IH => //.
        by rewrite rat_to_Qopp. }
    { move => a' q /= H2.
      case: (H a') => q' []H3 H4.
      rewrite H3 in H2; inversion H2; subst. clear H2.
        by rewrite H4. }
    { move => a' q /= H2.
      case: (Hx a') => q' []H3 H4.
      rewrite H3 in H2; inversion H2; subst. clear H2.
        by rewrite H4. }
    { move => q /=; inversion 1; subst.
        by rewrite Hy. }
    move => b e1 IH1 e2 IH2 q /=.
    case H1: (evalc e1 s) => // [v1].
    case H2: (evalc e2 s) => // [v2].
    inversion 1; subst. clear H0.
    (*case analysis on the binary operations*)
    case: b; rewrite /eval_binopc /eval_binop.
    { rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_plus.
      rewrite -(IH1 _ H1).
      rewrite -(IH2 _ H2).
      by rewrite 2!Qred_correct. }
    { rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_plus.
      rewrite -(IH1 _ H1).
      rewrite rat_to_Qopp.
      rewrite -(IH2 _ H2).
      by rewrite 2!Qred_correct. }
    rewrite rat_to_Q_red; apply: Qred_complete; rewrite rat_to_Q_mul.
    rewrite -(IH1 _ H1).
    rewrite -(IH2 _ H2).
    by rewrite 2!Qred_correct. 
  Qed.
  
  Lemma update_weights_inv2 f r s m :
    match_states r s -> 
    update_weights f s = Some m ->
    forall a,
    exists q,
      [/\ M.find a m = Some q
        , evalc (f a) s = Some q
        , Qred q = rat_to_Q (eval (f a) r) 
        & Qlt 0 q].
  Proof.
    move => H H2 a.
    move: (@update_weights_inv1 f s m) => Hinv1.
    move: (@match_eval f r s) => Hmatch.
    case: s H H2 Hinv1 Hmatch; intros.
    inversion H; subst.
    have H3: forall a, exists q, M.find a SWeights0 = Some q.
    { move => a'; case: (H9 a') => q []H3 H4; exists q => //. }
    case: (Hinv1 H3 H2 a) => q []H1 H4 H5.
    exists q; split => //.
    apply: Hmatch => //.
  Qed.    
  
  Lemma match_maps_update_weights f r s m :
    match_states r s -> 
    update_weights f s = Some m ->
    match_maps [ffun a => eval (f a) r] m /\
    (forall a, 0 < eval (f a) r)%R.
  Proof.
    move => H H2; split => a; case: (update_weights_inv2 H H2 a) => q.
    { case => H3 H4 H5 H6.
      exists q; split => //.
        by rewrite H5 ffunE. }
    case => H3 H4 H5 H6.
    have H7: 0 < Qred q by rewrite Qred_correct.
    rewrite H5 in H7; clear - H7.
    have H6: 0 = inject_Z 0 by [].
    rewrite H6 -rat_to_Q0 in H7.
    by apply: rat_to_Q_lt'.
  Qed.    
    
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
      generalize H2 => H2'.
      inversion H2; subst; simpl in *; clear H2.
      move: (H3 H2' erefl) => H5; clear H3.
      exists CSkip.
      eexists.
      split => //.
      split.
      { right.
        constructor.
        constructor. }
      simpl.
      case: H5 => H5 H6.
      constructor => //.
      Unshelve. by case: H5 => H5 H6 a; move: (H6 a); rewrite ffunE. }
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
      inversion H2; subst. simpl in *.
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
      inversion H2; subst. simpl in *.
      move: H3 => Heps.
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
  