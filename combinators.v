Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import extrema dist numerics bigops.
Require Import games compile smooth christodoulou.

Local Open Scope ring_scope.

(** This module defines combinators over multiplayer games. *)

(** A generic wrapper for directing the construction of cost games
    over finite types [T]. [I] is a phantom type, used to direct
    instance resolution. *)
Inductive Wrapper (I : Type) (T : finType) : Type :=
  Wrap : T -> Wrapper I T.
Definition unwrap (I : Type) (T : finType) (w : Wrapper I T) : T :=
  match w with Wrap t => t end.

Section Wrapper.
  Variable I : Type.
  Variable T : finType.
Definition Wrapper_eq (t1 t2 : Wrapper I T) :=
  match t1, t2 with
  | Wrap t1', Wrap t2' => t1'==t2'
  end.                                 
Lemma Wrapper_eqP : Equality.axiom Wrapper_eq.
Proof.
  case=> s; case=> t /=; case H: (s == t).
  by move: (eqP H)=> ->; constructor.
  by constructor; case => e; subst s; rewrite eq_refl in H.
Qed.    
Definition Wrapper_eqMixin := EqMixin Wrapper_eqP.
Canonical Wrapper_eqType := Eval hnf in EqType (Wrapper I T) Wrapper_eqMixin.

Definition T_of_Wrapper (w : Wrapper I T) : T := unwrap w.
Definition Wrapper_of_T (t : T) : Wrapper I T := Wrap _ t.
Lemma T_of_WrapperK : cancel T_of_Wrapper Wrapper_of_T.
Proof. by case. Qed.
Definition Wrapper_choiceMixin := CanChoiceMixin T_of_WrapperK.
Canonical Wrapper_choiceType :=
  Eval hnf in ChoiceType (Wrapper I T) Wrapper_choiceMixin.
Definition Wrapper_countMixin := CanCountMixin T_of_WrapperK.
Canonical Wrapper_countType :=
  Eval hnf in CountType (Wrapper I T) Wrapper_countMixin.

Definition Wrapper_enum := map (fun x => Wrap I x) (Finite.enum T).
Lemma Wrapper_enumP : Finite.axiom Wrapper_enum.
Proof. by rewrite /Wrapper_enum; case => s; rewrite count_map; apply/enumP. Qed.

Definition unwrap_ffun (N : nat) (t : (Wrapper I T)^N) : T^N :=
  finfun (fun i => unwrap (t i)).
End Wrapper.

Definition Wrapper_finMixin (I : Type) (T : finType) :=
  Eval hnf in FinMixin (@Wrapper_enumP I T).
Canonical Wrapper_finType (I : Type) (T : finType) :=
  Eval hnf in FinType (Wrapper I T) (Wrapper_finMixin I T).

Section WrapperLemmas.
  Variables (I : Type) (T : finType) (N : nat).
  Context `(game T N).
  
  Lemma unwrap_ffun_simpl (t t' : (Wrapper I T)^N) :
    \sum_(i < N)
     (cost) i [ffun i0 => unwrap ([ffun j => if i == j then t' j else t j] i0)] =
    \sum_(i < N)
     (cost) i [ffun j => if i == j then unwrap (t' j) else unwrap (t j)].
  Proof.
    apply/congr_big=> // i _; f_equal; apply/ffunP => j; rewrite !ffunE.
    by case: (i == j).
  Qed.

  Lemma unwrap_eta (t t' : (Wrapper I T)^N) :
    \sum_(i < N) (cost) i [ffun j => if i == j then unwrap (t' j) else unwrap (t j)] =
    \sum_(i < N)
     (cost) i [ffun j => if i == j
                         then [ffun i0 => unwrap (t' i0)] j
                         else [ffun i0 => unwrap (t i0)] j].
  Proof. by apply/congr_big=> // i _; f_equal; apply/ffunP => j; rewrite !ffunE. Qed.
End WrapperLemmas.

(** Resource Games *)

Inductive resource : Type :=
| RYes : resource
| RNo : resource.

Definition resource_eq (r1 r2 : resource) :=
  if r1 is RYes then if r2 is RYes then true else false
  else if r2 is RYes then false else true.
Lemma resource_eqP : Equality.axiom resource_eq.
Proof. by case; case; try constructor. Qed.
Definition resource_eqMixin := EqMixin resource_eqP.
Canonical resource_eqType := Eval hnf in EqType resource resource_eqMixin.

Definition bool_of_resource (r : resource) : bool :=
  if r is RYes then true else false.
Definition resource_of_bool (b : bool) : resource :=
  if b then RYes else RNo.
Lemma bool_of_resourceK : cancel bool_of_resource resource_of_bool.
Proof. by case. Qed.
Definition resource_choiceMixin := CanChoiceMixin bool_of_resourceK.
Canonical resource_choiceType :=
  Eval hnf in ChoiceType resource resource_choiceMixin.
Definition resource_countMixin := CanCountMixin bool_of_resourceK.
Canonical resource_countType :=
  Eval hnf in CountType resource resource_countMixin.

Definition resource_enum := [:: RYes; RNo].
Lemma resource_enumP : Finite.axiom resource_enum.
Proof. by case. Qed.
Definition resource_finMixin := Eval hnf in FinMixin resource_enumP.
Canonical resource_finType := Eval hnf in FinType resource resource_finMixin.

Section resourceDefs.
  Context (N : nat) (rty : realFieldType).
  Local Open Scope ring_scope.

  Definition traffic (f : {ffun 'I_N -> resource}) := #|RNo.-support f|.

  Definition traffic' (f : {ffun 'I_N -> resource}) :=
    (\sum_(i < N | f i == RYes) 1)%N.

  Lemma pred_no_yes (f : {ffun 'I_N -> resource}) :
    (#|[pred x | f x != RNo]| = #|[pred x | f x == RYes]|)%N.
  Proof.
    apply: eq_card=> x; rewrite /in_mem /=.
    case H3: (f x)=> //.
  Qed.    
  
  Lemma trafficP f : traffic f = traffic' f.
  Proof.
    rewrite /traffic /traffic'.
    by rewrite /support_for sum1_card pred_no_yes.
  Qed.        

  Lemma traffic_pos f : (0 : rty) <= (traffic f)%:R.
  Proof.
    rewrite /traffic; case H: #|RNo.-support f|=> //.
    by apply: ler0n.
  Qed.
  
  Definition resourceCostFun (i : 'I_N) (f : {ffun 'I_N -> resource}) : rty :=
    if f i is RYes then (traffic f)%:R else 0.
End resourceDefs.

Instance resourceCostInstance (N : nat)
  : CostClass N rat_realFieldType [finType of resource] :=
  fun (i : 'I_N) (f : {ffun 'I_N -> resource}) =>
    resourceCostFun rat_realFieldType i f.

Program Instance resourceCostAxiomInstance (N : nat)
  : @CostAxiomClass N rat_realFieldType [finType of resource] _.
Next Obligation.
  rewrite /cost_fun /resourceCostInstance /resourceCostFun.
  case: (f i)=> //. apply: traffic_pos.
Qed.

Instance resourceGame (N : nat) : @game [finType of resource] N _ _ _.

Instance resourceLambdaInstance 
  : LambdaClass [finType of resource] rat_realFieldType| 0 := 5%:R/3%:R.

Program Instance resourceLambdaAxiomInstance
  : @LambdaAxiomClass [finType of resource] rat_realFieldType _.

Instance resourceMuInstance
  : MuClass [finType of resource] rat_realFieldType | 0 := 1%:R/3%:R.

Instance resourceMuAxiomInstance
  : @MuAxiomClass [finType of resource] rat_realFieldType _.
Proof. by []. Qed.

Lemma Cost_traffic_sq N t:
  \sum_(i < N) cost i t = (traffic t)%:R ^+ 2.
Proof.
  have ->: ((traffic t)%:R ^+ 2 = (traffic t)%:R * (traffic t)%:R) by [].
  rewrite {2} trafficP.
  rewrite /cost_fun /resourceCostInstance /resourceCostFun.
  rewrite /traffic' -natrM big_distrr /=.
  have ->: ((\sum_(i < N | t i == RYes) traffic (N:=N) t * 1)%:R =
            \sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R * 1).
  { move => t0. rewrite mulr1 muln1. rewrite natr_sum => //. }
  have ->: (\sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R * 1 =
            \sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R).
  { move => t0. apply congr_big => //. move => i H. rewrite mulr1 => //. }
  have ->: (\sum_(i < N | t i == RYes) (traffic (N:=N) t)%:R =
            (\sum_(i < N) if t i == RYes then (traffic (N:=N) t)%:Q else 0)).
  { by rewrite -big_mkcond. }
    by apply congr_big => //; move => i H; case: (t i).
Qed.

Lemma traffic_1_pos N t :
  0 <= (traffic (N:=N) t)%:Q + 1.
Proof. apply: addr_ge0 => //. apply: traffic_pos. Qed.

Lemma sum_one_term N i t t':
  (\sum_(i0 < N)
    (if ((if i == i0 then t' i0 else t i0) == RYes)
          && (i0 == i) then 1 else 0))%N =
  (if t' i == RYes then 1 else 0)%N.
Proof. by rewrite -big_mkcond big_mkcondl big_pred1_eq eq_refl. Qed.

(* each mixed term can be at most (traffic t) + 1
   (1 more than the unmixed cost) and there are exactly
   (traffic t') such terms (when t' i = RNo, the term is 0) *)
Lemma Cost_mixed_le N t t' :
  \sum_(i < N) cost i (upd i t t') <=
  (traffic t')%:R * ((traffic t)%:R + 1).
Proof.
  have H0: (forall i, cost i (upd i t t') <= (traffic t)%:R + 1).
  { move => i.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun /=.
    rewrite ffunE eq_refl.
    case t'i: (t' i).
    - rewrite /traffic /support_for.
      rewrite (cardD1x (j:=i)).
      suff: (#|[pred i0 | t i0 != RNo & i0 != i]|
             <= #|[pred x | t x  != RNo]|)%N.
      { have <-: #|[pred i0 | t i0 != RNo & i0 != i]|
        = #|[pred i0 |
             [ffun j => if i == j then t' j else t j] i0 != RNo & i0 != i]|.
        { apply: eq_card=> x; rewrite /in_mem /= ffunE.
          case H: (x == i)=> /=; first by rewrite 2!andbF.
          rewrite 2!andbT; case H2: (i == x)=> //.
          move: (eqP H2)=> H3; rewrite H3 /= eq_refl in H; congruence. }
        rewrite addrC natrD=> H; apply: ler_add=> //.
          by rewrite ler_nat; apply: H. }
      apply: subset_leq_card.
        by apply/subsetP=> x; rewrite /in_mem /=; case/andP.
        rewrite ffunE eq_refl; apply/eqP=> H; rewrite H in t'i; congruence.
    - apply: traffic_1_pos.
  }
  have H: \sum_(i < N) (cost) i ((upd i t) t') <=
          (\sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') : rat).
  { have ->: (\sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') =
              \sum_(i < N) if t' i == RYes then (cost) i ((upd i t) t') else 0)
      by rewrite -big_mkcond.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun.
    rewrite ler_eqVlt. apply /orP. left. apply /eqP.
    apply congr_big => //.
    move => i _. simpl. rewrite ffunE. rewrite eq_refl.
    case: (t' i) => //.
  }
  apply: ler_trans.
  apply: H.
  move {H}.
  have H: \sum_(i < N | t' i == RYes) (cost) i ((upd i t) t') <=
          \sum_(i < N | t' i == RYes) ((traffic (N:=N) t)%:R + 1).
  { apply: ler_sum.
    move => i H.
    rewrite /cost_fun /resourceCostInstance /resourceCostFun.
    rewrite /upd ffunE eq_refl 2!trafficP /traffic'.
    move: H; move => /eqP H; rewrite H.
    have ->: ((\sum_(i0 < N |
                     [ffun j => if i == j then t' j else t j] i0 == RYes) 1)%N =
              ((\sum_(i0 < N |
                      ([ffun j => if i == j then t' j else t j] i0 == RYes)
                        && (i0 == i)) 1)%N +
               (\sum_(i0 < N |
                      ([ffun j => if i == j then t' j else t j] i0 == RYes)
                        && (i0 != i)) 1)%N)%N).
    { by rewrite -bigID. }
    rewrite natrD addrC. apply: ler_add.
    have ->: (\sum_(i0 < N |
                    ([ffun j => if i == j then t' j else t j] i0 == RYes)
                      && (i0 != i)) 1)%N =
    (\sum_(i0 < N) if ((if i == i0 then t' i0 else t i0) == RYes)
                        && (i0 != i) then 1 else 0)%N.
    { by rewrite big_mkcond /=;apply congr_big => //;move => i0 _;rewrite ffunE. }
    have ->: ((\sum_(i0 < N | t i0 == RYes) 1)%N =
              (\sum_(i0 < N) if t i0 == RYes then 1 else 0)%N).
    { by rewrite big_mkcond. }
    rewrite ler_nat. apply leq_sum. move => i0 _.
    case i_i0: (i == i0).
    - have ->: ((i0 != i) = false).
      { by rewrite eq_sym; apply /negPf; rewrite i_i0. }
      rewrite andbF.
      case: (t i0 == RYes) => //.
    - have ->: ((i0 != i) = true).
      { rewrite eq_sym. apply (introT (P := i != i0)). apply: idP.
        apply (contraFneq (b := false)). move => H'. rewrite -i_i0  H'.
        apply: eq_refl => //. by []. }
      rewrite andbT => //.
      have ->: ((\sum_(i0 < N |
                       ([ffun j => if i == j then t' j else t j] i0 == RYes)
                         && (i0 == i)) 1)%N =
                (\sum_(i0 < N) if (((if i == i0 then t' i0 else t i0) == RYes)
                                     && (i0 == i)) then 1 else 0)%N).
      { by rewrite big_mkcond;apply: congr_big => //;move => i0 _;rewrite ffunE. }
      rewrite sum_one_term. case: (t' i) => //.
  }
  apply: ler_trans; first by apply: H.
  move {H}.
  have ->: \sum_(i < N | t' i == RYes) ((traffic (N:=N) t)%:R + 1) =
  (\sum_(i < N | t' i == RYes) 1 * ((traffic (N:=N) t)%:R + 1) : rat).
  { by apply: congr_big=> // i _; rewrite mul1r. }
  rewrite -mulr_suml. apply: ler_wpmul2r. apply: traffic_1_pos.
  have ->: \sum_(i | t' i == RYes) 1 =
  (\sum_(i | t' i == RYes) 1)%N%:R.
  { by move => t0; rewrite natr_sum. } (*%:R = GRing.natmul*)
  rewrite sum1_card /traffic /support_for /SimplPred /=.
  have <-: #|[pred x | t' x != RNo]| = #|[pred x | t' x == RYes]|.
  { by apply: pred_no_yes. }
    by [].
Qed.

Lemma resourceSmoothnessAxiom N (t t' : (resource ^ N)%type) :
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of [finType of resource] * Cost t' +
  mu of [finType of resource] * Cost t.
Proof.
  rewrite /Cost.
  rewrite /lambda_val /resourceLambdaInstance.
  rewrite /mu_val /resourceMuInstance.
  have H0: (\sum_(i < N) (cost) i ((upd i t) t') <=
            (traffic t')%:R * ((traffic t)%:R + 1)).
  { by apply: Cost_mixed_le. }
  have H1: ((traffic (N:=N) t')%:R * ((traffic (N:=N) t)%:R + 1) <=
            5%:R / 3%:R * (\sum_i (cost) i t') +
            1%:R / 3%:R * (\sum_i (cost) i t)).
  { by rewrite !Cost_traffic_sq; apply: Christodoulou.result. }
  apply: ler_trans H0 H1.
Qed.

Program Instance resourceSmoothAxiomInstance N
  : @SmoothnessAxiomClass [finType of resource] N rat_realFieldType _ _ _ _ _ _ _.
Next Obligation. by apply: resourceSmoothnessAxiom. Qed.
Instance resourceSmoothInstance N
  : @smooth [finType of resource] N rat_realFieldType _ _ _ _ _ _ _ _.

(** Resource games are compilable *)

Instance resourceCTypeInstance : CType [finType of resource] :=
  [:: RYes; RNo].

Program Instance resourceRefineTypeAxiomInstance
  : @RefineTypeAxiomClass [finType of resource] _.
Next Obligation.
  by split => // r; rewrite mem_enum; case: r. 
Qed.

Instance resourceRefineTypeInstance
  : @RefineTypeClass [finType of resource] _ _.

Section resourceCompilable.
Variable (N : OrdNat.t).

Definition ctraffic (m : M.t resource) : Qcoq :=
  M.fold (fun i r acc =>
            if (i < N)%N
              then match r with
                   | RYes => (acc + 1)%coq_Qscope
                   | RNo => acc
                   end
              else acc)
         m 0%coq_Qscope.

Definition ctraffic' (m : M.t resource) : Qcoq :=
  big_sumQ (M.elements m)
    (fun p =>
      match p with (k, e) =>
        if (k < N)%N
          then match e with
               | RYes => 1%coq_Qscope
               | RNo => 0%coq_Qscope
               end
          else 0%coq_Qscope
      end).

Lemma Qplus_leib_comm x y:
  (x + y)%coq_Qscope = (y + x)%coq_Qscope.
Proof.
  case: x => x1 x2.
  case: y => y1 y2.
  rewrite /Qplus /Qnum /Qden => //.
  f_equal. ring. apply Pmult_comm.
Qed.

Lemma Qplus_leib_assoc x y z:
  (x + (y + z))%coq_Qscope = ((x + y) + z)%coq_Qscope.
Proof.
  case x => x1 x2.
  case y => y1 y2.
  case z => z1 z2.
  rewrite !/Qplus !/Qnum !/Qden => //.
  f_equal. ring_simplify.
  rewrite Pos.mul_comm [(x2 * y2)%positive] Pos.mul_comm.
  rewrite !Pos2Z.inj_mul !Zmult_assoc //.
  apply Pmult_assoc.
Qed.

Lemma Qplus_leib_0_l x : (0 + x)%coq_Qscope = x.
Proof.
  case: x => x1 x2.
  rewrite /Qplus /Qnum /Qden.
  f_equal. ring.
Qed.
Lemma ctraffic_sub0 (l : seq (M.key * resource)) n :
  List.fold_left
    (fun acc p => 
        if ((nat_of_bin p.1) < N)%N
          then match p.2 with
               | RYes => (acc + 1)%coq_Qscope
               | RNo => acc
               end
          else acc)
    l n
      =
  (List.fold_left
    (fun acc p => 
        if ( (nat_of_bin p.1) < N)%N
          then match p.2 with
               | RYes => (acc + 1)%coq_Qscope
               | RNo => acc
               end
          else acc)
    l 0%coq_Qscope + n)%coq_Qscope.
Proof.
  move: n.
  induction l => //=.
  move => n0. rewrite Qplus_leib_0_l => //.
  move => n.
  case: (a.1 < N)%N => //.
  case: a.2;
  rewrite IHl => //=.
  rewrite Qplus_leib_0_l.
  rewrite (IHl 1%coq_Qscope).
  rewrite -Qplus_leib_assoc.
  f_equal. apply Qplus_leib_comm.
Qed.

Lemma ctraffic_subP l n :
  List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => (acc + 1)%coq_Qscope
               | RNo => acc
               end
          else acc)
    l n
      =
  List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => (acc + 1)%coq_Qscope
               | RNo => acc
               end
          else acc)
    (List.rev l) n.
Proof.
  rewrite -List.fold_left_rev_right.
  induction (List.rev l) => //=.
  rewrite IHl0.
  case: (a.1 < N)%N => //.
  case: (a.2) => //.
  rewrite (ctraffic_sub0 _ (n+1)%coq_Qscope) ctraffic_sub0.
  rewrite Qplus_leib_assoc => //.
Qed.

Lemma ctraffic_filter_sub0 (l : seq (M.key * resource)) n :
  List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => (acc + 1)%coq_Qscope
      | RNo => acc
      end)
    l n
      =
  (List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => (acc + 1)%coq_Qscope
      | RNo => acc
      end)
    l 0%coq_Qscope + n)%coq_Qscope.
Proof.
  move: n.
  induction l.
  {
    move => n => /=.
    rewrite Qplus_leib_0_l => //.
  }
  {
    move => n => /=.
    rewrite IHl.
    case: a.2 => //.
    rewrite (IHl (0+1)%coq_Qscope) Qplus_leib_0_l -Qplus_leib_assoc.
    f_equal.
    apply Qplus_leib_comm.
  }
Qed.

Lemma ctraffic_subF l n :
  List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => (acc + 1)%coq_Qscope
               | RNo => acc
               end
          else acc)
    l n
      =
  List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => (acc + 1)%coq_Qscope
      | RNo => acc
      end)
    (List.filter (fun p => (nat_of_bin p.1 < N)%N) l) n.
Proof.
  move: n.
  set f := 
   (fun (acc : Q) (p : BinNums.N * resource) =>
    if (p.1 < N)%N
    then match p.2 with
        | RYes => (acc + 1)%Q
        | RNo => acc
        end
    else acc).
  set f' :=
   (fun (acc : Q) (p : BinNums.N * resource) =>
   match p.2 with
   | RYes => (acc + 1)%Q
   | RNo => acc
   end). 
  induction l => //=.
  move => n.
  rewrite ctraffic_sub0 IHl.
  rewrite /f {2}/f'.
  case: (a.1 < N)%N => //=.
  case: a.2.
  rewrite (ctraffic_filter_sub0 _ (n+1)%coq_Qscope) => //.
  rewrite -/f'. symmetry. 
  apply ctraffic_filter_sub0.
  rewrite -ctraffic_filter_sub0 => //.
Qed.

Lemma absz_plus a b :
  0 <= a -> 0 <= b ->
  @eq nat_eqType (absz (@GRing.add (GRing.Ring.zmodType int_Ring) a b))
      ((absz a) + (absz b))%N.
Proof. case: a; try auto; case: b => //. Qed.

Lemma rat_to_Q_s_add x (pfx : 0 <= x) :
  (rat_to_Q 1 + rat_to_Q x)%coq_Qscope = rat_to_Q (1 + x).
Proof.
  have Hx1: (le_rat 0 x) by [].
  move: pfx. rewrite ge_rat0 in Hx1. rewrite /numq in Hx1. move: Hx1.
  case: x =>  x.
  case: x => x1 x2 => /= => pf Hx1 pfx. clear pfx.
  rewrite /(GRing.add (V := rat_Ring)) /GRing.Zmodule.add => /=.
  rewrite /addq /addq_subdef => /=.
  rewrite gcdn1 div.divn1 mul1r mulr1.
  rewrite rat_to_Q_fracq_pos_leib /rat_to_Q => /=.
  rewrite /Qplus.
  rewrite Z.mul_1_r Z.mul_1_l => /=.
  f_equal.
  rewrite -int_to_Z_plus.
  {
    case_eq (int_to_Z x1).
    {
      move => H. rewrite Z.add_0_r.
      rewrite /int_to_Z.
      destruct x2. rewrite /int_to_positive.
      rewrite Z_of_nat_pos_of_nat => //.
      case/andP: pf => //.
      case/andP: pf => //.
    }
    {
      move => p H.
      rewrite /int_to_Z.
      destruct x2. rewrite /int_to_positive.
      rewrite Z_of_nat_pos_of_nat => //.
      case/andP: pf => //.
      case/andP: pf => //.
    }
    {
      move => p H.
      rewrite /int_to_Z.
      destruct x2. rewrite /int_to_positive.
      rewrite Z_of_nat_pos_of_nat => //.
      case/andP: pf => //.
      case/andP: pf => //.
    }
  }
  case/andP: pf => //.
  {
    case/andP: pf => H0 H1.
    move: H1. rewrite /coprime. move => /eqP H1. apply /eqP.
    rewrite absz_plus; auto.
    by rewrite gcdnC gcdnDl gcdnC.
  }
Qed.

Lemma ctraffic_sub_subP (l : seq (M.key*resource)):
  let f :=
    (fun acc p => 
      match p.2 with
      | RYes => (acc + 1)%coq_Qscope
      | RNo => acc
      end) in
  List.fold_left f l 0%coq_Qscope
    =
  rat_to_Q
    ((count
      (fun p => p.2  == RYes)
      l)%:R).
Proof.
  induction l => //.
  simpl.
  case: a.2 => /=;
  rewrite ctraffic_filter_sub0 IHl => /=;
  first rewrite Qplus_leib_0_l.
  rewrite Qplus_leib_comm => //.
  have H : rat_to_Q 1 = 1%coq_Qscope
    by rewrite /rat_to_Q => //.
  rewrite -H rat_to_Q_s_add => //.
  f_equal. rewrite natrD //.
  have H1: (0%:R <= (count (fun p : M.key * resource => p.2 == RYes) l)%:R).
  { move => t. by rewrite ler_nat. }
  apply H1.
  rewrite addnC addn0.
  rewrite Qplus_leib_comm Qplus_leib_0_l => //.
Qed.

Definition resource_ccost (i : OrdNat.t) (m : M.t resource) : Qcoq :=
  match M.find i m with
  | Some RYes => ctraffic m
  | Some RNo => 0%coq_Qscope
  | None => 0%coq_Qscope (*won't occur when i < N*)
  end.

Instance resourceCCostInstance : CCostClass [finType of resource]
  := resource_ccost.

Definition lift_traffic (s : {ffun 'I_N -> resource})
  : seq (M.key*resource):=
map
  (fun (x : 'I_N) => ((N.of_nat x), s x))
  (index_enum (ordinal_finType N)).  

Lemma list_trafficP (s : {ffun 'I_N -> resource}) :
  count (fun j : (M.key*resource) => j.2 == RYes) (lift_traffic s)
  =
  count (fun j: ordinal_finType N => s j == RYes)
    (index_enum (ordinal_finType N)).
Proof.
  rewrite count_map => /=.
  rewrite -!sum1_count => //.
Qed.

Lemma list_in_iff {X : eqType} (x : X) (l : list X) :
  x \in l <-> List.In x l.
Proof.
  split.
  { elim: l.
    - move => H. inversion H.
    - move => a l IHl H. rewrite in_cons in H.
      move: H => /orP [H | H].
      + simpl. left. move: H => /eqP H. by rewrite H.
      + right. by apply IHl. }
  { elim: l.
    - move => H. inversion H.
    - move => a l IHl H.
      case: H => H; rewrite in_cons; apply /orP.
      + left. rewrite H //.
      + right. by apply IHl. }
Qed.

Lemma list_in_finType_enum {X : finType} (x : X) :
  List.In x (enum X).
Proof.
  have H: (Finite.axiom (enum X)).
  { rewrite enumT. apply enumP. }
  rewrite /Finite.axiom in H. specialize (H x).
  induction (enum X) as [| x']. inversion H.
  case Hx: (x == x').
  move: Hx => /eqP Hx.
  left. by rewrite Hx.
  right. apply IHl. simpl in H.
  rewrite eq_sym Hx in H.
    by rewrite add0n in H.
Qed.

Lemma N_of_nat_of_bin x :
  N.of_nat (nat_of_bin x) = x.
Proof.
  rewrite /nat_of_bin.
  case: x => // p.
  have H: (nat_of_pos p = Pos.to_nat p). 
  {  elim: p => // p IHp /=.
     - by rewrite Pos2Nat.inj_xI IHp NatTrec.doubleE -mul2n.
     - by rewrite Pos2Nat.inj_xO IHp NatTrec.doubleE -mul2n.
  }
  rewrite H. by apply positive_nat_N.
Qed.


Lemma of_bin_N_of_nat x :
  nat_of_bin (N.of_nat x) = x.
Proof.
  case: x => // p => //=.
  rewrite of_succ_nat_of_nat_plus_1.
  have H: forall m, nat_of_pos m = Pos.to_nat m.
  { move => m; elim: m => // m IHp /=.
     - by rewrite Pos2Nat.inj_xI IHp NatTrec.doubleE -mul2n.
     - by rewrite Pos2Nat.inj_xO IHp NatTrec.doubleE -mul2n.
  }
  rewrite H. rewrite Nat2Pos.id; first by apply addn1.
  case p => //.
Qed.

Lemma InA_NoDupA_Unique A eqA x1 x2 :
  Equivalence eqA -> 
  forall l, @SetoidList.NoDupA A eqA l ->
    List.In x1 l ->
    List.In x2 l ->
    eqA x1 x2 ->
      x1 = x2.
Proof.
  induction l => H0 H1 H2 H3; first by inversion H1.
  inversion H0; subst.
  case: H1 => H1; case: H2 => H2; subst => //=.
  {
    inversion H0. apply False_rec. apply H6 => //.
    apply SetoidList.InA_alt.
    exists x2; split => //.
  }
  {
    inversion H0. apply False_rec. apply H6 => //.
    apply SetoidList.InA_alt.
    exists x1; split => //. symmetry => //.
  }
  {
    apply IHl; inversion H0 => //.
  }
Qed.

Program Instance resourceRefineCostAxiomInstance
  : @RefineCostAxiomClass N [finType of resource] _ _.
Next Obligation.  
  rewrite /(ccost) /resourceCCostInstance /resource_ccost.
  rewrite (H i pf).
  rewrite /(cost) /resourceCostInstance /= /resourceCostFun /=.
  case H2: (s _) => //.
  rewrite /ctraffic M.fold_1 trafficP /traffic' ctraffic_subF.
  move: (M.elements_3w m) => H1.
  rewrite ctraffic_sub_subP.
  f_equal.
  rewrite sum1_count. rewrite -list_trafficP.
  f_equal.
  apply /perm_eqP.
  apply uniq_perm_eq.
  {
    induction M.elements => //=.
    case: (a.1 < N)%N => //=.
    {
      apply /andP; split.
      {
        inversion H1; subst.
        apply/negP => H6.
        apply H4.
        rewrite mem_filter in H6.
        case/andP: H6 => H6 H7.
        apply SetoidList.InA_alt.
        exists a.
        split => //.
        apply list_in_iff in H7. apply H7.
      }
      {
        apply IHl.
        inversion H1 => //.
      }
    }
    {
      apply IHl.
      inversion H1 => //.
    }
  }
  {
    rewrite /lift_traffic.
    rewrite map_inj_uniq /index_enum.
    rewrite -enumT => /=.
    apply enum_uniq.
    rewrite /injective => x1 x2 H0.
    inversion H0.
    apply Nnat.Nat2N.inj_iff in H4.
    apply ord_inj in H4 => //.
  }
  {
    rewrite /lift_traffic.
    rewrite /eq_mem => x.
    case_eq
      (x \in List.filter (fun p : BinNums.N * resource => (p.1 < N)%N)
         (M.elements (elt:=resource) m)) => H4.
    {
       rewrite mem_filter in H4.
       case/andP: H4 => H4 H5.
      have H7: exists x', (fun x0 : ordinal N => pair (N.of_nat x0) (s x0)) x' = x.
      {
        specialize (H x.1 H4).
        rewrite MProps.F.elements_o in H.
        apply SetoidList.findA_NoDupA in H => //;
          last by constructor => //=; apply N.eq_trans.
        apply list_in_iff in H5.
        apply SetoidList.InA_alt in H.
        case: H => x' H => /=.
        case: H => H H6.
        case: H => H' H''.
        simpl in H', H''.
        rewrite /N.eq in H'.
        have H: x = x'.
        apply InA_NoDupA_Unique
          with (eqA := (M.eq_key (elt := resource)))
               (l := (M.elements (elt := resource) m)) => //;
          first by apply MProps.eqk_equiv.
        exists (Ordinal H4) => //.
        destruct x as [x1 x2].
        destruct x' as [x1' x2'].
        inversion H. simpl.
        f_equal => //.
        dependent rewrite H3.
        f_equal.
        apply N_of_nat_of_bin.
      }
      case: H7 => x' H7. rewrite -H7.
      rewrite /index_enum -enumT.
      rewrite mem_map; first by rewrite mem_enum => //.
      {
        rewrite /injective => x1 x2 H0.
        inversion H0.
        apply Nnat.Nat2N.inj_iff in H6.
        apply ord_inj in H6 => //.
      }        
    }
    {
      rewrite mem_filter in H4.
      case_eq (x \in [seq (N.of_nat (nat_of_ord x0), fun_of_fin s x0)
                | x0 <- index_enum (ordinal_finType (nat_of_bin N))])=> H5 => //.
      case/mapP: H5 => y H6 H7.
      case/andP: H4; split; destruct x as [x1 x2]; inversion H7 => /=.
      rewrite /index_enum -enumT //= in H6.
      rewrite of_bin_N_of_nat => //.
      apply list_in_iff.
      clear pf H2 H7 H3 H4 H6 x1 x2.
      simpl in y.
      destruct y as [yn Hy].
      SearchAbout nat_of_bin bin_of_nat.
      move: yn Hy => yn.
      rewrite -(bin_of_natK yn) => Hy.
      specialize (H _ Hy).
      rewrite MProps.F.elements_o in H.
      apply SetoidList.findA_NoDupA in H => //;
        last by constructor => //=; apply N.eq_trans.
      apply SetoidList.InA_alt in H.
      destruct H as [z H].
      destruct H as [H H'].
      destruct H as [H H''].
      simpl in H. simpl in H''.
      have Hz: (z = (N.of_nat (Ordinal (n:=N) (m:=bin_of_nat yn) Hy),
                   s (Ordinal (n:=N) (m:=bin_of_nat yn) Hy))).
      destruct z as [z1 z2].
      f_equal. simpl in H. rewrite -H.
      simpl. rewrite N_of_nat_of_bin => //.
      simpl in H''. rewrite H'' => //.
      rewrite -Hz => //.
    }
  }
Qed.

Instance resourceRefineCostInstance
  : @RefineCostClass N [finType of resource] _ _ _.

Instance resource_cgame 
  : cgame (N:=N) (T:=[finType of resource]) _ _ _.

End resourceCompilable.

(** Location Games *)

Inductive location (T : finType) : Type :=
  Location : forall l : {set T}, location T.

Definition location_eq T (l1 l2 : location T) :=
  match l1, l2 with
  | Location x1, Location x2 => x1 == x2
  end.
Lemma location_eqP T : Equality.axiom (@location_eq T).
Proof.
  case => x1; case => x2 /=; case H: (x1 == x2); constructor.
  by move: (eqP H) => ->.
  by case=> H2; rewrite H2 eq_refl in H.
Qed.    
Definition location_eqMixin T := EqMixin (@location_eqP T).
Canonical location_eqType T := Eval hnf in EqType (location T) (@location_eqMixin T).

Definition set_of_location T (l : location T) : {set T} :=
  match l with Location x => x end.
Definition location_of_set (T : finType) (x : {set T}) : location T := Location x.
Lemma set_of_locationK T : cancel (@set_of_location T) (@location_of_set T).
Proof. by case. Qed.
Definition location_choiceMixin T := CanChoiceMixin (@set_of_locationK T).
Canonical location_choiceType T :=
  Eval hnf in ChoiceType (location T) (@location_choiceMixin T).
Definition location_countMixin T := CanCountMixin (@set_of_locationK T).
Canonical location_countType T :=
  Eval hnf in CountType (@location T) (@location_countMixin T).

Lemma Location_inj T : injective (Location (T:=T)).
Proof. by move=> x y; case=> ->. Qed.

Definition location_enum (T : finType) := map (@Location T) (enum {set T}).
Lemma location_enumP T : Finite.axiom (location_enum T).
Proof.
  move=> x; apply: Finite.uniq_enumP.
  { rewrite map_inj_uniq; first by apply: enum_uniq.
    by apply: Location_inj. }
  move=> y; rewrite /location_enum inE; case: y => l; rewrite mem_map.
  by rewrite mem_enum.
  by apply: Location_inj.    
Qed.  
  
Definition location_finMixin T := Eval hnf in FinMixin (@location_enumP T).
Canonical location_finType T := Eval hnf in FinType (location T) (@location_finMixin T).

Section locationDefs.
  Context (N : nat) (rty : realFieldType) (T : finType).
  Context `{game [finType of {set T}] N rty}.
  Variable C : {set T} -> rty.
  Local Open Scope ring_scope.

  Definition U (s : {ffun 'I_N -> {set T}}) : {set T} :=
    [set l | [exists i, l \in s i]].
  
  Definition submodular (f : {set T} -> {set T}) :=
    forall s t : {set T},
      s \subset t ->
      C (s :&: t) + C (s :|: t) >= C s + C t.

  Definition W s := (C (U s)).

  Definition nullify_player (i : 'I_N) (s : {ffun 'I_N -> {set T}}) :=
    finfun (fun j => if i == j then set0 else s j).

  Definition Z i (s s' : {ffun 'I_N -> {set T}}) :=
    U s :|: \bigcup_(j : 'I_N | (j <= i)%N) (s j).
  
  Variable C_cond1 :
    forall (i : 'I_N) s, cost i s <= W s - W (nullify_player i s).
  Variable C_cond2 : forall s, \sum_(i : 'I_N) cost i s >= W s.
  Variable C_antimono :
    forall s t : {set T}, s \subset t -> C s >= C t.

  Lemma location_lem1 s s' :
    \sum_(i : 'I_N) cost i (upd i s s') <= W s' - W s.
  Proof.
    have H1:
      \sum_(i < N) (cost) i ((upd i s) s') <=
      \sum_(i < N) (W (upd i s s') - W (nullify_player i s)).
    { admit. }
    apply: ler_trans; first by apply: H1.
    have H2:
      \sum_(i < N) (W ((upd i s) s') - W (nullify_player i s)) <=
      \sum_(i < N) (C (Z i s s') - C (Z (i - 1) s s')).
    { admit. }
    apply: ler_trans; first by apply: H2.
    rewrite big_split /W => /=.
    have ->:
      \sum_(i < N) - C (Z (i - 1) s s') =
      - \sum_(i < N) C (Z (i - 1) s s').
    { admit. }
    have H3: \sum_(i < N) C (Z i s s') <= C (U s').
    { admit. }
    have H4: C (U s) <= \sum_(i < N) C (Z (i - 1) s s').
    { admit. }
    apply: ler_add => //; by rewrite ler_oppl opprK.
  Admitted.             
End locationDefs.

(** "Boolable" Types *)

Class Boolable (A : Type) : Type :=
  boolify : A -> bool.

Instance boolable_Resource : Boolable resource :=
  fun r => match r with RYes => true | RNo => false end.

(** Singleton Games A : Boolable, 
    c_i s = if (boolify s_i) then 1 else 0 *)

Section SingletonType.
Variable rty : realFieldType.
  
Inductive Singleton : Type := mkSingleton : Singleton.

Definition Singleton_eq (s1 s2 : Singleton) : bool := true.

Lemma Singleton_eqP : Equality.axiom Singleton_eq.
Proof. by case; case; constructor. Qed.
  
Definition Singleton_eqMixin := EqMixin Singleton_eqP.
Canonical Singleton_eqType := Eval hnf in EqType Singleton Singleton_eqMixin.

Definition singleton (A : finType) :=
  Wrapper [eqType of Singleton] A.

Definition singletonType (A : finType) :=
  [finType of Wrapper [eqType of Singleton] A].
End SingletonType.

Instance BoolableSingleton (A : finType) `(Boolable A)
  : Boolable (singletonType A) :=
  fun (s : singletonType A) => boolify (unwrap s).

Instance singletonCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(costA : CostClass N rty A)
         `(boolableA : Boolable A)
  : CostClass N rty (singletonType A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> singletonType A}) =>
    if boolify (f i) then 1 else 0.

Program Instance  singletonCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(costA : CostAxiomClass N rty A)
        `(boolableA : Boolable A)        
  : @CostAxiomClass
      N rty
      (singletonType A)
      (@singletonCostInstance N rty _ _ _).
Next Obligation.
  rewrite /(cost) /singletonCostInstance; case: (boolify _); first by apply: ler01.
  by apply: lerr.
Qed.

(*Uses the generic move instance for wrapped types*)

Instance singletonGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(Boolable A) 
        `(gameA : game A N rty)
  : @game (singletonType A) N rty _ _.

Module SingletonGameTest. Section singletonGameTest.
  Context {A N rty} `{gameA : game A N rty} `{Boolable A}.
  Variables (t : {ffun 'I_N -> singletonType A}) (i : 'I_N).
  Check cost i t.
End singletonGameTest. End SingletonGameTest.

Instance singletonLambdaInstance
         (rty : realFieldType) (A : finType)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (singletonType A) rty | 0 := lambda of A.

Program Instance singletonLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (singletonType A) rty _ | 0.

Instance singletonMuInstance
         (rty : realFieldType) (A : finType)
         `(lambdaA : MuClass A rty)
  : @MuClass (singletonType A) rty | 0 := mu of A.

Program Instance singletonMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (singletonType A) rty _ | 0.

Class LambdaGe1Class (A : finType) N (rty : realFieldType) `(smooth A N rty)
  : Type := lambda_ge1 : 1 <= lambda of A.

Program Instance singletonSmoothAxiomInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{boolableA : Boolable A}
         `{LambdaGe1Class A N rty}
  : @SmoothnessAxiomClass (singletonType A) N rty _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /singletonCostInstance.
  rewrite /lambda_val /singletonLambdaInstance.
  rewrite /mu_val /singletonMuInstance.
  have ->:
   \sum_(i < N)
      (if boolify ([ffun j => if i == j then t' j else t j] i) then 1 else 0) =
   \sum_(i < N) (if boolify (t' i) then 1 else (0 : rty)).
  { by apply/congr_big => // i _; rewrite ffunE eq_refl. }
  rewrite -[\sum_i (if boolify (t' i) then 1 else 0)]addr0; apply: ler_add.
  rewrite addr0; apply: ler_pemull=> //.
  apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
  apply: mulr_ge0; first by apply: mu_pos.
  by apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
Qed.  

Instance singletonSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{boolableA : Boolable A}
         `{LambdaGe1Class A N rty}
  : @smooth (singletonType A) N rty _ _ _ _ _ _ _ _.

Module SingletonSmoothTest. Section singletonSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty}.
  Context `{Boolable A} `{LambdaGe1Class A N rty}.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == lambda of (singletonType A). Abort.
End singletonSmoothTest. End SingletonSmoothTest.

(** Sigma Games {x : A | P x}, with P : A -> bool *)

Class PredClass (A : Type) := the_pred : A -> bool.

Instance sigmaCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         (predInstance : PredClass A)
         `(costA : CostClass N rty A)
  : CostClass N rty [finType of {x : A | the_pred x}] := 
  fun (i : 'I_N) (f : {ffun 'I_N -> {x : A | the_pred x}}) => 
    cost i [ffun j => projT1 (f j)]. 

Program Instance  sigmaCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        (predInstance : PredClass A)        
        `(costA : CostAxiomClass N rty A)
  : @CostAxiomClass N rty [finType of {x : A | the_pred x}] _.
  Next Obligation.
    rewrite /(cost) /sigmaCostInstance.
    apply: cost_axiom.
  Qed.

Instance sigmaGameInstance
         (N : nat) (rty : realFieldType) (A : finType)
         (predInstance : PredClass A)                 
         `(gameA : game A N rty)
  : @game [finType of {x : A | the_pred x}] _ _ _ _.

Module SigmaGameTest. Section sigmaGameTest.
  Context {A : finType} {N rty} (predA : PredClass A) `{gameA : game A N rty}.
  Variables (t : {ffun 'I_N -> {x : A | the_pred x}}) (i : 'I_N).
  Check cost i t.
End sigmaGameTest. End SigmaGameTest.

Instance sigmaLambdaInstance
         (rty : realFieldType) (A : finType)
         `(lambdaA : LambdaClass A rty)
         (predInstance : PredClass A)
  : @LambdaClass [finType of {x : A | the_pred x}] rty | 0 :=
  lambda of A.

Instance sigmaMuInstance
         (rty : realFieldType) (A : finType)
         `(muA : MuClass A rty)
         (predInstance : PredClass A)
  : @MuClass [finType of {x : A | the_pred x}] rty | 0 :=
  mu of A.

Lemma sigmaSmoothnessAxiom
      (N : nat) (rty : realFieldType) (A : finType)
      (predInstance : PredClass A)
      `{smoothA : smooth A N rty}
      (t t' : {ffun 'I_N -> {x : A | the_pred x}}) :
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of [finType of {x : A | the_pred x}] * Cost t' +
  mu of [finType of {x : A | the_pred x}] * Cost t.
Proof.
  rewrite /Cost /cost_fun /sigmaCostInstance /cost_fun.
  have ->: (lambda of [finType of {x : A | the_pred x}] = lambda of A) by [].
  have ->: (mu of [finType of {x : A | the_pred x}] = mu of A) by [].
  have ->: (\sum_(i < N) H i [ffun j => projT1 (((upd i t) t') j)] =
            \sum_(i < N) H i
             ((upd i [ffun j => projT1 (t j)]) [ffun j => projT1 (t' j)])).
  { apply congr_big => // i _. f_equal. apply ffunP => x /=.
    rewrite !ffunE. case: (i == x) => //. }
  apply (smooth_ax _).
Qed.

(** [NOTE CType instances]
    ~~~~~~~~~~~~~~~~~~~~~~
    [CType] instances should in general avoid using Ssreflect [enum]. 
    The reason is, extraction (and computation) of [enum ...] doesn't 
    usually (or ever...?) result in usable OCaml terms. Instead, 
    use the [enumerate] function of the underlying type to build the 
    instance at the current type.

    The example below illustrates the general problem: *)

Definition resources : list resource := Eval hnf in enum [finType of resource].
Extraction resources.
(* let resources =
  filter
    (pred_of_simpl
      (pred_of_mem_pred
        (mem predPredType (sort_of_simpl_pred pred_of_argType))))
    (Obj.magic Finite.EnumDef.enum
      (Finite.clone resource_finType (Finite.coq_class resource_finType))) *)
Definition resources' : list resource := Eval hnf in enumerate [finType of resource].
Extraction resources'.
(* let resources' =
  Cons (RYes, (Cons (RNo, Nil))) *)

(** Sigma games are compilable *)
(* GS: I'm commenting out this instance for now, to be fixed by me and 
       Alex after the 5900 midterm :-)
Section sigmaCompilable.
  Variable (N : OrdNat.t).
  
  Instance sigmaCTypeInstance (A : finType)
           (predInstance : PredClass A)
  : CType [finType of {x : A | the_pred x}] :=
    enum [finType of {x : A | the_pred x}].

  Program Instance sigmaRefineTypeAxiomInstance
          (A : finType)
          (predInstance : PredClass A)
  : @RefineTypeAxiomClass [finType of {x : A | the_pred x}] _.
  Next Obligation. by move=> r; rewrite mem_enum. Qed.

  Instance sigmaCCostInstance
           (A : finType)
           (predInstance : PredClass A)
           (ccostA : @CCostClass A)
  : CCostClass [finType of {x : A | the_pred x}]
    :=
      fun (i : OrdNat.t) (m : M.t {x : A | the_pred x}) =>
        0%coq_Qscope.
End sigmaCompilable.*)

(** Product Games A * B *)

Instance prodCostInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(costA : CostClass N rty aT)
         `(costB : CostClass N rty bT)         
  : CostClass N rty [finType of (aT*bT)] :=
  fun (i : 'I_N) (f : {ffun 'I_N -> aT*bT}) =>
    cost i (finfun (fun j => (f j).1)) +
    cost i (finfun (fun j => (f j).2)).  

Program Instance  prodCostAxiomInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(costA : CostAxiomClass N rty aT)
         `(costB : CostAxiomClass N rty bT)         
  : @CostAxiomClass N rty [finType of (aT*bT)] _.
  Next Obligation.
    rewrite /(cost) /prodCostInstance.
    apply addr_ge0 => //.
  Qed.

Instance prodGameInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(gameA : game aT N rty)
         `(gameB : game bT N rty) 
  : @game [finType of aT*bT] _ _ _ _.

Lemma lambda_of_finType (T : finType) `(smooth T) :
  lambda of T = lambda of [finType of T].
Proof. by []. Qed.

Lemma mu_of_finType (T : finType) `(smooth T) :
  mu of T = mu of [finType of T].
Proof. by []. Qed.

Module ProdGameTest. Section prodGameTest.
  Context {A B N rty} `{gameA : game A N rty} `{gameB : game B N rty}.
  Variables (t : {ffun 'I_N -> A*A}) (i : 'I_N).
  Check cost i t.
End prodGameTest. End ProdGameTest.

(*In the instance that follows, the "| 0" sets the instance 
  priority (for use in typeclass resolution), with 0 being 
  "highest". Priority 0 ensures that "prodLambda" is preferred 
  over the generic finType clone instance for LambdaClass.*)

Instance prodLambdaInstance
         (rty : realFieldType) (aT bT : finType)
         `(lambdaA : LambdaClass aT rty)
         `(lambdaB : LambdaClass bT rty)  
  : @LambdaClass [finType of (aT*bT)] rty | 0 :=
  maxr (lambda of aT) (lambda of bT).

Program Instance prodLambdaAxiomInstance
         (rty : realFieldType) (aT bT : finType)
         `(lambdaA : LambdaAxiomClass aT rty)
         `(lambdaB : LambdaAxiomClass bT rty)
  : @LambdaAxiomClass [finType of (aT*bT)] rty _.
Next Obligation.
  rewrite /lambda_val /prodLambdaInstance.
  by rewrite ler_maxr; apply/orP; left; apply: lambda_pos.
Qed.

Lemma lambdaA_le_prodLambda N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  lambda of [finType of aT] <= lambda of [finType of aT*bT].
Proof. by rewrite /prodLambdaInstance; rewrite ler_maxr; apply/orP; left. Qed.

Lemma lambdaB_le_prodLambda N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  lambda of [finType of bT] <= lambda of [finType of aT*bT]. 
Proof. by rewrite /prodLambdaInstance; rewrite ler_maxr; apply/orP; right. Qed.

Instance prodMuInstance
         (rty : realFieldType) (aT bT : finType)
         `(muA : MuClass aT rty)
         `(muB : MuClass bT rty)
  : @MuClass [finType of (aT*bT)] rty | 0 :=
  maxr (mu of aT) (mu of bT).

Program Instance prodMuAxiomInstance
        (rty : realFieldType) (aT bT : finType)
        `(muA : MuAxiomClass aT rty)
        `(muB : MuAxiomClass bT rty)
  : @MuAxiomClass [finType of (aT*bT)] rty _ | 0.
Next Obligation.
  rewrite /mu_val /prodMuInstance ler_maxr; apply/andP; split.
  { apply/orP; left; apply: mu_pos. }
  by rewrite ltr_maxl; apply/andP; split; apply: mu_lt1.
Qed.  

Lemma muA_le_prodMu N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  mu of [finType of aT] <= mu of [finType of aT*bT].
Proof. by rewrite /prodMuInstance; rewrite ler_maxr; apply/orP; left. Qed.

Lemma muB_le_prodMu N rty aT bT
      `(gameA : smooth aT N rty)
      `(gameB : smooth bT N rty) :
  mu of [finType of bT] <= mu of [finType of aT*bT]. 
Proof. by rewrite /prodMuInstance; rewrite ler_maxr; apply/orP; right. Qed.

Lemma prodSmoothnessAxiom' {aT bT N rty}
      `{smoothA : smooth aT N rty}
      `{smoothB : smooth bT N rty}
      (t t' : ((aT*bT) ^ N)%type) :
  \sum_(i < N)
    (cost) i [ffun j => ([ffun j0 => if i == j0 then t' j0 else t j0] j).1] =
  \sum_(i < N)
    (cost) i ([fun j0 => [ffun j => if i == j then (j0 j).1 else (t j).1]] t').
Proof.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  case: (i ==x) => //.
Qed.

Lemma prodSmoothnessAxiom {aT bT N rty}
      `{smoothA : smooth aT N rty}
      `{smoothB : smooth bT N rty}
  (t t' : ((aT*bT) ^ N)%type) :
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of [finType of aT*bT] * Cost t' + mu of [finType of aT*bT] * Cost t.
Proof.
  rewrite /Cost!big_split.
  rat_to_ring.
  set m := mu of [finType of aT * bT].
  set l := lambda of [finType of aT * bT]. 
  rewrite !mulrDr.
  rewrite [m * _ + _] addrC -addrA [l * _ + (m * _ + _)]
          addrA [(l * _ + _) + _] addrC !addrA -addrA.
  apply ler_add.
  apply ler_trans with
    (y := (lambda of [finType of aT]) *
          (\sum_(i < N) (cost) i [ffun j => (t' j).1]) +
          (mu of [finType of aT]) *
          (\sum_(i < N) (cost) i [ffun j => (t j).1])).
  rewrite -lambda_of_finType.
  rewrite -mu_of_finType.
  eapply (ler_trans _
    (smooth_ax _ _)).
  apply ler_add;
  rewrite ler_wpmul2r => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (lambdaA_le_prodLambda smoothA) => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (muA_le_prodMu smoothA) => //.
  apply ler_trans with
    (y := (lambda of [finType of bT]) *
          (\sum_(i < N) (cost) i [ffun j => (t' j).2]) +
          (mu of [finType of bT]) *
          (\sum_(i < N) (cost) i [ffun j => (t j).2])).
  rewrite -lambda_of_finType.
  rewrite -mu_of_finType.
  eapply (ler_trans _
    (smooth_ax _ _)).
  apply ler_add;
  rewrite ler_wpmul2r => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (lambdaB_le_prodLambda smoothA) => //.
  apply big_rec => //=.
  move => i x _ h'.
  apply addr_ge0 => //=.
  apply (muB_le_prodMu smoothA) => //.
  Unshelve.
  rewrite ler_eqVlt.
  apply /orP.
  left.
  apply/eqP.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite /upd.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  case: (i ==x) => //.
  rewrite ler_eqVlt.
  apply /orP.
  left.
  apply/eqP.
  apply eq_bigr.
  move => i _.
  apply f_equal.
  rewrite /upd.
  rewrite -ffunP.
  rewrite /eqfun.
  move => x.
  rewrite !ffunE.
  by case: (i ==x).
Qed.

Instance prodSmoothAxiomInstance {aT bT N rty}
         `{smoothA : smooth aT N rty}
         `{smoothB : smooth bT N rty}
  : @SmoothnessAxiomClass [finType of (aT*bT)] N rty _ _ _ _ _ _ _
  := prodSmoothnessAxiom.

Instance prodSmoothInstance {aT bT N rty}
         `{smoothA : smooth aT N rty}
         `{smoothB : smooth bT N rty}
  : @smooth [finType of (aT*bT)] N rty _ _ _ _ _ _ _ _.

Module ProdSmoothTest. Section prodSmoothTest.
  Context {A B N rty} `{gameA : smooth A N rty} `{gameB : smooth B N rty}.
  Lemma x0 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t == 0. Abort.
  Lemma x1 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t <= lambda of A. Abort.
  Lemma x2 (t : {ffun 'I_N -> A*B}) (i : 'I_N) :
    mu of [finType of A * B] == lambda of [finType of A * B]. Abort.
End prodSmoothTest. End ProdSmoothTest.

(** Product Games are compilable *)

Lemma allpairs_list_prod (A B : eqType) (l1 : seq A) (l2 : seq B) :
  [seq (a, b) | a <- l1, b <- l2] = List.list_prod l1 l2.
Proof.
  elim: l1 l2 => // a l IH l2 /=; rewrite IH.
  have ->: [seq (a, b) | b <- l2] = List.map [eta pair a] l2.
  { move {IH l}; elim: l2 => //. }
  by [].
Qed.

Lemma list_prod_uniq (A B : eqType) (l1 : seq A) (l2 : seq B) :
  uniq l1 ->
  uniq l2 ->
  uniq (List.list_prod l1 l2).
Proof.
  move => H1 H2; move: (allpairs_uniq H1 H2 (f:=fun a b => (a,b))).
  by rewrite -allpairs_list_prod; apply; case => x y; case => z w.
Qed.

Section prodCompilable.
  Variable (N : OrdNat.t).

  Instance prodCTypeInstance (aT bT : finType)
    : CType [finType of (aT*bT)] :=
    List.list_prod (enum aT) (enum bT).

  Program Instance prodRefineTypeAxiomInstance
          (aT bT : finType)
    : @RefineTypeAxiomClass [finType of aT*bT] _.
  Next Obligation.
    split. 
    { move => r. rewrite mem_enum. case: r. move => a b.
      rewrite /prodCTypeInstance /ctype_fun.
      have H: (List.In (a, b) (List.list_prod (enum aT) (enum bT))).
      { apply List.in_prod_iff. split; apply list_in_finType_enum. }
        by apply list_in_iff in H. }
    by apply: list_prod_uniq; apply: enum_uniq.
  Qed.

  Instance prodRefineTypeInstance (aT bT : finType)
    : @RefineTypeClass [finType of aT*bT]  _ _.
  
  Definition map_split {aT bT : Type} (m : M.t (aT*bT)) :=
    M.fold (fun i r acc =>
              match r with
              | (a, b) =>
                (M.add i a acc.1, M.add i b acc.2)
              end)
           m (M.empty aT, M.empty bT).
  
  Lemma map_split_spec (aT bT : Type) i (a : aT) (b : bT) m :
    M.find i m = Some (a, b) ->
    M.find i (map_split m).1 = Some a /\
    M.find i (map_split m).2 = Some b.
  Proof.
    { rewrite /map_split. apply MProps.fold_rec_weak.
      { move => mo m' a' H0 H1 H2.
        have H3: (forall (k : M.key) (e : (aT*bT)),
                     M.MapsTo k e mo <-> M.MapsTo k e m').
        { by apply MProps.F.Equal_mapsto_iff; apply H0. }
        apply M.find_2 in H2. apply H3 in H2. apply M.find_1 in H2.
        apply H1. apply H2. }
      { move => H. inversion H. }
      { move => k e a' m' H0 IH. case: e. move => a0 b0 H2 /=.
        rewrite MProps.F.add_o. case: (MProps.F.eq_dec k i) => H3 //.
        rewrite MProps.F.add_eq_o in H2; auto. inversion H2.
        split. auto. rewrite MProps.F.add_eq_o //.
        split. apply IH. rewrite MProps.F.add_neq_o in H2.
        apply H2. apply H3.
        rewrite MProps.F.add_neq_o. apply IH.
        rewrite MProps.F.add_neq_o in H2.
        apply H2. apply H3. apply H3. } }
  Qed.

  Instance prodCCostInstance
           (aT bT : finType)
           `(ccostA : CCostClass aT)
           `(ccostB : CCostClass bT)
    : CCostClass [finType of aT*bT]
    :=
      fun (i : OrdNat.t) (m : M.t (aT*bT)) =>
        Qred (match M.find i m with
              | Some (a, b) => (ccost i (map_split m).1 +
                               ccost i (map_split m).2)%coq_Qscope
              | _ => 0%coq_Qscope
              end).
  
  Program Instance prodRefineCostAxiomInstance
          (aT bT : finType)
          (costA : CostClass N rat_realFieldType aT)
          (costB : CostClass N rat_realFieldType bT)
          (ccostA : CCostClass aT)
          (ccostB : CCostClass bT)
          (refineA : RefineCostAxiomClass costA ccostA)
          (refineB : RefineCostAxiomClass costB ccostB)
    : @RefineCostAxiomClass
        N [finType of aT*bT]
        (@prodCostInstance N rat_realFieldType aT bT costA costB)
        (@prodCCostInstance aT bT ccostA ccostB).
  Next Obligation.
    rewrite /cost_fun /prodCostInstance /cost_fun.
    rewrite /ccost_fun /prodCCostInstance /ccost_fun.
    rewrite /RefineCostAxiomClass in refineA.
    rewrite /RefineCostAxiomClass in refineB.
    rewrite (H i pf).
    move: H.
    have ->: (s (Ordinal (n:=N) (m:=i) pf) =
              ((s (Ordinal (n:=N) (m:=i) pf)).1,
               (s (Ordinal (n:=N) (m:=i) pf)).2)).
    { by case: (s (Ordinal (n:=N) (m:=i) pf)). }
    move => H.
    have H2: ((ccost) i (map_split m).1 =
              rat_to_Q
                ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).1])).
    { apply refineA. move => j pf'.
      rewrite ffunE.
      specialize (H j pf').
      move: H. case: (s (Ordinal (n:=N) (m:=j) pf')) => a b H.
      apply map_split_spec in H.
      case: H => H0 H1.
      apply H0. }
    have H3: ((ccost) i (map_split m).2 =
              rat_to_Q
                ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).2])).
    { apply refineB. move => j pf'.
      rewrite ffunE.
      specialize (H j pf').
      move: H. case: (s (Ordinal (n:=N) (m:=j) pf')) => a b H.
      apply map_split_spec in H.
      case: H => H0 H1.
      apply H1. }
    have H4: ((ccostA i (map_split m).1 =
               rat_to_Q
                 ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).1]))).
    { apply H2. }
    have H5: ((ccostB i (map_split m).2 =
               rat_to_Q
                 ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).2]))).
    { apply H3. }
    rewrite H4 H5 [rat_to_Q (_ + _)] rat_to_Q_red.
    apply Qred_complete. apply Qeq_sym. apply rat_to_Q_plus.
Qed.
  
  Instance prodRefineCostInstance (aT bT : finType)
           (costA : CostClass N rat_realFieldType aT)
           (costB : CostClass N rat_realFieldType bT)
           (ccostA : CCostClass aT)
           (ccostB : CCostClass bT)
           (refineA : RefineCostAxiomClass costA ccostA)
           (refineB : RefineCostAxiomClass costB ccostB)
    : @RefineCostClass N [finType of aT*bT] _ _ _.

  Instance prod_cgame (aT bT : finType)
           `(costA : CostClass N rat_realFieldType aT)
           `(costAxiomA : @CostAxiomClass N rat_realFieldType aT costA)
           `(ccostA : CCostClass aT)
           `(refineTypeA : RefineTypeClass aT)
           `(refineCostAxiomA : @RefineCostAxiomClass N aT costA ccostA)
           `(refineCostA : @RefineCostClass N aT costA ccostA _)
           `(gA : @game aT N rat_realFieldType _ _)
           `(cgA : @cgame N aT _ _ _ _ _ _ _ _ _)
           `(costB : CostClass N rat_realFieldType bT)
           `(costAxiomB : @CostAxiomClass N rat_realFieldType bT costB)
           `(ccostB : CCostClass bT)
           `(refineTypeB : RefineTypeClass bT)
           `(refineCostAxiomB : @RefineCostAxiomClass N bT costB ccostB)
           `(refineCostB : @RefineCostClass N bT costB ccostB _)
           `(gB : @game bT N rat_realFieldType _ _)
           `(cgB : @cgame N bT _ _ _ _ _ _ _ _ _)
    : @cgame N [finType of aT*bT] (prodCTypeInstance aT bT)
             (prodRefineTypeAxiomInstance aT bT)
             (prodRefineTypeInstance aT bT) _ _ _ _ _ _.
End prodCompilable.

(** Scalar Games c * A *)

Section ScalarType.
Variable rty : realFieldType.
  
Inductive Scalar : rty -> Type :=
  mkScalar : forall (c : rty), Scalar c.

Definition Scalar_eq c (s1 s2 : Scalar c) : bool := 
  match s1, s2 with
  | mkScalar r1, mkScalar r2 => r1 == r2
  end.
Lemma Scalar_eqP c : Equality.axiom (@Scalar_eq c).
Proof. by case=> s; case=> r /=; rewrite eq_refl; constructor. Qed.
  
Definition Scalar_eqMixin c := EqMixin (@Scalar_eqP c).
Canonical Scalar_eqType c :=
  Eval hnf in EqType (@Scalar c) (Scalar_eqMixin c).

Definition scalar (c : rty) (A : finType) :=
  Wrapper (Scalar c) A.

Definition scalarType (c : rty) (A : finType) :=
  [finType of Wrapper (Scalar c) A].
End ScalarType.

Class ScalarClass (rty : realFieldType)
  : Type := scalar_val : rty.

Class ScalarAxiomClass (rty : realFieldType)
      `(ScalarClass rty)
  : Type := scalar_axiom : 0 < scalar_val.

Instance scalarCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(costA : CostClass N rty A)
         `(scalarA : ScalarClass rty)
  : CostClass N rty (scalarType scalar_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> scalarType scalar_val A}) =>
    scalar_val * cost i (unwrap_ffun f).

Program Instance  scalarCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(costA : CostAxiomClass N rty A)
        `(scalarA : ScalarAxiomClass rty)        
  : @CostAxiomClass
      N rty
      (scalarType scalar_val A)
      (@scalarCostInstance N rty _ _ _).
Next Obligation.
  rewrite /(cost) /scalarCostInstance mulr_ge0=> //.
  by apply: ltrW.
Qed.

Instance scalarGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(ScalarAxiomClass rty) 
        `(gameA : game A N rty)
  : @game (scalarType scalar_val A) N rty 
          (@scalarCostInstance N rty A _ _)
          (@scalarCostAxiomInstance N rty A _ _ _ _).

Module ScalarGameTest. Section scalarGameTest.
  Context {A N rty} `{gameA : game A N rty} `{scalarA : ScalarAxiomClass rty}.
  Variables (t : {ffun 'I_N -> scalarType scalar_val A}) (i : 'I_N).
  Check cost i t.
End scalarGameTest. End ScalarGameTest.

Instance scalarLambdaInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (scalarType scalar_val A) rty | 0 := lambda of A.

Program Instance scalarLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (scalarType scalar_val A) rty _ | 0.

Instance scalarMuInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (scalarType scalar_val A) rty | 0 := mu of A.

Program Instance scalarMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (scalarType scalar_val A) rty _ | 0.

Program Instance scalarSmoothAxiomInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @SmoothnessAxiomClass (scalarType scalar_val A) N rty _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /scalarCostInstance.
  rewrite /lambda_val /scalarLambdaInstance.
  rewrite /mu_val /scalarMuInstance.
  rewrite -3!mulr_sumr.
  rewrite mulrA [lambda of A * _]mulrC -mulrA.
  rewrite [mu of A * _]mulrA [mu of A * _]mulrC -mulrA.
  rewrite -mulrDr; apply: ler_mull=> //.
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smooth_ax.
Qed.

Instance scalarSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @smooth (scalarType scalar_val A) N rty _ _ _ _ _ _ _ _.

Module ScalarSmoothTest. Section scalarSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{scalarA : ScalarAxiomClass rty}.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == lambda of (scalarType scalar_val A). Abort.
End scalarSmoothTest. End ScalarSmoothTest.

Section scalarCompilable.
  Variable (N : OrdNat.t).
  Variable (q : Q).
  Variable T : finType.
  Definition scalar_q := scalar (Q_to_rat q) T.
  Definition scalar_T := scalarType (Q_to_rat q) T.
  Instance scalarCTypeInstance
    (** NOTE: This instance should be updated to use [enumerate]. 
        For rationale, see [NOTE: CType instances] above. *)           
    : CType (scalarType (Q_to_rat q) T) := enum scalar_T.

  Program Instance scalarRefineTypeAxiomInstance
    : @RefineTypeAxiomClass _ scalarCTypeInstance.
  Next Obligation.
    split => //.
    rewrite /ctype_fun /scalarCTypeInstance.
    apply: enum_uniq.
  Qed.
    
  Instance scalarRefineTypeInstance
    : @RefineTypeClass _ scalarCTypeInstance scalarRefineTypeAxiomInstance.

  Definition stripScalar : scalar_T -> T :=
   fun x : scalar_T =>
    match x with
    | @Wrap _ _ x' => x'
    end.

  Definition stripScalar_t : M.t scalar_T -> M.t T :=
  fun m : (M.t scalar_T) =>
    M.fold (fun i r acc =>
              M.add i (stripScalar r) acc)
      m (M.empty T).

  Instance scalarCCostInstance
    `(ccostT : CCostClass T)
    : CCostClass scalar_T
    :=
      fun (i : OrdNat.t) (m : M.t scalar_T) =>
        Qmult q (ccostT i (stripScalar_t m)).

  Program Instance scalarRefineCostAxiomInstance
          (costT : CostClass N rat_realFieldType T)
          (ccostT : CCostClass T)
          (refine : RefineCostAxiomClass costT ccostT)
    : @RefineCostAxiomClass
        N scalar_T
        (@scalarCostInstance N rat_realFieldType T costT (Q_to_rat q))
        (@scalarCCostInstance ccostT).
  Next Obligation.
    rewrite /(ccost) /scalarCCostInstance /(cost) /scalarCostInstance => /=.
    rewrite /scalar_val.
    admit.
  Admitted.
(*
  Instance scalarRefineCostInstance
    : @RefineCostClass N _ _ _ scalarRefineCostAxiomInstance.

  Instance prod_cgame (aT bT : finType)
           `(costA : CostClass N rat_realFieldType aT)
           `(costAxiomA : @CostAxiomClass N rat_realFieldType aT costA)
           `(ccostA : CCostClass aT)
           `(refineTypeA : RefineTypeClass aT)
           `(refineCostAxiomA : @RefineCostAxiomClass N aT costA ccostA)
           `(refineCostA : @RefineCostClass N aT costA ccostA _)
           `(gA : @game aT N rat_realFieldType _ _)
           `(cgA : @cgame N aT _ _ _ _ _ _ _ _ _)
           `(costB : CostClass N rat_realFieldType bT)
           `(costAxiomB : @CostAxiomClass N rat_realFieldType bT costB)
           `(ccostB : CCostClass bT)
           `(refineTypeB : RefineTypeClass bT)
           `(refineCostAxiomB : @RefineCostAxiomClass N bT costB ccostB)
           `(refineCostB : @RefineCostClass N bT costB ccostB _)
           `(gB : @game bT N rat_realFieldType _ _)
           `(cgB : @cgame N bT _ _ _ _ _ _ _ _ _)
    : @cgame N [finType of aT*bT] (prodCTypeInstance aT bT)
             (prodRefineTypeAxiomInstance aT bT)
             (prodRefineTypeInstance aT bT) _ _ _ _ _ _.
*)

End scalarCompilable.

(** Bias Games c + A *)

Section BiasType.
Variable rty : realFieldType.
  
Inductive Bias : rty -> Type :=
  mkBias : forall c : rty, Bias c.

Definition Bias_eq c (s1 s2 : Bias c) : bool := 
  match s1, s2 with
  | mkBias r1, mkBias r2 => r1 == r2
  end.
Lemma Bias_eqP c : Equality.axiom (@Bias_eq c).
Proof. by case=> s; case=> r /=; rewrite eq_refl; constructor. Qed.
  
Definition Bias_eqMixin c := EqMixin (@Bias_eqP c).
Canonical Bias_eqType c :=
  Eval hnf in EqType (@Bias c) (Bias_eqMixin c).

Definition bias (c : rty) (A : finType) :=
  Wrapper (Bias c) A.

Definition biasType (c : rty) (A : finType) :=
  [finType of Wrapper (Bias c) A].
End BiasType.

Instance biasCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(costA : CostClass N rty A)
  : CostClass N rty (biasType scalar_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> biasType scalar_val A}) =>
    scalar_val + cost i (finfun (fun j => unwrap (f j))).

Program Instance  biasCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(costA : CostAxiomClass N rty A)
  : @CostAxiomClass N rty (biasType scalar_val A) (@biasCostInstance N rty _ scalar_val _).
Next Obligation.
  rewrite /(cost) /biasCostInstance addr_ge0 => //.
  by apply: ltrW; apply scalar_axiom.
Qed.

Instance biasGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(gameA : game A N rty)
        `(scalarA : ScalarAxiomClass rty)
  : @game (biasType scalar_val A) N rty 
          (@biasCostInstance N rty A scalar_val _)
          (@biasCostAxiomInstance N rty A _ _ _ _).

Module BiasGameTest. Section biasGameTest.
  Context {A N rty} `{gameA : game A N rty} `{scalarA : ScalarAxiomClass rty}.
  Variables (t : {ffun 'I_N -> biasType scalar_val A}) (i : 'I_N).
  Check cost i t.
End biasGameTest. End BiasGameTest.

Instance biasLambdaInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (biasType scalar_val A) rty | 0 := lambda of A.

Program Instance biasLambdaAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (biasType scalar_val A) rty _ | 0.

Instance biasMuInstance
         (rty : realFieldType) (A : finType)
         `(scalarA : ScalarClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (biasType scalar_val A) rty | 0 := mu of A.

Program Instance biasMuAxiomInstance
        (rty : realFieldType) (A : finType)
        `(scalarA : ScalarAxiomClass rty)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (biasType scalar_val A) rty _ | 0.
                                          
Class LambdaMuGe1Class (A : finType) N (rty : realFieldType) `(smooth A N rty)
  : Type := lambdaMu_ge1 : 1 <= lambda of A + mu of A.

Program Instance biasSmoothAxiomInstance {A N rty}
        `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)  
        `{scalarA : ScalarAxiomClass rty}
  : @SmoothnessAxiomClass (biasType scalar_val A) N rty _ _ _ _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /biasCostInstance.
  rewrite /lambda_val /biasLambdaInstance.
  rewrite /mu_val /biasMuInstance.
  rewrite big_split /= !big_distrr /= -2!mulr_sumr 2!big_split /= 2!mulrDr.
  rewrite addrA [lambda of A * _ + _]addrC.
  rewrite -[(lambda of A * _ + _) + _]addrA.
  rewrite [lambda of A * _ + _]addrC.
  rewrite -[(lambda of A * _ + _) + _ + _]addrA; apply: ler_add.
  { rewrite -mulrDl; apply: ler_pemull.
    by apply: sumr_ge0=> _ _; apply: ltrW; apply: scalar_axiom.
    by apply: lambdaMu_ge1. }
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smooth_ax.
Qed.

Instance biasSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)
         `{scalarA : ScalarAxiomClass rty}
  : @smooth (biasType scalar_val A) N rty _ _ _ _ _ _ _ _.

Module BiasSmoothTest. Section biasSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{scalarA : ScalarAxiomClass rty}.
  Context (LambdaMu_ge1 : LambdaMuGe1Class gameA).
  Lemma x0 (t : {ffun 'I_N -> (biasType scalar_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (biasType scalar_val A)}) (i : 'I_N) :
    cost i t == lambda of (biasType scalar_val A). Abort.
End biasSmoothTest. End BiasSmoothTest.

(** Unit Games c(s) = 0 *)

Section UnitType.
Variable rty : realFieldType.
  
Inductive Unit : Type := mkUnit : Unit.

Definition Unit_eq (s1 s2 : Unit) : bool := true.

Lemma Unit_eqP : Equality.axiom Unit_eq.
Proof. by case; case; constructor. Qed.
  
Definition Unit_eqMixin := EqMixin Unit_eqP.
Canonical Unit_eqType := Eval hnf in EqType Unit Unit_eqMixin.

Definition bool_of_unit (u : Unit) : bool := true.
Definition unit_of_bool (b : bool) : Unit := mkUnit.
Lemma bool_of_unitK : cancel bool_of_unit unit_of_bool.
Proof. by case. Qed.

Definition unit_choiceMixin := CanChoiceMixin bool_of_unitK.
Canonical unit_choiceType :=
  Eval hnf in ChoiceType Unit unit_choiceMixin.
Definition unit_countMixin := CanCountMixin bool_of_unitK.
Canonical unit_countType :=
  Eval hnf in CountType Unit unit_countMixin.

Definition unit_enum := [:: mkUnit].
Lemma unit_enumP : Finite.axiom unit_enum.
Proof. by case. Qed.
Definition unit_finMixin := Eval hnf in FinMixin unit_enumP.
Canonical unit_finType := Eval hnf in FinType Unit unit_finMixin.

Definition unitTy := Wrapper [eqType of Unit] [finType of Unit].
Definition unitType := [finType of unitTy].
End UnitType.

Instance unitCostInstance
         (N : nat) (rty : realFieldType)
  : CostClass N rty unitType :=
  fun (i : 'I_N) (f : {ffun 'I_N -> unitType}) => 0.

Program Instance  unitCostAxiomInstance
        (N : nat) (rty : realFieldType)
  : @CostAxiomClass N rty unitType (@unitCostInstance N rty).

Program Instance unitGameInstance
        (N : nat) (rty : realFieldType) 
  : @game unitType N rty 
          (@unitCostInstance N rty)
          (@unitCostAxiomInstance N rty).

Module UnitGameTest. Section unitGameTest.
  Context {N rty} `{gameA : game unitType N rty}.
  Variables (t : {ffun 'I_N -> unitType}) (i : 'I_N).
  Check cost i t.
End unitGameTest. End UnitGameTest.

Instance unitLambdaInstance
         (rty : realFieldType) 
  : @LambdaClass unitType rty | 0 := 1.

Program Instance unitLambdaAxiomInstance
        (rty : realFieldType) 
  : @LambdaAxiomClass unitType rty _ | 0.
Next Obligation. by apply: ler01. Qed.

Instance unitMuInstance
         (rty : realFieldType)
  : @MuClass unitType rty | 0 := 0.

Program Instance unitMuAxiomInstance
        (rty : realFieldType)
  : @MuAxiomClass unitType rty _ | 0.
Next Obligation.
  apply/andP; split; first by apply: lerr.
  by apply: ltr01.
Qed.
                                          
Program Instance unitSmoothAxiomInstance {N rty}
  : @SmoothnessAxiomClass unitType N rty _ _ _ _ _ _ _.
Next Obligation.
  rewrite mul1r mul0r addr0; have ->: t = t'.
  { apply/ffunP; case => m i. case: (t _)=> s. case: (t' _)=> s'.
    by f_equal; case: s; case: s'. }
  by [].
Qed.

Instance unitSmoothInstance {N rty}
  : @smooth unitType N rty _ _ _ _ _ _ _ _.

Module UnitSmoothTest. Section unitSmoothTest.
  Context {N rty} `{gameA : smooth unitType N rty}.
  Lemma x0 (t : {ffun 'I_N -> unitType}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> unitType}) (i : 'I_N) :
    cost i t == lambda of unitType. Abort.
End unitSmoothTest. End UnitSmoothTest.

(** Unit Games are compilable *)

Section unitCompilable.
  Variable (N : OrdNat.t).

  Instance unitCTypeInstance : CType unitType :=
    [:: Wrap [eqType of Unit] mkUnit].

  Program Instance unitRefineTypeAxiomInstance
    : @RefineTypeAxiomClass unitType _.
  Next Obligation. by split => // r; rewrite mem_enum; case: r. Qed.

  Instance unitRefineTypeInstance
    : @RefineTypeClass unitType  _ _.

  Definition unit_ccost (i : OrdNat.t) (m : M.t unitTy) : Qcoq :=
    0%coq_Qscope.

  Instance unitCCostInstance : CCostClass unitType
    := unit_ccost.

  Program Instance unitRefineCostAxiomInstance :
    @RefineCostAxiomClass N unitType _ _.

  Instance unitRefineCostInstance
    : @RefineCostClass N unitType _ _ _.

  Instance unit_cgame 
    : cgame (N:=N) (T:=unitType) _ _ _.

End unitCompilable.

(** Affine Games: C(x) = ax + b, 0 <= a, 0 <= b *)

Section AffineGame.
Variable rty : realFieldType.
Context `(scalarA : ScalarClass rty) `(@ScalarAxiomClass _ scalarA).
Context `(scalarB : ScalarClass rty) `(@ScalarAxiomClass _ scalarB).

Variables (A : finType) (N : nat).
Context `(Boolable A).
Context `(game A N rty).

Definition affineType : Type :=
  scalarType (@scalar_val _ scalarA) A *
  scalarType (@scalar_val _ scalarB) (singletonType A).

Section affineGameTest.
Variable t : {ffun 'I_N -> affineType}.
Variable i : 'I_N.
Check cost i t.
End affineGameTest.
End AffineGame.
