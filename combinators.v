Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import strings.
Require Import extrema dist numerics bigops.
Require Import games compile smooth christodoulou.

Local Open Scope ring_scope.

(** This module defines combinators over multiplayer games. *)

(** A generic wrapper for directing the construction of cost games
    over finite types [T]. [I] is a phantom type, used to direct
    instance resolution. *)
Inductive Wrapper (I : Type) (T : Type) : Type :=
  Wrap : T -> Wrapper I T.
Definition unwrap (I : Type) (T : Type) (w : Wrapper I T) : T :=
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

(******************************************
  Resource Games 
 ******************************************)

Inductive resource : Type :=
| RYes : resource
| RNo : resource.

Definition string_of_resource (r : resource) : string :=
  match r with
  | RYes => "RYes"
  | RNo => "RNo"
  end.

Instance resourceShowable : Showable resource :=
  mkShowable string_of_resource.

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

  Lemma traffic_max (f : {ffun 'I_N -> [finType of resource]}) :
    (traffic f <= N)%N.
  Proof.
    rewrite -[N]card_ord -sum1_card trafficP /traffic' big_mkcond /=.
    apply leq_sum=> i H1; case: (f i) => //.
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

Instance resourceCostMaxInstance (N : nat)
  : CostMaxClass N rat_realFieldType resource := N%:R.

Program Instance resourceCostMaxAxiomInstance (N : nat)
  : CostMaxAxiomClass (@resourceCostInstance N)
      (resourceCostMaxInstance N).
Next Obligation.
  rewrite /cost_fun /resourceCostInstance /resourceCostFun.
  rewrite /costmax_fun /resourceCostMaxInstance.
  case: (s i); last by apply ler0n.
  move: (traffic_max s) => H. rewrite -(ler_nat rat_numDomainType) in H.
  assumption.
Qed.

Instance resourceGame (N : nat) : @game [finType of resource] N _ _ _ _
                                      (resourceCostMaxAxiomInstance _).

(******************************************
  Resource Games are (5/3, 1/3)-Smooth
 ******************************************)

Instance resourceLambdaInstance 
  : @LambdaClass resource rat_realFieldType| 0 := 5%:R/3%:R.

Program Instance resourceLambdaAxiomInstance
  : @LambdaAxiomClass resource rat_realFieldType _.

Instance resourceMuInstance
  : MuClass resource rat_realFieldType | 0 := 1%:R/3%:R.

Instance resourceMuAxiomInstance
  : @MuAxiomClass resource rat_realFieldType _.
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
  lambda of resource * Cost t' +
  mu of resource * Cost t.
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
  : @SmoothnessAxiomClass [finType of resource] N rat_realFieldType _ _ _
                          (resourceCostMaxAxiomInstance _) _ _ _ _.
Next Obligation. by apply: resourceSmoothnessAxiom. Qed.
Instance resourceSmoothInstance N
  : @smooth [finType of resource] N rat_realFieldType _ _ _
            (resourceCostMaxAxiomInstance _) _ _ _ _ _.

(******************************************
  Resource Games are Boolable
 ******************************************)

Instance boolable_Resource : Boolable resource :=
  fun r => match r with RYes => true | RNo => false end.

Instance boolableUnit_Resource :
  @BoolableUnit resource boolable_Resource := RNo.

Program Instance boolableUnitAxiom_Resource :
  @BoolableUnitAxiom _ _ boolableUnit_Resource.

Instance eqResource : Eq resource := eq.

Instance eqDecResource : Eq_Dec eqResource.
Proof.
  move => x y.
  case:(eqVneq x y) => H;
  [left | right] => //.
  move/eqP: H => //.
Qed.

Instance eqReflResource : Eq_Refl eqResource.
Proof.
  rewrite /Eq_Refl /eqResource. move => x //.
Qed.

(******************************************
  Singleton Games A : Boolable, 
  c_i s =  if (boolify s_i) then 1 else 0
 ******************************************)

Section SingletonType.

Variable rty : realFieldType.
  
Inductive Singleton : Type := mkSingleton : Singleton.

Definition Singleton_eq (s1 s2 : Singleton) : bool := true.

Lemma Singleton_eqP : Equality.axiom Singleton_eq.
Proof. by case; case; constructor. Qed.
  
Definition Singleton_eqMixin := EqMixin Singleton_eqP.
Canonical Singleton_eqType := Eval hnf in EqType Singleton Singleton_eqMixin.

Definition singleton (A : Type) :=
  Wrapper Singleton A.

Definition singletonType (A : finType) :=
  [finType of Wrapper [eqType of Singleton] A].
End SingletonType.

Global Instance BoolableSingleton (A : Type) `(Boolable A)
  : Boolable (singleton A) :=
  fun (s : singleton A) => boolify (unwrap s).

Global Instance BoolableUnitSingleton (A : Type) `(bA : BoolableUnit A)
  : (BoolableUnit (BoolableSingleton _)) :=  (Wrap Singleton bA).

Global Program Instance BoolableUnitSingletonAxiom
        (A: Type) `(bA : BoolableUnitAxiom A)
  : @BoolableUnitAxiom _ _ (BoolableUnitSingleton A _).

Program Instance eqSingleton (A : Type) (eqA : Eq A) : Eq (singleton A) :=
  fun a b => 
    eqA (unwrap a) (unwrap b).

Program Instance eqDecSingleton
                  (A : Type) (eqA : Eq A)
                  (eqDecA : Eq_Dec eqA) : Eq_Dec (@eqSingleton A eqA).
Next Obligation.
  case: x => x; case: y => y.
  rewrite /eqSingleton => //.
Qed.

Program Instance eqReflSingleton
                  (A : Type) (eqA : Eq A)
                  (eqReflA : Eq_Refl eqA) : Eq_Refl (@eqSingleton A eqA).
Next Obligation.
  rewrite /Eq_Refl /eqSingleton. case: x => //.
Qed.

Instance singletonCostInstance
         (N : nat) (A : finType)
         `(boolableA : Boolable A)
  : CostClass N rat_realFieldType (singletonType A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> singletonType A}) =>
    if boolify (f i) then 1 else 0.

Program Instance  singletonCostAxiomInstance
        (N : nat) (A : finType)
        `(boolableA : Boolable A)        
  : @CostAxiomClass
      N rat_realFieldType
      (singletonType A)
      (@singletonCostInstance N _ _).
Next Obligation.
  rewrite /(cost) /singletonCostInstance; case: (boolify _); first by apply: ler01.
  by apply: lerr.
Qed.

Instance singletonCostMaxInstance (N : nat) (A : finType)
  : CostMaxClass N rat_realFieldType (singleton A) :=
  1.

Program Instance singletonCostMaxAxiomInstance
        (N : nat) (A : finType)
        `(boolableA : Boolable A)
  : CostMaxAxiomClass (@singletonCostInstance N A _)
                      (singletonCostMaxInstance N  A).
Next Obligation.
  rewrite /cost_fun /singletonCostInstance.
  rewrite /costmax_fun /singletonCostMaxInstance.
  case: (boolify (s i)) => //.
Qed.

(*Uses the generic move instance for wrapped types*)

Instance singletonGameInstance
        (N : nat) (A : finType)
        `(boolableA :Boolable A) 
  : @game (singletonType A) N rat_realFieldType _ _ _
          (singletonCostMaxAxiomInstance _ _ _).

Module SingletonGameTest. Section singletonGameTest.
  Context {A : finType} {N : nat}  `{Boolable A}.
  Variables (t : {ffun 'I_N -> singletonType A}) (i : 'I_N).
  Check cost i t.
End singletonGameTest. End SingletonGameTest.

Instance singletonLambdaInstance (A : Type)
  : @LambdaClass (singleton A) rat_realFieldType| 0 := 5%:R/3%:R.

Program Instance singletonLambdaAxiomInstance
        (A : Type)
  : @LambdaAxiomClass (singleton A) _ _.

Instance singletonMuInstance
         (A : Type)
  : @MuClass (singleton A) rat_realFieldType| 0 := 1%:R/3%:R.

Instance singletonMuAxiomInstance
        (A : Type)
  : @MuAxiomClass (singleton A) _ _.
Proof. by []. Qed.

Program Instance singletonSmoothAxiomInstance
          {A : finType} {N}
         `{boolableA : Boolable A}
  : @SmoothnessAxiomClass (singletonType A) N _ (singletonCostInstance _)
                          (singletonCostAxiomInstance _ _ _)
                          _ (singletonCostMaxAxiomInstance _ _ _) 
                          _ (singletonLambdaAxiomInstance A)
                          _ (singletonMuAxiomInstance A).
Next Obligation.
  rewrite /Cost /(cost) /singletonCostInstance.
  rewrite /lambda_val /singletonLambdaInstance.
  rewrite /mu_val /singletonMuInstance.
  have ->:
   \sum_(i < N)
      (if boolify ([ffun j => if i == j then t' j else t j] i) then 1 else 0) =
   \sum_(i < N) (if boolify (t' i) then 1 else (0 : rat_realFieldType)).
  { by apply/congr_big => // i _; rewrite ffunE eq_refl. }
  rewrite -[\sum_i (if boolify (t' i) then 1 else 0)]addr0; apply: ler_add.
  rewrite addr0; apply: ler_pemull=> //.
  apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
  apply: mulr_ge0; first by apply: (mu_pos (T:=singleton A)).
  apply: sumr_ge0 => // i _; case: (boolify _) => //; apply: ler01.
Qed.  

Instance singletonSmoothInstance {A : finType} {N}
         `{boolableA : Boolable A}
  : @smooth (singletonType A) N _ _ _ _
            (singletonCostMaxAxiomInstance _ _ _)
            _ _ _ _ _.

Module SingletonSmoothTest. Section singletonSmoothTest.
  Context {A : finType} {N : nat} `{Boolable A}.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (singletonType A)}) (i : 'I_N) :
    cost i t == lambda of (singletonType A). Abort.
End singletonSmoothTest. End SingletonSmoothTest.

(**********************************************
  Sigma Games {x : A | P x}, with P : A -> bool
 **********************************************)

Class PredClass (A : Type) := the_pred : A -> bool.

Class PredClassPreservesBoolableUnit
        (A : Type) `(Boolable A) `(P : PredClass A)
        (bA : @BoolableUnit A _)
  := unitPreserved : P bA = true.

Instance SigmaBoolableInstance
         A (B : Boolable A) (P : PredClass A)
  : Boolable {x : A | the_pred x} :=
  fun p => boolify (projT1 p).

(* We need to ensure that our BoolableUnit surives P *)
Instance BoolableUnitSigma
        A `(Boolable A) `(bA : @BoolableUnit A _)
        `(P : PredClass A) `(pf : @PredClassPreservesBoolableUnit A _ _ bA)
  : BoolableUnit (@SigmaBoolableInstance A _ _) :=
  (exist _ bA pf).

Program Instance BoolableUnitSigmaAxiom 
        A `(Boolable A) `(bA : @BoolableUnit A _)
        `(@BoolableUnitAxiom _ _ bA) 
        `(P : PredClass A) (pf : @PredClassPreservesBoolableUnit A _ _ bA)
  : @BoolableUnitAxiom _ _ (BoolableUnitSigma pf).

Program Instance eqSigma (A : Type) (eqA : Eq A) (P : PredClass A)
  : Eq {x : A | P x} :=
    fun a b => 
      eqA (proj1_sig a) (proj1_sig b).

Program Instance eqSigmaDec
                  (A : Type) (eqA : Eq A)
                  (eqDecA : Eq_Dec eqA)
                  (P : PredClass A)
  : Eq_Dec (@eqSigma _ eqA P).
Next Obligation.
  rewrite /eqSigma => //.
Qed.

Program Instance eqSigmaRefl
                  (A : Type) (eqA : Eq A)
                  (eqReflA : Eq_Refl eqA)
                  (P : PredClass A)
  : Eq_Refl (@eqSigma _ eqA P).
Next Obligation.
  rewrite /eqSigma => //.
Qed.

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

Instance sigmaCostMaxInstance (N : nat) (rty : realFieldType) (A : Type)
         (predInstance : PredClass A)
         (costMaxInstance : CostMaxClass N rty A)
  : CostMaxClass N rty {x : A | the_pred x} :=
  costmax_fun.

Program Instance sigmaCostMaxAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(predInstance : PredClass A)
        `(costA : CostClass N rty A)
        `(costMaxInstance : CostMaxClass N rty A)
        `(costMaxAxiomInstance : @CostMaxAxiomClass N rty A costA costMaxInstance)
  : CostMaxAxiomClass (@sigmaCostInstance N rty A predInstance costA)
                      (sigmaCostMaxInstance predInstance costMaxInstance) := _.
Next Obligation.
  move => x s; rewrite /(cost) /sigmaCostInstance.
  apply: costMaxAxiom_fun.
Qed.  

Instance sigmaGameInstance
         (N : nat) (rty : realFieldType) (A : finType)
         (predInstance : PredClass A)                 
         `(gameA : game A N rty)
  : @game [finType of {x : A | the_pred x}] _ _ _ _ _ _.

Module SigmaGameTest. Section sigmaGameTest.
  Context {A : finType} {N rty} (predA : PredClass A) `{gameA : game A N rty}.
  Variables (t : {ffun 'I_N -> {x : A | the_pred x}}) (i : 'I_N).
  Check cost i t.
End sigmaGameTest. End SigmaGameTest.

Instance sigmaLambdaInstance
         (rty : realFieldType) (A : Type)
         `(lambdaA : LambdaClass A rty)
         (predInstance : PredClass A)
  : @LambdaClass {x : A | the_pred x} rty | 0 :=
  lambda of A.

Program Instance sigmaLambdaAxiomInstance
        (rty : realFieldType) (A : Type)
        `(lambdaA : LambdaClass A rty)
        `(lambdaAxiomA : @LambdaAxiomClass A rty lambdaA)
        `(predInstance : PredClass A)        
  : @LambdaAxiomClass
      {x : A | the_pred x}
      rty
      (@sigmaLambdaInstance rty A lambdaA predInstance)
  := _.

Instance sigmaMuInstance
         (rty : realFieldType) (A : Type)
         `(muA : MuClass A rty)
         (predInstance : PredClass A)
  : @MuClass {x : A | the_pred x} rty | 0 :=
  mu of A.

Program Instance sigmaMuAxiomInstance
        (rty : realFieldType) (A : Type)
        `(muA : MuClass A rty)
        `(muAxiomA : @MuAxiomClass A rty muA)
        `(predInstance : PredClass A)        
  : @MuAxiomClass
      {x : A | the_pred x}
      rty
      (@sigmaMuInstance rty A muA predInstance)
  := _.

Lemma sigmaSmoothnessAxiom
      (N : nat) (rty : realFieldType) (A : finType)
      (predInstance : PredClass A)
      `{smoothA : smooth A N rty}
      (t t' : {ffun 'I_N -> {x : A | the_pred x}}) :
  \sum_(i : 'I_N) cost i (upd i t t') <=
  lambda of {x : A | the_pred x} * Cost t' +
  mu of {x : A | the_pred x} * Cost t.
Proof.
  rewrite /Cost /cost_fun /sigmaCostInstance /cost_fun.
  have ->: (lambda of [finType of {x : A | the_pred x}] = lambda of A) by [].
  have ->: (mu of [finType of {x : A | the_pred x}] = mu of A) by [].
  have ->: (\sum_(i < N) costClass i [ffun j => projT1 (upd i t t' j)] =
            \sum_(i < N) costClass i
             (upd i [ffun j => projT1 (t j)] [ffun j => projT1 (t' j)])).
  { apply congr_big => // i _. f_equal. apply ffunP => x /=.
    rewrite !ffunE. case: (i == x) => //. }
  apply (smoothness_axiom _).
Qed.

Program Instance sigmaSmoothAxiomInstance
      (N : nat) (rty : realFieldType) (A : finType)
      `(predInstance : PredClass A)
      `{smoothA : smooth A N rty}
  : @SmoothnessAxiomClass
      [finType of {x : A | the_pred x}]
      N _
      (sigmaCostInstance _)
      (sigmaCostAxiomInstance _ _ _ _ _)
      _ (sigmaCostMaxAxiomInstance _ _ _ _ _ _ _) 
      _ (sigmaLambdaAxiomInstance _ A _ _ _)
      _ (sigmaMuAxiomInstance _ A _ _ _).
Next Obligation. apply: sigmaSmoothnessAxiom. Qed.

Instance sigmaSmoothInstance
      (N : nat) (rty : realFieldType) (A : finType)
      `(predInstance : PredClass A)
      `{smoothA : smooth A N rty}
  : @smooth
      [finType of {x : A | the_pred x}]
      N
      rty
      _ _ _ _ _ _ _ _ 
      (sigmaSmoothAxiomInstance _ _ _ _).
      
Module SigmaSmoothTest. Section sigmaSmoothTest.
  Context (N : nat) (rty : realFieldType) (A : finType)
          `(predInstance : PredClass A)
          `{smoothA : smooth A N rty}.
  Definition t := {x : A | the_pred x}.
  Lemma x0 (t : {ffun 'I_N -> t}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (x : {ffun 'I_N -> t}) (i : 'I_N) :
    cost i x == lambda of t. Abort.
End sigmaSmoothTest. End SigmaSmoothTest.

(**********************************************
  Product Games A * B 
 **********************************************)

Instance prodBoolableInstance
         (A B : Type) (bA : Boolable A) (bB : Boolable B)
  : Boolable (A*B) :=
      fun ab => boolify (fst ab) && boolify (snd ab).

Instance prodBoolableUnit
         (A B : Type) `(bA : BoolableUnit A) `(bB : BoolableUnit B)
  : BoolableUnit (@prodBoolableInstance A B _ _) :=
      (bA, bB).

Program Instance prodBoolableUnitAxiom
          (A B : Type)
          `(bA : BoolableUnit A)
          (bAa : BoolableUnitAxiom bA)
          `(bB : BoolableUnit B)
          (bBa : BoolableUnitAxiom bB)
  : BoolableUnitAxiom (prodBoolableUnit A B bA bB).
Next Obligation.
  rewrite /prodBoolableInstance !/boolify bAa bBa => //.
Qed.

Instance eqProd
      (A B: Type) (eqA : Eq A) (eqB : Eq B)
  : Eq (A*B)%type :=
    fun p1 p2 =>
    match p1, p2 with
    | (a1, b1), (a2, b2) => (eqA a1 a2) /\ (eqB b1 b2)
    end. 

Program Instance eqProdDec
      (A B : Type) (eqA : Eq A) (eqB : Eq B)
      (eqDecA : Eq_Dec eqA) (eqDecB : Eq_Dec eqB)
  : Eq_Dec (@eqProd _ _ eqA eqB).
Next Obligation.
  rewrite /eqProd.
  case: (eqDecA a0 a);
  case: (eqDecB b0 b) => H0 H1;
  [left | right | right | right] => // => H;
  [apply H0 | apply H1 | apply H1]; apply H.
Qed.

Program Instance eqProdRefl
      (A B : Type) (eqA : Eq A) (eqB : Eq B)
      (eqReflA : Eq_Refl eqA) (eqReflB : Eq_Refl eqB)
  : Eq_Refl (@eqProd _ _ eqA eqB).
Next Obligation.
  rewrite /eqProd; split.
  apply eqReflA. apply eqReflB.
Qed.

Instance prodCostInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         (costA : CostClass N rty aT)
         (costB : CostClass N rty bT)         
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

Instance prodCostMaxInstance (N : nat) (rty : realFieldType) (aT bT : Type)
         (costMaxA : CostMaxClass N rty aT)
         (costMaxB : CostMaxClass N rty bT)
  : CostMaxClass N rty (aT*bT).
Proof. apply GRing.add. apply costMaxA. apply costMaxB. Defined.

Program Instance prodCostMaxAxiomInstance
        (N : nat) (rty : realFieldType) (aT bT : finType)
        (costA : CostClass N rty aT)
        (costB : CostClass N rty bT) 
        (costMaxA : CostMaxClass N rty aT)
        (costMaxB : CostMaxClass N rty bT)
        (costMaxAxiomA : CostMaxAxiomClass costA _)
        (costMaxAxiomB : CostMaxAxiomClass costB _)
  : CostMaxAxiomClass (@prodCostInstance N rty aT bT _ _)
                      (prodCostMaxInstance _ _).
Next Obligation. by apply ler_add. Qed.

Instance prodGameInstance
         (N : nat) (rty : realFieldType) (aT bT : finType)
         `(gameA : game aT N rty)
         `(gameB : game bT N rty) 
  : @game [finType of aT*bT] _ _ _ _ _ _.

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
         (rty : realFieldType) (aT bT : Type)
         `(lambdaA : LambdaClass aT rty)
         `(lambdaB : LambdaClass bT rty)  
  : @LambdaClass (aT*bT) rty | 0 :=
  maxr (lambda of aT) (lambda of bT).

Program Instance prodLambdaAxiomInstance
         (rty : realFieldType) (aT bT : Type)
         `(lambdaA : LambdaAxiomClass aT rty)
         `(lambdaB : LambdaAxiomClass bT rty)
  : @LambdaAxiomClass (aT*bT) rty _.
Next Obligation.
  rewrite /lambda_val /prodLambdaInstance.
  rewrite ler_maxr.
  apply/orP.
  left.
  apply: lambda_pos.
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
         (rty : realFieldType) (aT bT : Type)
         `(muA : MuClass aT rty)
         `(muB : MuClass bT rty)
  : @MuClass (aT*bT) rty | 0 :=
  maxr (mu of aT) (mu of bT).

Program Instance prodMuAxiomInstance
        (rty : realFieldType) (aT bT : Type)
        `(muA : MuAxiomClass aT rty)
        `(muB : MuAxiomClass bT rty)
  : @MuAxiomClass (aT*bT) rty _ | 0.
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
    (smoothness_axiom _ _)).
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
    (smoothness_axiom _ _)).
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
  : @SmoothnessAxiomClass [finType of (aT*bT)] N rty _ _ _ _ _ _ _ _ 
  := prodSmoothnessAxiom.

Instance prodSmoothInstance {aT bT N rty}
         `{smoothA : smooth aT N rty}
         `{smoothB : smooth bT N rty}
  : @smooth [finType of (aT*bT)] N rty _ _ _ _ _ _ _ _ _.

Module ProdSmoothTest. Section prodSmoothTest.
  Context {A B N rty} `{gameA : smooth A N rty} `{gameB : smooth B N rty}.
  Lemma x0 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t == 0. Abort.
  Lemma x1 (t : {ffun 'I_N -> A*B}) (i : 'I_N) : cost i t <= lambda of A. Abort.
  Lemma x2 (t : {ffun 'I_N -> A*B}) (i : 'I_N) :
    mu of [finType of A * B] == lambda of [finType of A * B]. Abort.
End prodSmoothTest. End ProdSmoothTest.

(*************************************
 Scalar Games c * A 
 *************************************)

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

Definition scalar (c : rty) (A : Type) :=
  Wrapper (Scalar c) A.

Definition scalarType (c : rty) (A : finType) :=
  [finType of Wrapper (Scalar c) A].

Global Instance BoolableScalar (c : rty) (A : Type) `(Boolable A)
  : Boolable (scalar c A) :=
  fun (s : scalar c A) => boolify (unwrap s).

Global Instance BoolableUnitScalar (c : rty) (A : Type) `(bA : BoolableUnit A) :
  BoolableUnit (@BoolableScalar c A _) := (Wrap (Scalar c) bA).

Global Program Instance BoolableUnitScalarAxiom
  (c : rty) (A : Type) `(bA : BoolableUnit A) `(bAax : @BoolableUnitAxiom _ _ bA) :
  @BoolableUnitAxiom _ _ (BoolableUnitScalar c A bA).

Global Instance eqScalar
      (c : rty) (A : Type) (eqA : Eq A)
  : Eq (scalar c A) :=
    fun a1 a2 =>
    (eqA (unwrap a1) (unwrap a2)). 

Global Program Instance eqScalarDec
      (c : rty) (A : Type) (eqA : Eq A)
      (eqDecA : Eq_Dec eqA)
  : Eq_Dec (@eqScalar c _  eqA).
Next Obligation.
  rewrite /eqScalar.
  case: x => x; case: y => y //.
Qed.

Global Program Instance eqScalarRefl
      (c : rty) (A : Type) (eqA : Eq A)
      (eqReflA : Eq_Refl eqA)
  : Eq_Refl (@eqScalar c _  eqA).
Next Obligation.
  rewrite /eqScalar.
  case: x => x  //.
Qed.
End ScalarType.

Class ScalarClass (rty : realFieldType)
  : Type := scalar_val : rty.

Class DyadicScalarClass 
  : Type := dyadic_scalar_val : dyadic_rat.

Instance DyadicScalarInstance `(DyadicScalarClass)
  : ScalarClass [realFieldType of rat] :=
  dyadic_scalar_val.  

Class ScalarAxiomClass (rty : realFieldType)
      `(ScalarClass rty)
  : Type := scalar_axiom : 0 <= scalar_val.

Global Instance scalarCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(costA : CostClass N rty A)
         `(scalarA : ScalarClass rty)
  : CostClass N rty (scalarType scalar_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> scalarType scalar_val A}) =>
    scalar_val * cost i (unwrap_ffun f).

Program Instance scalarCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(costA : CostAxiomClass N rty A)
        `(scalarA : ScalarAxiomClass rty)
  : @CostAxiomClass
      N rty
      (scalarType scalar_val A)
      (@scalarCostInstance N rty _ _ _).
Next Obligation.
  rewrite /(cost) /scalarCostInstance mulr_ge0=> //.
Qed.

Instance scalarCostMaxInstance (N : nat) (rty : realFieldType) (A : Type)
         (costMax : CostMaxClass N rty A)
         (scalarA : ScalarClass rty)
  : CostMaxClass N rty (scalar scalar_val A) :=
  scalar_val * costmax_fun.

Program Instance scalarCostMaxAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        (costInstance : CostClass N rty A)
        (costAxiomInstance : CostAxiomClass costInstance)
        (costMaxInstance : CostMaxClass N rty A)
        (costMaxAxiomInstance : CostMaxAxiomClass costInstance _)
        (scalarInstance : ScalarClass rty)
        (scalarAxiomInstance : ScalarAxiomClass _)
  : CostMaxAxiomClass (@scalarCostInstance N rty A _ _) (scalarCostMaxInstance costMaxInstance _).
Next Obligation. by apply ler_pmul => //; apply ltrW => //. Qed.

Global Instance scalarGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(ScalarAxiomClass rty) 
        `(gameA : game A N rty)
  : @game (scalarType scalar_val A) N rty 
          (@scalarCostInstance N rty A _ _)
          (@scalarCostAxiomInstance N rty A _ _ _ _) _
          (scalarCostMaxAxiomInstance _ _ _ _ _ _ _ _ _).

Module ScalarGameTest. Section scalarGameTest.
  Context {A N rty} `{gameA : game A N rty} `{scalarA : ScalarAxiomClass rty}.
  Variables (t : {ffun 'I_N -> scalarType scalar_val A}) (i : 'I_N).
  Check cost i t.
End scalarGameTest. End ScalarGameTest.

Instance scalarLambdaInstance
         (rty : realFieldType) (A : Type)
         `(scalarA : ScalarClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (scalar scalar_val A) rty | 0 := lambda of A.

Instance scalarLambdaAxiomInstance
         (rty : realFieldType) (A : Type)
        `(scalarA : ScalarClass rty)         
        `(scalarAxiomA : @ScalarAxiomClass rty scalarA)
        `(lambdaA : LambdaClass A rty)
        `(lambdaAxiomA : @LambdaAxiomClass A rty lambdaA)
  : @LambdaAxiomClass
      (scalar scalar_val A)
      rty
      (scalarLambdaInstance scalarA lambdaA) | 0
  := @lambda_axiom A rty lambdaA lambdaAxiomA.

Instance scalarMuInstance
         (rty : realFieldType) (A : Type)
         `(scalarA : ScalarClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (scalar scalar_val A) rty | 0 := mu of A.

Instance scalarMuAxiomInstance
        (rty : realFieldType) (A : Type)
        `(scalarA : ScalarAxiomClass rty)
        `(muA : MuClass A rty)        
        `(muAxiomA : @MuAxiomClass A rty muA)
  : @MuAxiomClass (scalar scalar_val A) rty _ | 0
  := @mu_axiom A rty muA muAxiomA.

Program Instance scalarSmoothAxiomInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @SmoothnessAxiomClass (scalarType scalar_val A) N rty _ _ _
                          (scalarCostMaxAxiomInstance _ _ _ _ _ _ _ _ _)
                          _ _ _ _.
Next Obligation.
  rewrite /Cost /(cost) /scalarCostInstance.
  rewrite /lambda_val /scalarLambdaInstance.
  rewrite /mu_val /scalarMuInstance.
  rewrite -3!mulr_sumr.
  rewrite mulrA [lambda of A * _]mulrC -mulrA.
  rewrite [mu of A * _]mulrA [mu of A * _]mulrC -mulrA.
  rewrite -mulrDr. apply: ler_pmul => //. apply sumr_ge0 => //.
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smoothness_axiom.
Qed.

Instance scalarSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         `{scalarA : ScalarAxiomClass rty}
  : @smooth (scalarType scalar_val A) N rty _ _ _
            (scalarCostMaxAxiomInstance _ _ _ _ _ _ _ _ _)
            _ _ _ _ _.

Module ScalarSmoothTest. Section scalarSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{scalarA : ScalarAxiomClass rty}.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (scalarType scalar_val A)}) (i : 'I_N) :
    cost i t == lambda of (scalarType scalar_val A). Abort.
End scalarSmoothTest. End ScalarSmoothTest.

(*************************************
 Bias Games c + A 
 *************************************)

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

Definition bias (c : rty) (A : Type) :=
  Wrapper (Bias c) A.

Definition biasType (c : rty) (A : finType) :=
  [finType of Wrapper (Bias c) A].

Global Instance BoolableBias (c : rty) (A : Type) `(Boolable A)
  : Boolable (bias c A) :=
  fun (s : bias c A) => boolify (unwrap s).

Global Instance BoolableUnitBias (c : rty) (A : Type) `(bA : BoolableUnit A) :
  BoolableUnit (@BoolableBias c A _) := (Wrap (Bias c) bA).

Global Program Instance BoolableUnitBiasAxiom
  (c : rty) (A : Type) `(bA : BoolableUnit A) `(bAax : @BoolableUnitAxiom _ _ bA) :
  @BoolableUnitAxiom _ _ (BoolableUnitBias c A bA).

Global Instance eqBias
      (c : rty) (A : Type) (eqA : Eq A)
  : Eq (bias c A) :=
    fun a1 a2 =>
    (eqA (unwrap a1) (unwrap a2)). 

Program Instance eqBiasDec 
      (c : rty) (A : Type) (eqA : Eq A)
      (eqDecA : Eq_Dec eqA)
  : Eq_Dec (@eqBias c _  eqA).
Next Obligation.
  rewrite /eqBias.
  case: x => x; case: y => y //.
Qed.

Program Instance eqBiasRefl
      (c : rty) (A : Type) (eqA : Eq A)
      (eqReflA : Eq_Refl eqA)
  : Eq_Refl (@eqBias c _  eqA).
Next Obligation.
  rewrite /eqBias.
  case: x => x //.
Qed.

End BiasType.

Class BiasClass (rty : realFieldType)
  : Type := bias_val : rty.

Class BiasAxiomClass (rty : realFieldType)
      `(BiasClass rty)
  : Type := bias_axiom : 0 <= bias_val.

Instance biasCostInstance
         (N : nat) (rty : realFieldType) (A : finType)
         `(biasA : BiasClass rty)
         `(costA : CostClass N rty A)
  : CostClass N rty (biasType bias_val A) :=
  fun (i : 'I_N) (f : {ffun 'I_N -> biasType bias_val A}) =>
    bias_val + cost i (finfun (fun j => unwrap (f j))).

Program Instance biasCostAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(biasA : BiasAxiomClass rty)
        `(costA : CostAxiomClass N rty A)
  : @CostAxiomClass N rty (biasType scalar_val A)
                    (@biasCostInstance N rty _ bias_val _).
Next Obligation.
  rewrite /(cost) /biasCostInstance addr_ge0 => //.
Qed.

Instance biasCostMaxInstance (N : nat) (rty : realFieldType) (A : Type)
         (costMax : CostMaxClass N rty A)
         `(biasA : BiasAxiomClass rty)
  : CostMaxClass N rty (bias bias_val A) :=
  bias_val + costmax_fun.

Program Instance biasCostMaxAxiomInstance
        (N : nat) (rty : realFieldType) (A : finType)
        (costInstance : CostClass N rty A)
        (costAxiomInstance : CostAxiomClass costInstance)
        (costMaxInstance : CostMaxClass N rty A)
        (costMaxAxiomInstance : CostMaxAxiomClass costInstance _)
        `(biasA : BiasAxiomClass rty)
  : CostMaxAxiomClass (@biasCostInstance N rty A _ _)
                      (biasCostMaxInstance _ _ _ costMaxInstance _).
Next Obligation. by apply ler_add. Qed.

Instance biasGameInstance
        (N : nat) (rty : realFieldType) (A : finType)
        `(gameA : game A N rty)
        `(biasA : BiasAxiomClass rty)
  : @game (biasType bias_val A) N rty 
          (@biasCostInstance N rty A bias_val _)
          (@biasCostAxiomInstance N rty A _ _ _ _)
          _ (biasCostMaxAxiomInstance _ _ _ _ _ _ _ _).

Module BiasGameTest. Section biasGameTest.
  Context {A N rty} `{gameA : game A N rty} `{biasA : BiasAxiomClass rty}.
  Variables (t : {ffun 'I_N -> biasType bias_val A}) (i : 'I_N).
  Check cost i t.
End biasGameTest. End BiasGameTest.

Instance biasLambdaInstance
         (rty : realFieldType) (A : Type)
         `(biasA : BiasClass rty)
         `(lambdaA : LambdaClass A rty)
  : @LambdaClass (bias bias_val A) rty | 0 := lambda of A.

Program Instance biasLambdaAxiomInstance
        (rty : realFieldType) (A : Type)
        `(biasA : BiasAxiomClass rty)
        `(lambdaA : LambdaAxiomClass A rty)
  : @LambdaAxiomClass (bias bias_val A) rty _ | 0.

Instance biasMuInstance
         (rty : realFieldType) (A : Type)
         `(biasA : BiasClass rty)
         `(lambdaA : MuClass A rty)
  : @MuClass (bias bias_val A) rty | 0 := mu of A.

Program Instance biasMuAxiomInstance
        (rty : realFieldType) (A : Type)
        `(biasA : BiasAxiomClass rty)
        `(lambdaA : MuAxiomClass A rty)
  : @MuAxiomClass (bias bias_val A) rty _ | 0.
                                          
Class LambdaMuGe1Class (A : finType) N (rty : realFieldType) `(smooth A N rty)
  : Type := lambdaMu_ge1 : 1 <= lambda of A + mu of A.

Program Instance biasSmoothAxiomInstance {A N rty}
        `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)  
        `{biasA : BiasAxiomClass rty}
  : @SmoothnessAxiomClass (biasType bias_val A) N rty _ _ _
                          (biasCostMaxAxiomInstance _ _ _ _ _ _ _ _)
                          _ _ _ _.
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
    by apply: sumr_ge0=> _ _; apply: bias_axiom.
    by apply: lambdaMu_ge1. }
  by rewrite unwrap_ffun_simpl unwrap_eta; apply: smoothness_axiom.
Qed.

Instance biasSmoothInstance {A N rty}
         `{smoothA : smooth A N rty}
         (LambdaMu_ge1 : LambdaMuGe1Class smoothA)
         `{biasA : BiasAxiomClass rty}
  : @smooth (biasType bias_val A) N rty _ _ _
            (biasCostMaxAxiomInstance _ _ _ _ _ _ _ _)
            _ _ _ _ _.

Module BiasSmoothTest. Section biasSmoothTest.
  Context {A N rty} `{gameA : smooth A N rty} `{biasA : BiasAxiomClass rty}.
  Context (LambdaMu_ge1 : LambdaMuGe1Class gameA).
  Lemma x0 (t : {ffun 'I_N -> (biasType bias_val A)}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> (biasType bias_val A)}) (i : 'I_N) :
    cost i t == lambda of (biasType bias_val A). Abort.
End biasSmoothTest. End BiasSmoothTest.

(****************************************
  Unit Games c(s) = 0 
 ****************************************)

Section UnitType.
Variable rty : realFieldType.
  
Inductive Unit : Set := mkUnit : Unit.

Definition string_of_unit (r : Unit) : string :=
  match r with
  | unit => "mkUnit"
  end.

Instance unitShowable : Showable Unit :=
  mkShowable string_of_unit.

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
         (N : nat) {rty : realFieldType}
  : CostClass N rty [finType of Unit] :=
  fun (i : 'I_N) (f : {ffun 'I_N -> [finType of Unit]}) => 0.

Program Instance  unitCostAxiomInstance
        (N : nat) {rty : realFieldType}
  : @CostAxiomClass N rty [finType of Unit] (@unitCostInstance N rty).

Instance unitCostMaxInstance ( N : nat) {rty : realFieldType}
  : CostMaxClass N rty Unit := 0.

Program Instance unitCostMaxAxiomInstance
        (N : nat) {rty : realFieldType}
  : CostMaxAxiomClass (@unitCostInstance N rty)
                      (@unitCostMaxInstance N rty).

Program Instance unitGameInstance
        (N : nat) {rty : realFieldType}
  : @game [finType of Unit] N rty 
          (@unitCostInstance N rty)
          (@unitCostAxiomInstance N rty) _
          (@unitCostMaxAxiomInstance _ _).

Module UnitGameTest. Section unitGameTest.
  Context {N rty} `{gameA : game unitType N rty}.
  Variables (t : {ffun 'I_N -> unitType}) (i : 'I_N).
  Check cost i t.
End unitGameTest. End UnitGameTest.

Instance unitLambdaInstance
         (rty : realFieldType) 
  : @LambdaClass Unit rty | 0 := 1.

Program Instance unitLambdaAxiomInstance
        (rty : realFieldType) 
  : @LambdaAxiomClass Unit rty _ | 0.
Next Obligation. by apply: ler01. Qed.

Instance unitMuInstance
         (rty : realFieldType)
  : @MuClass Unit rty | 0 := 0.

Program Instance unitMuAxiomInstance
        (rty : realFieldType)
  : @MuAxiomClass Unit rty _ | 0.
Next Obligation.
  apply/andP; split; first by apply: lerr.
  by apply: ltr01.
Qed.
                                          
Program Instance unitSmoothAxiomInstance {N rty}
  : @SmoothnessAxiomClass [finType of Unit] N rty _ _ _ _ _ _ _ _.
Next Obligation.
  rewrite mul1r /Cost /(cost) /unitCostInstance mul0r addr0 => //.
Qed.

Instance unitSmoothInstance {N rty}
  : @smooth [finType of Unit] N rty _ _ _ _ _ _ _ _ _.

Module UnitSmoothTest. Section unitSmoothTest.
  Context {N rty} `{gameA : smooth [finType of Unit] N rty}.
  Lemma x0 (t : {ffun 'I_N -> [finType of Unit]}) (i : 'I_N) :
    cost i t == 0. Abort.
  Lemma x0 (t : {ffun 'I_N -> [finType of Unit]}) (i : 'I_N) :
    cost i t == lambda of [finType of Unit]. Abort.
End unitSmoothTest. End UnitSmoothTest.

(*********************************************
  Affine Games: C(x) = ax + b, 0 <= a, 0 <= b 
 *********************************************)

Section AffineType.
Variable rty : realFieldType.
Variable scalarA scalarB : ScalarClass rty.

Definition affine_pre (A : Type) : Type :=
  (scalar (@scalar_val _ scalarA) A) *
  (scalar (@scalar_val _ scalarB) (singleton A))%type.

Global Instance affinePredInstance
                  (A : Type) (eqA : Eq A) (eqDecA : Eq_Dec eqA) 
  : PredClass (affine_pre A):=
  fun p => 
    match p.1, p.2 with
    | Wrap x, Wrap (Wrap y) => eqDecA x y
    end.

Global Instance affinePredPreservesBoolableUnit
  (A : Type)
  (eqA : Eq A) (eqDecA : Eq_Dec eqA) (eqReflA : Eq_Refl eqA)
  (boolableA : Boolable A) (boolableUnitA : BoolableUnit boolableA)
  : @PredClassPreservesBoolableUnit 
      (affine_pre A) _ _ _.
Proof.
  rewrite /PredClassPreservesBoolableUnit /affinePredInstance  /=.
  case: eqDecA => H //.
Qed.

Definition affine
             (A : Type) (eqA : Eq A) (eqDecA : Eq_Dec eqA)
  := {x : affine_pre A | the_pred x}.

Global Instance affineBoolable
    (A : Type) (eqA : Eq A) (eqDecA : Eq_Dec eqA)
    `(bA : Boolable A) (a : BoolableUnit bA)
  : Boolable (@affine A _ _) := _.

Global Instance affineBoolableUnit
  (A : Type)
  (eqA : Eq A) (eqDecA : Eq_Dec eqA) (eqReflA : Eq_Refl eqA)
  (boolableA : Boolable A) (boolableUnitA : BoolableUnit boolableA)
  : BoolableUnit (affineBoolable boolableUnitA) := _.

Global Instance affineBoolableUnitAxiom
  (A : Type)
  (eqA : Eq A) (eqDecA : Eq_Dec eqA) (eqReflA : Eq_Refl eqA)
  (boolableA : Boolable A) (boolableUnitA : BoolableUnit boolableA)
  (bA : BoolableUnitAxiom boolableUnitA)
  : @BoolableUnitAxiom (@affine A _ _) _ _ := _.
End AffineType.

Section affineGameTest.
Context `(scalarA : ScalarClass rat_realFieldType) `(@ScalarAxiomClass _ scalarA)
        `(scalarB : ScalarClass rat_realFieldType) `(@ScalarAxiomClass _ scalarB)
         (A : finType) (N : nat) `(Boolable A) `(cgame N A)
         (eqA : Eq A) (eqDecA : Eq_Dec eqA).

Instance affineInst : PredClass (affine_pre scalarA scalarB A):= affinePredInstance eqDecA.
Variable t_pre: {ffun 'I_N -> affine_pre scalarA scalarB A}.
Variable t : {ffun 'I_N -> affine scalarA scalarB eqDecA}.
Variable i : 'I_N.

Check cost i t_pre.
Check cost i t.

End affineGameTest.