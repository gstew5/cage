Set Implicit Arguments.
Unset Strict Implicit.

Require Import NArith QArith String.
Require Import ProofIrrelevance.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

Require Import strings.
Require Import extrema dist numerics bigops dyadic.
Require Import games compile smooth christodoulou combinators.

Local Open Scope ring_scope.

(******************************************
  Resource Games are Compilable
 ******************************************)

Instance resourceEnumerableInstance : Enumerable resource := 
  [:: RYes; RNo].

Program Instance resourceRefineTypeAxiomInstance
  : @RefineTypeAxiomClass [finType of resource] _.
Next Obligation.
  by split => // r; rewrite mem_enum; case: r. 
Qed.

Instance resourceRefineTypeInstance
  : @RefineTypeClass [finType of resource] _ _.

Definition ctraffic (N : nat) (m : M.t resource) : N.t :=
  (M.fold (fun i r acc =>
             if (i < N)%N
             then match r with
                  | RYes => acc + 1
                  | RNo => acc
                   end
             else acc)
          m 0)%num.

Lemma ctraffic_sub0 N (l : seq (M.key * resource)) n :
  (List.fold_left
    (fun acc p => 
        if ((nat_of_bin p.1) < N)%N
          then match p.2 with
               | RYes => acc + 1
               | RNo => acc
               end
          else acc)
    l n
      =
  (List.fold_left
    (fun acc p => 
        if ( (nat_of_bin p.1) < N)%N
          then match p.2 with
               | RYes => acc + 1
               | RNo => acc
               end
          else acc)
    l 0 + n))%num.
Proof.
  move: n.
  induction l => //=.
  move => n.
  case: (a.1 < N)%N => //.
  case: a.2; rewrite IHl => //=.
  rewrite (IHl 1%num).
  rewrite -N.add_assoc.
  f_equal.
  apply N.add_comm.
Qed.

Lemma ctraffic_subP N l n :
  (List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => acc + 1
               | RNo => acc
               end
          else acc)
    l n
      =
  List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => acc + 1
               | RNo => acc
               end
          else acc)
    (List.rev l) n)%num.
Proof.
  rewrite -List.fold_left_rev_right.
  induction (List.rev l) => //=.
  rewrite IHl0.
  case: (a.1 < N)%N => //.
  case: (a.2) => //.
  rewrite (ctraffic_sub0 _ _ (n+1)%num) ctraffic_sub0.
  by rewrite N.add_assoc.
Qed.

Lemma ctraffic_filter_sub0 (l : seq (M.key * resource)) n :
  (List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => acc + 1
      | RNo => acc
      end)
    l n
      =
  (List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => acc + 1
      | RNo => acc
      end)
    l 0 + n))%num.
Proof.
  move: n; induction l => //.
  move => n => /=.
  rewrite IHl.
  case: a.2 => //.
  rewrite (IHl (0+1)%num) N.add_0_l.
  rewrite (N.add_comm n 1) N.add_assoc //.
Qed.

Lemma ctraffic_subF N l n :
  (List.fold_left
    (fun acc p => 
        if (nat_of_bin p.1 < N)%N
          then match p.2 with
               | RYes => acc + 1
               | RNo => acc
               end
          else acc)
    l n
      =
  List.fold_left
    (fun acc p => 
      match p.2 with
      | RYes => acc + 1
      | RNo => acc
      end)
    (List.filter (fun p => (nat_of_bin p.1 < N)%N) l) n)%num.
Proof.
  move: n.
  set f := 
   (fun (acc : N.t) (p : BinNums.N * resource) =>
    if (p.1 < N)%N
    then match p.2 with
        | RYes => (acc + 1)%num
        | RNo => acc
        end
    else acc).
  set f' :=
   (fun (acc : N.t) (p : BinNums.N * resource) =>
   match p.2 with
   | RYes => (acc + 1)%num
   | RNo => acc
   end). 
  induction l => //=.
  move => n.
  rewrite ctraffic_sub0 IHl.
  rewrite /f {2}/f'.
  case: (a.1 < N)%N => //=.
  case: a.2.
  rewrite (ctraffic_filter_sub0 _ (n+1)%num) => //.
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

Lemma ctraffic_sub_subP (l : seq (M.key*resource)):
  let f :=
    (fun acc p => 
      match p.2 with
      | RYes => (acc + 1)%num
      | RNo => acc
      end) in
  N_to_Q (List.fold_left f l 0)%num
    =
  rat_to_Q
    ((count
      (fun p => p.2  == RYes)
      l)%:R).
Proof.
  induction l => //=.
  have H : rat_to_Q 1 = 1%coq_Qscope by rewrite /rat_to_Q => //.
  have Hx : N_to_Q 1 = 1%coq_Qscope by [].
  have Hy : N_to_Q 0 = 0%coq_Qscope by [].  
  case: a.2; rewrite ctraffic_filter_sub0 /= N_to_Q_plus IHl; set Y := count _ _.
  { rewrite Hx natrD -rat_to_Q_s_add.
    by rewrite Qplus_leib_comm H.
    have H1: (0%:R <= (count (fun p : M.key * resource => p.2 == RYes) l)%:R).
    { move => t. by rewrite ler_nat. }
    by apply: H1. }
  by rewrite Hy addnC addn0 Qplus_leib_comm Qplus_leib_0_l.
Qed.

Definition resource_ccost N (i : OrdNat.t) (m : M.t resource) : D :=
  match M.find i m with
  | Some RYes => N_to_D (ctraffic N m)
  | Some RNo => D0
  | None => D0 (*won't occur when i < N*)
  end.

Global Instance resourceCCostInstance N : CCostClass N resource
  := resource_ccost N.

Definition lift_traffic N (s : {ffun 'I_N -> resource})
  : seq (M.key*resource):=
 map
  (fun (x : 'I_N) => ((N.of_nat x), s x))
  (index_enum (ordinal_finType N)).  

Lemma list_trafficP N (s : {ffun 'I_N -> resource}) :
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
  Proof. by apply list_in_iff, mem_enum. Qed.

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

(*FIXME: MOVE*)
Lemma eq_Qeq q r : q=r -> Qeq q r.
Proof. by move => ->; apply: Qeq_refl. Qed.                     

Program Instance resourceRefineCostAxiomInstance N
  : @RefineCostAxiomClass N [finType of resource] _ _.
Next Obligation.  
  rewrite /(ccost) /resourceCCostInstance /resource_ccost.
  rewrite (H i pf).
  rewrite /(cost) /resourceCostInstance /= /resourceCostFun /=.
  case H2: (s _) => //.
  rewrite /ctraffic M.fold_1 trafficP /traffic' ctraffic_subF.
  move: (M.elements_3w m) => H1.
  rewrite N_to_D_to_Q.
  rewrite ctraffic_sub_subP.
  apply: eq_Qeq.
  f_equal.
  rewrite sum1_count.
  rewrite -list_trafficP.
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
                | x0 <- index_enum (ordinal_finType N)])=> H5 => //.
      case/mapP: H5 => y H6 H7.
      case/andP: H4; split; destruct x as [x1 x2]; inversion H7 => /=.
      rewrite /index_enum -enumT //= in H6.
      rewrite of_bin_N_of_nat => //.
      apply list_in_iff.
      clear pf H2 H7 H3 H4 H6 x1 x2.
      simpl in y.
      destruct y as [yn Hy].
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

Instance resourceRefineCostInstance N
  : @RefineCostClass N [finType of resource] _ _ _.

Instance resourceCCostMaxInstance N
  : @CCostMaxClass N [finType of resource] :=
  N_to_D (N.of_nat N).

Instance resourceRefineCostMaxInstance N
  : @RefineCostMaxClass N _ (resourceCostMaxInstance _) (resourceCCostMaxInstance _).
Proof.
  rewrite /RefineCostMaxClass /resourceCCostMaxInstance /resourceCostMaxInstance.
  apply Qle_lteq.
  right => //.
  rewrite N_to_D_to_Q /=.
  admit. (* HERE HERE HERE *)
Qed.

Instance resource_cgame N
  : cgame (N:=N) (T:=[finType of resource]) _ _ _
      (resourceGame N).

(** [NOTE Enumerable instances]
    ~~~~~~~~~~~~~~~~~~~~~~
    [Enumerable] instances should in general avoid using Ssreflect [enum]. 
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


(*********************************************
 Singleton Games are Compilable 
 *********************************************)

Global Instance singCCostInstance (A : Type) `(Boolable A) N
  : CCostClass N (singleton A)
  :=      
    fun (i : OrdNat.t) (m : M.t (singleton A)) =>
      (match M.find i m with
            | Some t => if (boolify t) then 1%coq_Qscope else 0%coq_Qscope
            | _ => 0%coq_Qscope
            end).

Instance singCTypeInstance (A : Type) (EnumA : Enumerable A)
    : Enumerable (singleton A) := map (@Wrap Singleton A) (enumerate A).

Instance singCCostMaxInstance (N : nat) (A : Type)
    : @CCostMaxClass N (singleton A) := 1%Q.


Section singletonCompilable.
  Context {A : finType} {N: nat} `{RefineTypeAxiomClass A} `{Boolable A}.

  Global Program Instance singRefineTypeAxiomInstance
    : @RefineTypeAxiomClass (singletonType A) (singCTypeInstance _).
  Next Obligation.
    generalize H => H1. clear H. case: H1 => H1 H2.
    split; last first.
    {
      rewrite map_inj_uniq. apply H2.
      rewrite /injective => x1 x2 H3.
      inversion H3 => //.
    }
    rewrite /(enumerate Wrapper Singleton A) /singCTypeInstance.
    move => r.
    apply /mapP.
    case_eq (in_mem r (mem (enum_mem (T:=singletonType A)
              (mem (sort_of_simpl_pred (pred_of_argType
                (Wrapper Singleton A))))))) => H3; rewrite H3.
    {
      move: H3.
      case: r => x H3.
      exists x; last by [].
      rewrite H1 mem_enum.
      rewrite mem_enum in H3 => //.
    }
    {
      move => H4.
      case: H4 => x H4 H5.
      rewrite H5 in H3.
      move/negP: H3 => H3.
      apply H3 => //.
      rewrite mem_enum => //.
    }
  Qed.

  Global Instance singRefineTypeInstance
    : @RefineTypeClass (singletonType A)  _ _.

  Global Program Instance singRefineCostAxiomInstance `(Boolable A)
    : RefineCostAxiomClass _ (singCCostInstance _ N).
  Next Obligation.
    rewrite /cost_fun /singletonCostInstance /cost_fun.
    rewrite /ccost_fun /singCCostInstance /ccost_fun.
    rewrite (H2 i pf).
    case: (boolify (s (Ordinal (n := N) (m := i) pf))) => //.
  Qed.
  
  Global Instance singRefineCostInstance
    : @RefineCostClass N (singletonType A) _ _ _.

  Global Instance singRefineCostMaxInstance
    : @RefineCostMaxClass N _ (singletonCostMaxInstance _ _) (singCCostMaxInstance N A).
  Proof.
    rewrite /RefineCostMaxClass /resourceCCostMaxInstance
            /singletonCostMaxInstance /singCCostMaxInstance => //.
  Qed.

  Global Instance sing_cgame
  : @cgame N (singletonType A) _ _ _ (singletonCostInstance H0)
      _
      _ (singletonCostMaxAxiomInstance _ A _) _ _ _ _ singRefineCostMaxInstance _.
End singletonCompilable.

Module SingletonCGameTest. Section singletonCGameTest.
  Context {A : finType} {N : nat} `{Boolable A}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (singletonType A).
  Check ccost_fun (N:=N) i' t'.
End singletonCGameTest.  End SingletonCGameTest.  

(**********************************************
  Sigma games are compilable 
 **********************************************)

Instance sigmaCCostMaxInstance (N : nat) (A : Type)
         (predInstance : PredClass A)
         (ccostMaxInstance : CCostMaxClass N A)
  : @CCostMaxClass N {x : A | the_pred x} := ccostMaxInstance.

Section sigmaCompilable.
  Definition to_sigma A (f : A -> bool) (x : A) : option {x : A | f x} :=
    (match f x return f x = _ -> option {x : A | f x} with
     | false => fun _ => None
     | true => fun pf => Some (exist f x pf)
     end) erefl.

  Fixpoint filter_sigma A (f : A -> bool) (l : seq A) : seq {x : A | f x} :=
    match l with
    | nil => nil
    | h :: t =>
      match to_sigma f h with
      | Some x => x :: filter_sigma f t
      | None => filter_sigma f t
      end
    end.

  Lemma to_sigma_true_Some A (f : A -> bool) x :
    f x = true ->
    exists x', to_sigma f x = Some x'.
  Proof.
    rewrite /to_sigma.
    move: (exist (fun x0 => f x0) x).
    case: (f x) => //.
    by move => s pf; exists (s erefl).
  Qed.

  Lemma to_sigma_inj (A : finType) (f : A -> bool) a b :
    to_sigma f a = Some b ->
    a = proj1_sig b.
  Proof.
    rewrite /to_sigma.
    have H: forall pf', (proj1_sig (exist (fun x => f x) a pf') = a) by [].
    move: H.
    move: (exist (fun x => f x) a).
    case: (f a) => // s H; case.
    by rewrite -(H (erefl true)) => ->.
  Qed.

  Lemma to_sigma_None_false A (f : A -> bool) (a : A) :
    to_sigma f a = None ->
    f a = false.
  Proof.
    move=> H. destruct (f a) eqn:Hf => //.
    have H0: (exists a', to_sigma f a = some a').
    { by apply to_sigma_true_Some, Hf. }
    destruct H0 as [a']. rewrite H in H0. inversion H0.
  Qed.

  Lemma mem_seq_filter
        (A : finType) (f : A -> bool) (x : A) (x' : {x : A | f x}) l :
    to_sigma f x = Some x' ->
    mem_seq (filter_sigma f l) x' ->
    mem_seq l x.
  Proof.
    move=> H0 H1. induction l. inversion H1.
    simpl in H1. destruct (to_sigma f a) eqn:Hs.
    move: H1=> /orP [H1 | H1]. apply /orP. left. 
    move: H1=> /eqP H1. subst.
    apply to_sigma_inj in Hs. apply to_sigma_inj in H0. subst => //.
    apply /orP. right. apply IHl; assumption.
    apply /orP. right. apply IHl; assumption.
  Qed.

  Lemma projT1_inj A (f : A -> bool) (a b : {x : A | f x}) :
    proj1_sig a = proj1_sig b ->
    a = b.
  Proof.
    case: a; case: b=> /= x p x0 p0 H.
    by subst; f_equal; apply proof_irrelevance.
  Qed.

  Lemma projT1_pred_true A (f : A -> bool) (a : A) (b : {x : A | f x}) :
    a = proj1_sig b ->
    f a = true.
  Proof. by case: b=> /= x H0 H1; rewrite H1 H0. Qed.

  Lemma list_in_filter_sigma
        (A : finType) (f : A -> bool) (x : {x : A | f x}) (l : seq A) :
    List.In (proj1_sig x) l ->
    List.In x (filter_sigma f l).
  Proof.
    move=> H. induction l. inversion H.
    simpl. simpl in H. destruct H as [H | H].
    - destruct (to_sigma f a) eqn:Hs.
      + simpl. apply to_sigma_inj in Hs. left. rewrite H in Hs.
        apply projT1_inj in Hs. by rewrite Hs.
      + apply projT1_pred_true in H. apply to_sigma_None_false in Hs.
        congruence.
    - destruct (to_sigma f a) eqn:Hs; try right; apply IHl; assumption.
  Qed.

  Global Instance sigmaEnumerableInstance (A : Type)
           (enumerableInstance : Enumerable A)
           (predInstance : PredClass A)
    : Enumerable {x : A | the_pred x} :=
    filter_sigma the_pred (enumerate A).

  Global Program Instance sigmaRefineTypeAxiomInstance
          (A : finType)
          `(refineTypeAxiomInstanceA : RefineTypeAxiomClass A)
          (predInstance : PredClass A)
    : @RefineTypeAxiomClass [finType of {x : A | the_pred x}] _.
  Next Obligation.
    rewrite /RefineTypeAxiomClass in refineTypeAxiomInstanceA.
    case: refineTypeAxiomInstanceA=> [H0 H1]. rewrite /eq_mem in H0.
    split.
    { move=> r. rewrite /enumerable_fun. rewrite /sigmaEnumerableInstance.
      have ->: (r \in enum [finType of {x : A | the_pred x}]).
      { apply mem_enum. }
      have ->: (r \in filter_sigma the_pred (enumerate A)).
      { apply list_in_iff, list_in_filter_sigma.
        specialize (H0 (proj1_sig r)). apply list_in_iff.
        rewrite H0. by apply mem_enum. }
        by []. }
    { rewrite /enumerable_fun /sigmaEnumerableInstance. clear H0. move: H1.
      elim: (enumerate A).
      - by [].
      - move => a l IHl H1. simpl. simpl in H1. move: H1=> /andP [H1 H2].
        destruct (to_sigma the_pred a) eqn:Ha. simpl. apply /andP.
        split. rewrite /in_mem. simpl. apply /negP. move=> Contra.
        rewrite /in_mem in H1. simpl in H1. move: H1=> /negP H1.
        rewrite /pred_of_eq_seq in H1. rewrite /pred_of_eq_seq in Contra.
        
        have H3: (mem_seq (T:=A) l a).
        { apply: mem_seq_filter. apply Ha. assumption. }
        contradiction.
        apply IHl; assumption. apply IHl; assumption. }
  Qed.

  Global Instance sigmaRefineTypeInstance (A : finType)
           (predInstance : PredClass A)
           `(refineTypeAxiomInstanceA : RefineTypeAxiomClass A)
    : @RefineTypeClass [finType of {x : A | the_pred x}]  _ _.

  Global Instance sigmaCCostInstance
           (A : Type) N
           (predInstance : PredClass A)
           (ccostA : @CCostClass N A)
    : CCostClass N {x : A | the_pred x}
    :=
      fun (i : OrdNat.t) (m : M.t {x : A | the_pred x}) =>
        ccost i (M.map (fun x => proj1_sig x) m).
  
  Global Program Instance sigmaRefineCostAxiomInstance
          (N : nat) (A : finType)
          (predInstance : PredClass A)
          (costA : CostClass N rat_realFieldType A)
          (ccostA : CCostClass N A)
          (refineA : RefineCostAxiomClass costA ccostA)
    : @RefineCostAxiomClass
        N [finType of {x : A | the_pred x}]
        (@sigmaCostInstance N rat_realFieldType A _ costA)
        (@sigmaCCostInstance A _ _ ccostA).
  Next Obligation.
    apply refineA=> j pf'; rewrite ffunE.
    apply MProps.F.find_mapsto_iff, MProps.F.map_mapsto_iff.
    specialize (H j pf'); apply MProps.F.find_mapsto_iff in H.
    by exists (s (Ordinal (n:=N) (m:=j) pf')); split => //.
  Qed.

  Global Instance sigmaRefineCostInstance (N : nat) (A : finType)
           (predInstance : PredClass A)
           (costA : CostClass N rat_realFieldType A)
           (ccostA : CCostClass N A)
           (refineA : RefineCostAxiomClass costA ccostA)
    : @RefineCostClass N [finType of {x : A | the_pred x}] _ _ _.

  Global Instance sigmaCostMaxRefineInstance (N : nat) (A : finType)
           (predInstance : PredClass A)
           (costMaxInstance : CostMaxClass N _ A)
           (ccostMaxInstance : CCostMaxClass N A)
           (refineCostMaxInstance : RefineCostMaxClass costMaxInstance ccostMaxInstance)
    : @RefineCostMaxClass N A
        (sigmaCostMaxInstance predInstance costMaxInstance)
        (sigmaCCostMaxInstance predInstance ccostMaxInstance).
  Proof.
    rewrite /RefineCostMaxClass /sigmaCostMaxInstance
            /sigmaCCostMaxInstance => //.
  Qed.

  Global Instance sigma_cgame (N : nat) (A : finType)
           (predInstance : PredClass A)
           (costA : CostClass N rat_realFieldType A)
           (costAxiomA : @CostAxiomClass N rat_realFieldType A costA)
           (costMaxA : CostMaxClass N rat_realFieldType A)
           (costMaxAxiomA : CostMaxAxiomClass _ _)
           (ccostA : CCostClass N A)
           (ccostMaxA : CCostMaxClass N A)
           (refineCostMaxInstanceA : RefineCostMaxClass costMaxA ccostMaxA)
           `(refineTypeA : RefineTypeClass A)
           (refineCostAxiomA : @RefineCostAxiomClass N A costA ccostA)
           (refineCostA : @RefineCostClass N A costA ccostA _)
           (gA : @game A N rat_realFieldType _ _ _ _)
           (cgA : @cgame N A _ _ _ _ _ _ _ _ _ _ _ _ _)
    : @cgame N [finType of {x : A | the_pred x}] _ _ _ _ _ _ _ _ _ _ _
             (sigmaCostMaxRefineInstance refineCostMaxInstanceA)
             (sigmaGameInstance N _ A predInstance gA) .  
End sigmaCompilable.

(***************************************
  Product Games are compilable 
 ***************************************)

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

Instance prodEnumerableInstance (aT bT : Type)
         (enumerableA : Enumerable aT)
         (enumerableB : Enumerable bT)
  : Enumerable (aT*bT) :=
  List.list_prod (enumerate aT) (enumerate bT).

Program Instance prodRefineTypeAxiomInstance
        (aT bT : finType)
        `(refineTypeAxiomInstanceA : RefineTypeAxiomClass aT)
        `(refineTypeAxiomInstanceB : RefineTypeAxiomClass bT)
  : @RefineTypeAxiomClass [finType of aT*bT] _.
Next Obligation.
  rewrite /RefineTypeAxiomClass in refineTypeAxiomInstanceA.
  rewrite /RefineTypeAxiomClass in refineTypeAxiomInstanceB.
  case: refineTypeAxiomInstanceA=> [HA0 HA1].
  case: refineTypeAxiomInstanceB=> [HB0 HB1].
  split.
  { move => r. rewrite mem_enum. case: r. move => a b.
    rewrite /prodEnumerableInstance /enumerable_fun.
    rewrite /eq_mem in HA0. rewrite /eq_mem in HB0.
    have H: (List.In (a, b) (List.list_prod (enumerate aT) (enumerate bT))).
    { apply List.in_prod_iff. split; apply list_in_iff.
      - by rewrite HA0; apply mem_enum.
      - by rewrite HB0; apply mem_enum. }
    apply list_in_iff in H. by rewrite H. }
    by apply: list_prod_uniq; assumption.
Qed.

Instance prodRefineTypeInstance (aT bT : finType)
         `(refineTypeAxiomInstanceA : RefineTypeAxiomClass aT)
         `(refineTypeAxiomInstanceB : RefineTypeAxiomClass bT)
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
       N 
       (aT bT : Type)
       `(ccostA : CCostClass N aT)
       `(ccostB : CCostClass N bT)
  : CCostClass N (aT*bT)
  :=
    fun (i : OrdNat.t) (m : M.t (aT*bT)) =>
      Qred (match M.find i m with
            | Some (a, b) => (ccost i (map_split m).1 +
                              ccost i (map_split m).2)%coq_Qscope
            | _ => 0%coq_Qscope
            end).

Program Instance prodRefineCostAxiomInstance
        (N : nat) (aT bT : finType)
        (costA : CostClass N rat_realFieldType aT)
        (costB : CostClass N rat_realFieldType bT)
        (ccostA : CCostClass N aT)
        (ccostB : CCostClass N bT)
        (refineA : RefineCostAxiomClass costA ccostA)
        (refineB : RefineCostAxiomClass costB ccostB)
  : @RefineCostAxiomClass
      N [finType of aT*bT]
      (@prodCostInstance N rat_realFieldType aT bT costA costB)
      (@prodCCostInstance N aT bT ccostA ccostB).
Next Obligation.
  rewrite /cost_fun /prodCostInstance /cost_fun
          /ccost_fun /prodCCostInstance /ccost_fun.
  rewrite /RefineCostAxiomClass in refineA, refineB.
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
  rewrite /ccost_fun in H2, H3.
  rewrite H2 H3 [rat_to_Q (_ + _)] rat_to_Q_red.
  apply Qred_complete, Qeq_sym, rat_to_Q_plus.
Qed.

Instance prodRefineCostInstance (N : nat) (aT bT : finType)
         (costA : CostClass N rat_realFieldType aT)
         (costB : CostClass N rat_realFieldType bT)
         (ccostA : CCostClass N aT)
         (ccostB : CCostClass N bT)
         (refineA : RefineCostAxiomClass costA ccostA)
         (refineB : RefineCostAxiomClass costB ccostB)
  : @RefineCostClass N [finType of aT*bT] _ _ _.

Instance prodCCostMaxInstance (N : nat) (aT bT : Type)
         (ccostMaxA : CCostMaxClass N aT)
         (ccostMaxB : CCostMaxClass N bT)
  : CCostMaxClass N (aT*bT) := (ccostMaxA + ccostMaxB)%Q. 

Instance prodRefineMaxCostInstance (N : nat) (aT bT : finType)
         (costMaxA   : CostMaxClass N _ aT)
         (ccostMaxA  : CCostMaxClass N aT)
         (refineMaxA : RefineCostMaxClass costMaxA ccostMaxA)
         (costMaxB   : CostMaxClass N _ bT)
         (ccostMaxB  : CCostMaxClass N bT)       
         (refineMaxB : RefineCostMaxClass costMaxB ccostMaxB)
  : RefineCostMaxClass
      (prodCostMaxInstance costMaxA costMaxB)
      (prodCCostMaxInstance ccostMaxA ccostMaxB).
Proof.
  rewrite /RefineCostMaxClass /prodCostMaxInstance /prodCCostMaxInstance
          rat_to_Q_plus. apply Qplus_le_compat => //.
Qed.

Instance prod_cgame (N : nat) (aT bT : finType)
         (costA : CostClass N rat_realFieldType aT)
         (costAxiomA : @CostAxiomClass N rat_realFieldType aT costA)
         (ccostA : CCostClass N aT)
         (costMaxA : CostMaxClass N rat_realFieldType aT)
         (ccostMaxA  : CCostMaxClass N aT)
         (costMaxAxiomA : CostMaxAxiomClass costA _)
         (refineMaxA : RefineCostMaxClass costMaxA ccostMaxA)
         `(refineTypeA : RefineTypeClass aT)
         (refineCostAxiomA : @RefineCostAxiomClass N aT costA ccostA)
         (refineCostA : @RefineCostClass N aT costA ccostA _)
         (gA : @game aT N rat_realFieldType _ _ _ _)
         (cgA : @cgame N aT _ _ _ _ _ _ _ _ _ _ _ _ _)
         (costB : CostClass N rat_realFieldType bT)
         (costAxiomB : @CostAxiomClass N rat_realFieldType bT costB)
         (ccostB : CCostClass N bT)
         (ccostMaxB : CCostMaxClass N bT)
         (costMaxB : CostMaxClass N rat_realFieldType bT)
         (costMaxAxiomB : CostMaxAxiomClass costB _)
         (refineMaxB : RefineCostMaxClass costMaxB ccostMaxB)
         `(refineTypeB : RefineTypeClass bT)
         (refineCostAxiomB : @RefineCostAxiomClass N bT costB ccostB)
         (refineCostB : @RefineCostClass N bT costB ccostB _)
         (gB : @game bT N rat_realFieldType _ _ _ _)
         (cgB : @cgame N bT _ _ _ _ _ _ _ _ _ _ _ _ _)
  : @cgame N [finType of aT*bT] _ _ _ _ _ _ _ _ _ _ _
           (prodRefineMaxCostInstance refineMaxA refineMaxB)
           (prodGameInstance N _ _ _ gA gB) .  

Module ProdCGameTest. Section prodCGameTest.
  Context {A B : finType} {N : nat} `{cgame N A} `{cgame N B}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (A*B).
  Check ccost_fun (N:=N) i' t'.
End prodCGameTest. End ProdCGameTest.

(*******************************************
 Scalar Games are Compilable 
 *******************************************)

Instance scalarEnumerableInstance
         (A : Type) `(Enumerable A)
         (q : rat)
  : Enumerable (scalar q A) := map (@Wrap (Scalar q) A) (enumerate A).

Definition unwrapScalarTree A (q : rat) : M.t (scalar q A) -> M.t A :=
  fun m : (M.t (scalar q A)) =>
    M.fold (fun i r acc =>
              M.add i (unwrap r) acc)
      m (M.empty A).    

Instance scalarCCostInstance
         N (A : Type)
         `(Enumerable A) `(CCostClass N A)
         (q : rat)
  : CCostClass N (scalar q A)
  :=
    fun (i : OrdNat.t) (m : M.t (scalar q A)) =>
      Qred(Qmult (rat_to_Q q) (ccost i (unwrapScalarTree m))).

Instance scalarCCostMaxInstance
         N (A : Type) `(cmax : CCostMaxClass N A) (q : rat)
  : @CCostMaxClass N (scalar q A) := (rat_to_Q q * cmax)%Q.

Section scalarCompilable.
  Context {A N} {q : rat} `{cgame N A}.

  Global Program Instance scalarRefineTypeAxiomInstance
    : @RefineTypeAxiomClass (scalarType q A) _.
  Next Obligation.
    clear H1 H2 refineCostAxiomClass H0 refineCostClass ccostClass
          costAxiomClass costMaxAxiomClass costClass.
    generalize H; clear H.
    rewrite /RefineTypeAxiomClass => H.
    destruct H; split; last first.
    {
      rewrite map_inj_uniq. apply H.
      rewrite /injective => x1 x2 H3.
      inversion H3 => //.
    }
    rewrite /(enumerate Wrapper Singleton A) /singCTypeInstance.
    move => r.
    apply /mapP.
    case_eq (in_mem r (mem (enum_mem (T:=scalarType (rty:=rat_realFieldType) q A)
              (mem (sort_of_simpl_pred (pred_of_argType
                (Wrapper (Scalar (rty:=rat_realFieldType) q) A))))))) => H3; rewrite H3.
    {
      move: H3.
      case: r => x H3.
      exists x; last by [].
      rewrite H0 mem_enum.
      rewrite mem_enum in H3 => //.
    }
    {
      move => H4.
      case: H4 => x H4 H5.
      rewrite H5 in H3.
      move/negP: H3 => H3.
      apply H3 => //.
      rewrite mem_enum => //.
    }
  Qed.

  Global Instance scalarRefineTypeInstance
    : @RefineTypeClass (scalarType q A)  _ _.

  Lemma unwrapScalarTree_spec i (t : scalarType q A) m:
    M.find i m = Some t ->
      M.find i (unwrapScalarTree m) = Some (unwrap t).
  Proof.
    clear H H0 H1 H2 refineCostAxiomClass refineCostClass
          ccostClass costAxiomClass costMaxAxiomClass costClass.
    rewrite /unwrapScalarTree.
    apply MProps.fold_rec_weak.
    {
      move => mo m' a' H0 H1 H2.
      have H3: (forall (k : M.key) e,
        M.MapsTo k e mo <-> M.MapsTo k e m');
          first by apply MProps.F.Equal_mapsto_iff; apply H0.
      apply M.find_2 in H2. apply H3 in H2. apply M.find_1 in H2.
      apply H1. apply H2.
    }
    {
      move => H. inversion H.
    }
    {
      move => k e a' m' H0 IH. case: e. move => a0 H2 /=.
      rewrite MProps.F.add_o. case: (MProps.F.eq_dec k i) => H3 //.
      generalize H2; clear H2.
      rewrite MProps.F.add_eq_o. move => H2. inversion H2.
      split => []. by []. apply IH.
      generalize H2; clear H2.
      rewrite MProps.F.add_neq_o. move => H2. inversion H2 => //.
      by [].
    }
  Qed.

  Global Program Instance scalarRefineCostAxiomInstance
    : @RefineCostAxiomClass N (scalarType q A)
        (@scalarCostInstance _ _ _ costClass q) _. 
  Next Obligation.
    clear H H0 H1 H2
          refineCostClass costAxiomClass.
    rewrite /cost_fun /scalarCostInstance /cost_fun.
    rewrite /(ccost) /scalarCCostInstance /(ccost).
    rewrite [rat_to_Q (_ * _)] rat_to_Q_red.
    apply Qred_complete.
    rewrite rat_to_Q_mul /scalar_val.
    move: (Qeq_dec (rat_to_Q q) 0%Q).
    case => H0;
      first by rewrite H0 !Qmult_0_l => //.
    apply Qmult_inj_l => //.
    move: refineCostAxiomClass; clear refineCostAxiomClass.
    rewrite /RefineCostAxiomClass /(ccost) => refineCostAxiomClass.
    specialize (refineCostAxiomClass pf).
    rewrite -(@refineCostAxiomClass(unwrapScalarTree m)) => //.
    move => j pf'. 
    specialize (H3 j pf').
    apply unwrapScalarTree_spec in H3.
    rewrite H3. f_equal.
    rewrite /unwrap_ffun. rewrite ffunE => //.
  Qed.

  Global Instance scalarRefineCostInstance
    : @RefineCostClass N (scalarType q A)
        (@scalarCostInstance N _ A costClass _) _ _.

  Global Instance scalarRefineCostMaxInstance `(scalarAxiomInstance : @ScalarAxiomClass _ q)
    : @RefineCostMaxClass N (scalarType q A)
        (scalarCostMaxInstance costMaxClass q) (scalarCCostMaxInstance ccostMaxClass q).
  Proof.
    rewrite /RefineCostMaxClass /scalarCostMaxInstance /scalarCCostMaxInstance 
            rat_to_Q_mul. apply Qmult_le_l => //.
    have H3 : rat_to_Q 0 = 0%Q by rewrite rat_to_Q0.
    rewrite -H3. apply lt_rat_to_Q => //.
  Qed.

  Global Instance scalar_cgame `{scalarA : @ScalarAxiomClass rat_realFieldType q}
    : @cgame N (scalarType q A) _ _ _ _ _ _ _ _ _ _ _ _
        (scalarGameInstance _ _ _ _ _).
End scalarCompilable.

Module ScalarCGameTest. Section scalarCGameTest.
  Context {A : finType} {N : nat} `{cgame N A} {q : rat_realFieldType}
          `{scalarA : @ScalarAxiomClass rat_realFieldType q}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (@scalarType rat_realFieldType q A).
  Check ccost_fun (N:=N) i' t'.
End scalarCGameTest. End ScalarCGameTest.

(**********************************
 Bias Games are Compilable 
 **********************************)

Definition unwrapBiasTree A (q : rat) : M.t (bias q A) -> M.t A :=
  fun m : (M.t (bias q A)) =>
    M.fold (fun i r acc =>
              M.add i (unwrap r) acc)
      m (M.empty A).    

Global Instance biasCCostInstance
         N (A : Type)
         `(Enumerable A) `(CCostClass N A)
         (q : rat)
  : CCostClass N (bias q A)
  :=
    fun (i : OrdNat.t) (m : M.t (bias q A)) =>
      Qred(Qplus (rat_to_Q q) (ccost i (unwrapBiasTree m))).
  
Instance biasCCostMaxInstance N (A : Type) `(cmax : CCostMaxClass N A) (q : rat)
  : @CCostMaxClass N (bias q A) := ((rat_to_Q q) + cmax)%Q.

Instance biasCTypeInstance A (q : rat)
         `(Enumerable A)
  : Enumerable (bias q A) :=
  map (@Wrap (Bias q) A) (enumerate A).

Section biasCompilable.
  Context {A N} {q : rat} `{cgame N A}.

  Global Program Instance biasRefineTypeAxiomInstance
    : @RefineTypeAxiomClass (biasType q A) _.
  Next Obligation.
    clear H1 H2 refineCostAxiomClass  H0 refineCostClass
          ccostClass costAxiomClass costMaxAxiomClass costClass.
    generalize H; clear H.
    rewrite /RefineTypeAxiomClass => H.
    destruct H; split; last first.
    {
      rewrite map_inj_uniq. apply H.
      rewrite /injective => x1 x2 H3.
      inversion H3 => //.
    }
    rewrite /(enumerate Wrapper Singleton A) /singCTypeInstance.
    move => r.
    apply /mapP.
    case_eq (in_mem r (mem (enum_mem (T:=biasType (rty:=rat_realFieldType) q A)
              (mem (sort_of_simpl_pred (pred_of_argType
                (Wrapper (Bias (rty:=rat_realFieldType) q) A))))))) => H3; rewrite H3.
    {
      move: H3.
      case: r => x H3.
      exists x; last by [].
      rewrite H0 mem_enum.
      rewrite mem_enum in H3 => //.
    }
    {
      move => H4.
      case: H4 => x H4 H5.
      rewrite H5 in H3.
      move/negP: H3 => H3.
      apply H3 => //.
      rewrite mem_enum => //.
    }
  Qed.

  Global Instance biasRefineTypeInstance
    : @RefineTypeClass (biasType q A)  _ _.

  Lemma unwrapBiasTree_spec i (t : biasType q A) m:
    M.find i m = Some t ->
      M.find i (unwrapBiasTree m) = Some (unwrap t).
  Proof.
    clear H H0 H1 H2 refineCostAxiomClass refineCostClass
          ccostClass costAxiomClass costMaxAxiomClass costClass.
    rewrite /unwrapBiasTree.
    apply MProps.fold_rec_weak.
    {
      move => mo m' a' H0 H1 H2.
      have H3: (forall (k : M.key) e,
        M.MapsTo k e mo <-> M.MapsTo k e m');
          first by apply MProps.F.Equal_mapsto_iff; apply H0.
      apply M.find_2 in H2. apply H3 in H2. apply M.find_1 in H2.
      apply H1. apply H2.
    }
    {
      move => H. inversion H.
    }
    {
      move => k e a' m' H0 IH. case: e. move => a0 H2 /=.
      rewrite MProps.F.add_o. case: (MProps.F.eq_dec k i) => H3 //.
      generalize H2; clear H2.
      rewrite MProps.F.add_eq_o. move => H2. inversion H2.
      split => []. by []. apply IH.
      generalize H2; clear H2.
      rewrite MProps.F.add_neq_o. move => H2. inversion H2 => //.
      by [].
    }
  Qed.

  Global Program Instance biasRefineCostAxiomInstance
    : @RefineCostAxiomClass _ (biasType q A) (biasCostInstance costClass) _.
  Next Obligation.
    clear H H0 H1 H2
          refineCostClass costAxiomClass.
    rewrite /cost_fun /biasCostInstance /cost_fun.
    rewrite /(ccost) /biasCCostInstance /ccost_fun /(ccost).
    rewrite [rat_to_Q (_ + _)] rat_to_Q_red.
    apply Qred_complete.
    rewrite rat_to_Q_plus /scalar_val.
    move: (Qeq_dec (rat_to_Q q) 0%Q).
    move: refineCostAxiomClass; clear refineCostAxiomClass.
    rewrite /RefineCostAxiomClass /(ccost) => refineCostAxiomClass.
    specialize (refineCostAxiomClass pf).
    rewrite -(@refineCostAxiomClass(unwrapBiasTree m)) => //.
    move => j pf'. 
    specialize (H3 j pf').
    apply unwrapBiasTree_spec in H3.
    rewrite H3. f_equal.
    rewrite /unwrap_ffun. rewrite ffunE => //.
  Qed.

  Global Instance biasRefineCostInstance
    : @RefineCostClass N (biasType q A) (biasCostInstance costClass) _ _.

  Global Instance biasRefineCostMaxInstance `(biasAxiomInstance : @BiasAxiomClass _ q)
    : @RefineCostMaxClass N (biasType q A)
        (biasCostMaxInstance _ _ _ costMaxClass biasAxiomInstance)
        (biasCCostMaxInstance _ _).
  Proof.
    rewrite /RefineCostMaxClass /biasCostMaxInstance /biasCCostMaxInstance
            rat_to_Q_plus. apply Qplus_le_compat => //.
    apply Qle_refl.
  Qed.

  Global Instance bias_cgame `{@BiasAxiomClass rat_realFieldType q}
    : @cgame N (biasType q A) _ _ _ _ _ _
             (biasCostMaxAxiomInstance _ _ _ _ _ _ _ _)
             _ _ _ _ _(biasGameInstance _ _ _ _ _).
End biasCompilable.

Module BiasCGameTest. Section biasCGameTest.
  Context {A : finType} {N : nat} `{cgame N A} {q : rat_realFieldType}
          `{biasA : @BiasAxiomClass rat_realFieldType q}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (@biasType rat_realFieldType q A).
  Check ccost_fun (N:=N) i' t'.
End biasCGameTest. End BiasCGameTest.

(***************************
 Unit Games are compilable 
 ***************************)

Section unitCompilable.
  Variable (N : nat).

  Global Instance unitEnumerableInstance : Enumerable Unit :=
    [:: mkUnit].

  Global Program Instance unitRefineTypeAxiomInstance
    : @RefineTypeAxiomClass [finType of Unit] _.
  Next Obligation. by split => // r; rewrite mem_enum; case: r. Qed.

  Global Instance unitRefineTypeInstance
    : @RefineTypeClass [finType of Unit]  _ _.

  Definition unit_ccost (i : OrdNat.t) (m : M.t Unit) : Qcoq :=
    0%coq_Qscope.

  Global Instance unitCCostInstance
    : CCostClass N [finType of Unit] := unit_ccost.

  Global Program Instance unitRefineCostAxiomInstance
    : @RefineCostAxiomClass N [finType of Unit] _ _.

  Global Instance unitRefineCostInstance
    : @RefineCostClass N [finType of Unit] _ _ _.

  Global Instance unitCCostMaxInstance
    : @CCostMaxClass N [finType of Unit] := 0%Q. 

  Global Instance unitrefineCostMaxInstance
    : @RefineCostMaxClass _ _ (unitCostMaxInstance N _) unitCCostMaxInstance.
  Proof.
    rewrite /RefineCostMaxClass /unitCostMaxInstance /unitCCostMaxInstance.
    rewrite /rat_to_Q => //.
  Qed.

  Global Instance unit_cgame 
    : cgame (N:=N) (T:= [finType of Unit]) _ _ _ _.
End unitCompilable.
