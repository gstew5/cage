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

Require Import OUVerT.strings.
Require Import OUVerT.extrema OUVerT.dist OUVerT.numerics
        OUVerT.bigops OUVerT.dyadic.
Require Import games compile smooth christodoulou combinators.
Require Import OUVerT.listlemmas OUVerT.maplemmas subsettypes.

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
  by rewrite N_to_D_to_Q /= rat_to_Q_N_to_Q.
Qed.

Ltac simp :=
  repeat
    match goal with
    | H : ?x = true |- _ =>
      apply Is_true_eq_left in H; unfold Is_true in H
    | H : ?x = false |- _ =>
      apply negbT in H; unfold negb in H
    | H : context[(?x <= ?N)%N] |- _ =>
      case: leP H => //; intros
    | |- context[(?x <= ?N)%N] =>
      apply /leP => //
    end.

Ltac my_omega :=
  unfold Dlt,Qlt,Dle,Qle,Dle,D_to_Q,Qle in *; simpl;
  simp; simpl in *; intros; omega.

Lemma D_num_le_spec : forall (p p' : Z) ,
    Z.le p p' -> 
    Dle (DD {| num := p; den := 1 |}) (DD {| num := p'; den := 1 |})%DRed.
Proof.
  intros.
  my_omega.
Qed.

Lemma le_num_le : forall (n n' : N),
    (n <= n')%num <-> le n n'.
  split; intros.
  apply N.le_equiv in H.
  rewrite /N.le_alt in H.
  destruct H.
  apply Nat.le_equiv.
  rewrite /Nat.le_alt.
  exists x.
  rewrite <- nat_of_add_bin.
  rewrite H.
  auto.  

  apply N.le_equiv.
  rewrite /N.le_alt.
  apply Nat.le_equiv in H.
  rewrite /Nat.le_alt in H.
  destruct H.
  exists (N.of_nat x).
  replace n with (N.of_nat (nat_of_bin n)) by apply N_of_nat_of_bin.
  rewrite -Nat2N.inj_add.
  rewrite H.
  apply N_of_nat_of_bin.
Qed.    
  
Lemma Z_le_inj : forall (n n' : N),
    (n <= n')%num -> (Z.le (NtoZ n) (NtoZ n')).
Proof.
  intros.
  rewrite /NtoZ.
  induction n => //;
                   destruct n'; auto => //.
Qed.
Hint Resolve Z_le_inj.

Lemma if_not_in_filterN_eq_filterSn : forall 
    (l : list (BinNums.N * resource)) (N : BinNums.N) a,
  ~SetoidList.InA (M.eq_key (elt:=resource)) (N, a) l->
  (List.filter (fun p0 : BinNums.N * resource => (nat_of_bin p0.1 < N)%N) l) =
  (List.filter (fun p0 : BinNums.N * resource => (nat_of_bin p0.1 < N.+1)%N) l).
Proof.
  assert (forall x y, {M.eq_key (elt := resource) x y} + {~ M.eq_key x y}).
  destruct x, y; simpl.
  apply M.E.eq_dec.
  assert (forall x l, {SetoidList.InA (M.eq_key (elt:=resource)) x l}
                      + {~ SetoidList.InA (M.eq_key (elt:=resource)) x l}).
  apply SetoidList.InA_dec; intros; auto.
  induction l => //.
  intros N a0 H.
  simpl.
  case_eq (a.1 < N)%N => Hlt //.
  have->: (a.1 < N.+1)%N; auto.
  f_equal.
  eapply IHl; eauto.
  case_eq (a.1 < N.+1)%N => Hlt' //; eauto.
  exfalso.
  apply H.
  constructor.
  rewrite /M.eq_key /M.Raw.Proofs.PX.eqk /N.eq.
  simpl.
  destruct a; simpl in *.
  apply nat_of_bin_inj.
  my_omega.
Qed.

Lemma ctrafficN_relates_ctrafficSn :
  forall (x : BinNums.N) l (N : BinNums.N)  a,
    Datatypes.length
      (List.filter (fun p0 : BinNums.N * resource=> (p0.1 < N)%N) l) = x
    ->  
    Datatypes.length
      (List.filter (fun p0 : BinNums.N * resource => (p0.1 < N.+1)%N) l) =
    S x -> 
    ~ SetoidList.InA (M.eq_key (elt:=resource)) (N,a) l ->
    (S (Datatypes.length
       (List.filter (fun p0 : BinNums.N * resource => (p0.1 < N.+1)%N) l))) =
    x
.
Proof.
  intros.
  apply if_not_in_filterN_eq_filterSn with (N0 := N) in H1.
  rewrite <- H1 in *.
  exfalso.
  rewrite -> H0 in *.
  omega.
Qed.

Lemma ctraffic_Sn_or_normal : forall (l : seq (BinNums.N * resource)) N,
    let l' :=  (Datatypes.length
       (List.filter (fun p0 : BinNums.N * resource => (p0.1 < N.+1)%N) l))
    in 
    SetoidList.NoDupA (M.eq_key (elt:=resource)) l ->
    l' =
    (S (Datatypes.length
    (List.filter (fun p0 : BinNums.N * resource => (p0.1 < N)%N) l)))
    \/
    l' = 
    (Datatypes.length
       (List.filter (fun p0 : BinNums.N * resource => (p0.1 < N)%N) l)).
Proof.
  intros l N l' H.
  unfold l' in *.
  clear l'.
  move: N H.
  induction l => //; auto.
  move => N H.
  inversion H as [| x l0 H2 H3 H1]; subst.
  specialize (IHl N H3).
  destruct IHl; simpl;
  repeat match goal with
         | |- context[if (?x < ?N)%N then _ else _] =>
           let H := fresh "C" in case_eq ((x < N)%N); intros H
  end; simpl; auto; simp; auto.
  {
    have: eq (S (nat_of_bin (@fst BinNums.N resource a))) (S N);
      first by my_omega.
    intros x.
    inversion x.
    subst.
    clear n; clear C0; clear p; clear C; clear x.
    right.
    have:
      exists (n:N), (Datatypes.length
           (List.filter (fun p0 : N * resource => (p0.1 < a.1)%N) l)) = n
           => [| H4].
    destruct (Datatypes.length
      (List.filter (fun p0 : N * resource => (p0.1 < a.1)%N) l)).
    exists N0;
    eauto.
    exists (N.succ (N.of_nat n)).
    rewrite - Nat2N.inj_succ.
    rewrite of_bin_N_of_nat.
    auto.
    destruct H4.
    rewrite -> H1 in *.
    destruct a; simpl in *.
    apply ctrafficN_relates_ctrafficSn with (a := r); auto.
  }
  exfalso.
  my_omega.
Qed.
  
Lemma filter_length_ltN_if_nodup : forall l N,
    SetoidList.NoDupA (M.eq_key (elt:=resource)) l ->
    (Datatypes.length
      (List.filter (fun p : BinNums.N * resource => (p.1 < N)%N) l) <= N)%coq_nat.
Proof.
  intros.
  induction N => //.
  {
    clear -H.
    induction l => //;
    simpl in *; 
    inversion H; subst; auto.    
  }
    destruct (ctraffic_Sn_or_normal (l:=l) N); intuition; auto.
Qed.
    
Lemma lt_fold : forall A (f f' : BinNums.N -> A -> N) l n n',
    (n <= n')%num -> 
    (forall (acc acc': N) x, (acc <= acc')%num ->  f acc x <= f' acc' x)%num-> 
    (le (List.fold_left f l n) (List.fold_left f' l n')).
Proof.
  induction l => //.
  intros.
  simpl.
  apply le_num_le => //.
  intros.
  specialize (IHl (f n a) (f' n' a)).
  apply IHl; 
  auto.
Qed.

Lemma lt_size : forall (N : N) (N0 : BinNums.N)
                       (l : seq (BinNums.N * resource)),
    le (List.fold_left
    (fun (acc : BinNums.N) (p : BinNums.N * resource) =>
     match p.2 with
     | RYes => (acc + 1)%num
     | RNo => acc
     end) l
    N0)
  (List.fold_left (fun (a : BinNums.N) (_ : M.key * resource)
                   => (N.add a 1)%N) l N0).
Proof.
  intros.
  assert (N0 <= N0)%num by 
  apply N.le_refl.
  apply lt_fold with (f := (fun (acc : BinNums.N) (p : BinNums.N * resource) =>
     match p.2 with
     | RYes => (acc + 1)%num
     | RNo => acc
     end))
                     (f' :=
                        (fun (a : BinNums.N) (_ : M.key * resource) => (N.add a 1))) (l := l)
                   in H; eauto.
  intros.
  case: x.2 => //.
  apply N.add_le_mono_r; auto.
  replace acc with (acc + 0)%num.
  apply N.add_le_mono; auto.
  compute; intros; discriminate.
  case acc =>//.
Qed.

Lemma ctraffic_ltN_lt : forall (N : N) m,
  ((ctraffic N m) <= N)%N.
Proof.
  move => N m.
  rewrite /ctraffic.
  rewrite M.fold_1.
  rewrite ctraffic_subF.
  specialize (M.elements_3w m); intros nodup.
  specialize (filter_length_ltN_if_nodup N nodup).
  generalize dependent (M.elements (elt:=resource) m) => l.
  generalize dependent ((List.filter (fun p : BinNums.N * resource => (p.1 < N)%N) l)).
  intros.
  specialize (lt_size N).
  intros.
  specialize (H0 N0 l0 ).
  generalize dependent ((fun (acc : BinNums.N) (p : BinNums.N * resource) =>
      match p.2 with
      | RYes => (acc + 1)%num
      | RNo => acc
      end)).
  intros.
  move: H0.
  assert (forall n n', n = n' ->  (List.fold_left (fun (a : BinNums.N) (_ : M.key * resource) => N.add a 1) l0 n) = 
      (List.fold_left (fun (a : BinNums.N) (_ : M.key * resource) => N.succ (N.of_nat (a)))l0 n')); auto.
  {
    clear.
    induction l0 => //.
    simpl in *.
    intros.
    rewrite (IHl0 (N.add n 1) (N.succ (N.of_nat n'))); subst; auto.
    rewrite -Nat2N.inj_succ.
    rewrite N.add_1_r.
    rewrite Nat2N.inj_succ.
    f_equal.
    rewrite N_of_nat_of_bin => //.
  }
  rewrite (H0 N0 N0); auto.
  clear H0.
  intros.
  apply /leP.
  assert (forall n n',  n = N.of_nat n' ->  List.fold_left 
         (fun (a : BinNums.N) (_ : M.key * resource) =>
            N.succ (N.of_nat a)) l0 n =
          N.of_nat (List.fold_left (fun (x : nat) (_ : M.key * resource) => S x) l0 n')).
  {
    clear.
    induction l0 => //.
    intros.
    simpl in *.
    rewrite N_of_nat_of_bin.
    specialize (IHl0 (N.succ n) (S n')).
    rewrite IHl0; auto.
    rewrite Nat2N.inj_succ.
    f_equal.
    auto.
  }
  specialize (H1 N0 O ).
  rewrite H1 in H0; auto.
  rewrite List.fold_left_length in H0.
  simpl in *.
  clear H1.
  generalize dependent (List.fold_left n l0 0%num).
  intros.
  rewrite of_bin_N_of_nat in H0.
  clear -H H0.
  unfold M.key in H0.
  unfold N.t in H0.
  omega.
Qed.

Instance resourceCCostMaxMaxClassInstance N
  : @CCostMaxMaxClass N [finType of resource] _
                     _.
Proof.
  split;
  rewrite /ccost_fun /resourceCCostInstance /ccostmax_fun;
  rewrite /resourceCCostMaxInstance;
  rewrite /resource_ccost.
  +
    case: (M.find (elt:=resource) i m) => r //.
    case r => //.
    {
      rewrite /ctraffic.
      apply MProps.fold_rec_weak => //.
      intros.
      case (k < N)%N => //.
      case e => //.
      unfold Dle in *.
      rewrite N_to_D_plus.
      rewrite Dadd_ok.
      clear -H0.
      my_omega.
    }
  +
  rewrite /ccost_fun /resourceCCostInstance /ccostmax_fun.
  rewrite /resourceCCostMaxInstance.
  rewrite /resource_ccost.
  case: (M.find (elt:=resource) i m).
  move => a.
  case a.
  {
    rewrite /N_to_D.
    apply D_num_le_spec.
    apply Z.mul_le_mono_nonneg_l => //.
    apply Z_le_inj.
    rewrite le_num_le.
    rewrite of_bin_N_of_nat.
    specialize ctraffic_ltN_lt.
    intros.
    specialize (H (N.of_nat N) m).
    case: leP H => //.
    intros H.
    rewrite of_bin_N_of_nat in H.
    auto.
  }
  all:
  destruct N; 
  compute; intros; discriminate; eauto.
Qed.

Instance resource_cgame N
  : cgame (N:=N) (T:=[finType of resource]) _ _ _ _
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
    (fun (i : OrdNat.t) (m : M.t (singleton A)) =>
      match M.find i m with
      | Some t => if boolify t then 1 else 0
      | _ => 0
      end)%D.

Instance singCTypeInstance (A : Type) (EnumA : Enumerable A)
    : Enumerable (singleton A) := map (@Wrap Singleton A) (enumerate A).

Instance singCCostMaxInstance (N : nat) (A : Type)
    : @CCostMaxClass N (singleton A) := 1%D.

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

  Global Instance singCostMaxMaxInstance
    : CCostMaxMaxClass  (singCCostMaxInstance N A) _.
  Proof.
    split; 
    unfold CCostMaxMaxClass;
    rewrite /ccostmax_fun/singCCostMaxInstance;
    rewrite /ccost_fun /singCCostInstance.
    all:
    case: (M.find (elt:=singleton A) i m); intros;
      [destruct boolify; eauto | ];
          compute; intros; try discriminate.
  Qed.

  Global Instance sing_cgame
  : @cgame N (singletonType A) _ _ _ (singletonCostInstance H0)
      _
      _ (singletonCostMaxAxiomInstance _ A _) _
      _ _ _ _ singRefineCostMaxInstance _.

End singletonCompilable.

Module SingletonCGameTest. Section singletonCGameTest.
  Context {A : finType} {N : nat} `{Boolable A}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (singletonType A).
  Check ccost_fun (N:=N) i' t'.
End singletonCGameTest. End SingletonCGameTest.  

(**********************************************
  Sigma games are compilable 
 **********************************************)

Instance sigmaCCostMaxInstance (N : nat) (A : Type)
         (predInstance : PredClass A)
         (ccostMaxInstance : CCostMaxClass N A)
  : @CCostMaxClass N {x : A | the_pred x} := ccostMaxInstance.

Section sigmaCompilable.
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

  Global Instance sigmaCostMaxMaxInstance (N : nat) (A : finType)
         (ccostA : CCostClass N A)
         (ccostMaxInstance : CCostMaxClass N A)
         (predInstance : PredClass A)
         (ccostMaxInstance : CCostMaxClass N A)
         (ccostMaxMaxInstance : @CCostMaxMaxClass N A _ _ )
    : CCostMaxMaxClass (T := [finType of {x : A | the_pred x}]) _ _.
  Proof.
    rewrite /CCostMaxMaxClass /ccost_fun /ccostmax_fun
            /sigmaCCostInstance /sigmaCCostMaxInstance => //.
  Defined.

  Global Instance sigma_cgame (N : nat) (A : finType)
           (predInstance : PredClass A)
           (costA : CostClass N rat_realFieldType A)
           (costAxiomA : @CostAxiomClass N rat_realFieldType A costA)
           (costMaxA : CostMaxClass N rat_realFieldType A)
           (costMaxAxiomA : CostMaxAxiomClass _ _)
           (ccostA : CCostClass N A)
           (ccostMaxA : CCostMaxClass N A)
           (refineCostMaxInstanceA : RefineCostMaxClass costMaxA ccostMaxA)
           (ccostMaxMaxA : @CCostMaxMaxClass N A _ _)
           `(refineTypeA : RefineTypeClass A)
           (refineCostAxiomA : @RefineCostAxiomClass N A costA ccostA)
           (refineCostA : @RefineCostClass N A costA ccostA _)
           (gA : @game A N rat_realFieldType _ _ _ _)
           (cgA : @cgame N A _ _ _ _ _ _ _ _ _ _ _ _ _ _ )
    : @cgame N [finType of {x : A | the_pred x}] _ _ _ _ _ _ _ _ _ _ _
             _
             (sigmaCostMaxRefineInstance refineCostMaxInstanceA)
             (sigmaGameInstance N _ A predInstance gA) .  
End sigmaCompilable.

(***************************************
  Product Games are compilable 
 ***************************************)

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

Instance prodCCostInstance
       N 
       (aT bT : Type)
       `(ccostA : CCostClass N aT)
       `(ccostB : CCostClass N bT)
  : CCostClass N (aT*bT)
  :=
    (fun (i : OrdNat.t) (m : M.t (aT*bT)) =>
       (ccost i (map_split m).1 +
         ccost i (map_split m).2))%D.

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
  have H2: (D_to_Q ((ccost) i (map_split m).1) ==
            rat_to_Q
              ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).1]))%coq_Qscope.
  { apply: refineA => j pf'.
    rewrite ffunE.
    specialize (H j pf').
    move: H. case: (s (Ordinal (n:=N) (m:=j) pf')) => a b H.
    apply map_split_spec in H.
    case: H => H0 H1.
    apply H0. }
  have H3: (D_to_Q ((ccost) i (map_split m).2) ==
            rat_to_Q
              ((cost) (Ordinal (n:=N) (m:=i) pf) [ffun j => (s j).2]))%Q.
  { apply refineB. move => j pf'.
    rewrite ffunE.
    specialize (H j pf').
    move: H. case: (s (Ordinal (n:=N) (m:=j) pf')) => a b H.
    apply map_split_spec in H.
    case: H => H0 H1.
    apply H1. }
  rewrite /ccost_fun in H2, H3.
  rewrite Dadd_ok.
  rewrite H2 H3 [rat_to_Q (_ + _)] rat_to_Q_red.
  by apply Qeq_sym; rewrite -rat_to_Q_red rat_to_Q_plus.
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
  : CCostMaxClass N (aT*bT) := (ccostMaxA + ccostMaxB)%D. 

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
          rat_to_Q_plus Dadd_ok.
  by apply: Qplus_le_compat.
Qed.


Lemma split_lt_max :
  forall (N : nat) aT bT
         `(costA : CostClass N rat_realFieldType aT)
         `(costB : CostClass N rat_realFieldType bT)
         (ccostA : CCostClass N aT)
         (ccostB : CCostClass N bT)
         (ccostMaxA  : CCostMaxClass N aT)       
         (ccostMaxB  : CCostMaxClass N bT)
         (ccostMaxMaxA : @CCostMaxMaxClass N aT _ _ )
         (ccostMaxMaxB : @CCostMaxMaxClass N bT _ _ )
  (m : M.t (aT * bT)) i,
    (0 <= (ccost_fun (N := N) i (map_split m).1) + (ccost_fun (N := N) i (map_split m).2) <=
     ccostMaxA + ccostMaxB)%DRed.
Proof.
  intros.
  generalize dependent ((map_split m).1) => ma.
  generalize dependent ((map_split m).2) => mb.
  have: (0 <= ccost_fun (N := N) i ma <= ccostMaxA)%DRed;
    last move => H; eauto.
  have: (0 <= (ccost_fun (N := N) i mb) <= ccostMaxB)%DRed;
    last move => H1;
  eauto.
  generalize dependent ((ccost) i ma).
  generalize dependent ((ccost) i mb).
  intros.
  unfold Dle in *.
  rewrite !Dadd_ok.
  destruct H1,H.
  split.
  2: apply Qplus_le_compat; auto.
  clear -H0 H.
  generalize dependent (D_to_Q d).
  generalize dependent (D_to_Q d0).
  intros.
  unfold D_to_Q in *.
  simpl in *.
  assert (0 # 2 == 0)%Q => //.
  rewrite -> H1 in *.
  clear H1.
  clear -H H0.
  destruct q,q0 => //.
  unfold Qle in *.
  simpl in *.
  ring_simplify in H.
  ring_simplify in H0.
  ring_simplify.
  apply Z.add_nonneg_nonneg;
  apply Z.mul_nonneg_nonneg => //.
Qed.

Instance prodCostMaxMaxInstance (N : nat) (aT bT : finType)
         (costA : CostClass N rat_realFieldType aT)
         (costAxiomA : @CostAxiomClass N rat_realFieldType aT costA)
         (costB : CostClass N rat_realFieldType bT)
         (costAxiomB : @CostAxiomClass N rat_realFieldType bT costB)
         (ccostA : CCostClass N aT)
         (ccostB : CCostClass N bT)
         (ccostMaxA  : CCostMaxClass N aT)       
         (ccostMaxB  : CCostMaxClass N bT)       
         (ccostMaxMaxA : @CCostMaxMaxClass N aT _ _ )
         (ccostMaxMaxB : @CCostMaxMaxClass N bT _ _ )
  : @CCostMaxMaxClass N (aT*bT) _ _ .
Proof.
  rewrite /CCostMaxMaxClass;
  rewrite /ccost_fun /ccostmax_fun
          /prodCCostInstance /prodCCostMaxInstance.
  intros.
  apply split_lt_max => //.
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
         (costMaxMaxA : @CCostMaxMaxClass N aT _ _)
         (gA : @game aT N rat_realFieldType _ _ _ _)
         (cgA : @cgame N aT _ _ _ _ _ _ _ _ _ _ _ _ _ _)
         (costB : CostClass N rat_realFieldType bT)
         (costAxiomB : @CostAxiomClass N rat_realFieldType bT costB)
         (ccostB : CCostClass N bT)
         (ccostMaxB : CCostMaxClass N bT)
         (costMaxB : CostMaxClass N rat_realFieldType bT)
         (costMaxAxiomB : CostMaxAxiomClass costB _)
         (refineMaxB : RefineCostMaxClass costMaxB ccostMaxB)
         `(refineTypeB : RefineTypeClass bT)
         (refineCostAxiomB : @RefineCostAxiomClass N bT costB ccostB)
         (costMaxMaxA : @CCostMaxMaxClass N bT _ _)
         (refineCostB : @RefineCostClass N bT costB ccostB _)
         (gB : @game bT N rat_realFieldType _ _ _ _)
         (cgB : @cgame N bT _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  : @cgame N [finType of aT*bT] _ _ _ _ _ _ _ _ _ _ _
           _
           _
           (prodGameInstance N _ _ _ gA gB).


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
         (A : Type)
         `(Enumerable A)
         `(ScalarClass)
  : Enumerable (scalar scalar_val A) := 
    map (@Wrap (Scalar scalar_val) A) (enumerate A).

Definition unwrapScalarTree
           A `(ScalarClass) : M.t (scalar scalar_val A) -> M.t A :=
  fun m : (M.t (scalar scalar_val A)) =>
    M.fold (fun i r acc =>
              M.add i (unwrap r) acc)
      m (M.empty A).    

Global Instance scalarCCostInstance
         N (A : Type)
         `(Enumerable A)
         `(CCostClass N A)
         `(DyadicScalarClass)
  : CCostClass N (scalar scalar_val A)
  :=
    fun (i : OrdNat.t) (m : M.t (@scalar _ scalar_val A)) =>
      (dyadic_scalar_val * ccost i (unwrapScalarTree m))%D.

Instance scalarCCostMaxInstance
         N (A : Type)
         `(cmax : CCostMaxClass N A)
         `(DyadicScalarClass)
  : @CCostMaxClass N (scalar scalar_val A) := (dyadic_scalar_val * cmax)%D.

Section scalarCompilable.
  Context {A N} `{Hdyadic: DyadicScalarClass} `{cgame N A}.

  Global Program Instance scalarRefineTypeAxiomInstance
    : @RefineTypeAxiomClass (scalarType scalar_val A) _.
  Next Obligation.
    clear H gameClass ccostMaxMaxClass  refineCostAxiomClass refineCostClass ccostClass
          costAxiomClass costMaxAxiomClass costClass.
    clear refineTypeClass.
    generalize refineTypeAxiomCl; clear refineTypeAxiomCl.
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
    case_eq (in_mem
               r (mem
                  (enum_mem
                     (T:=scalarType (rty:=rat_realFieldType) scalar_val A)
                     (mem (sort_of_simpl_pred (pred_of_argType
              (Wrapper (Scalar (rty:=rat_realFieldType) scalar_val) A)))))))
      => H3; rewrite H3.
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
    : @RefineTypeClass (scalarType scalar_val A)  _ _.

  Lemma unwrapScalarTree_spec i (t : scalarType scalar_val A) m:
    M.find i m = Some t ->
    M.find i (unwrapScalarTree m) = Some (unwrap t).
  Proof.
    clear H gameClass ccostMaxMaxClass refineCostAxiomClass refineCostClass
          ccostClass costAxiomClass costMaxAxiomClass costClass refineTypeClass refineTypeAxiomCl.
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
    : @RefineCostAxiomClass
        N (scalarType scalar_val A)
        (@scalarCostInstance _ _ _ costClass scalar_val)
        _. 
  Next Obligation.
    clear refineTypeClass H gameClass
          refineCostClass costAxiomClass refineTypeAxiomCl.
    rewrite /cost_fun /scalarCostInstance /cost_fun.
    rewrite /(ccost) /scalarCCostInstance /(ccost).
    rewrite [rat_to_Q (_ * _)] rat_to_Q_red.
    rewrite -rat_to_Q_red /scalar_val.
    rewrite rat_to_Q_mul Dmult_ok.
    generalize (Qeq_dec (rat_to_Q (projT1 dyadic_scalar_val)) 0%Q).
    case => refineTypeAxiomCl.
    { rewrite refineTypeAxiomCl !Qmult_0_l => //.
      have ->: (D_to_Q dyadic_scalar_val == 0)%Q.
      { by rewrite dyadic_rat_to_Q refineTypeAxiomCl. }
      by rewrite Qmult_0_l. }
    have ->: (D_to_Q dyadic_scalar_val == rat_to_Q (projT1 dyadic_scalar_val))%Q.
    { apply: dyadic_rat_to_Q. }
    apply Qmult_inj_l => //.
    move: refineCostAxiomClass; clear refineCostAxiomClass.
    rewrite /RefineCostAxiomClass /(ccost) => refineCostAxiomClass.
    specialize (refineCostAxiomClass pf).
    rewrite -(@refineCostAxiomClass(unwrapScalarTree m)) => //.
    move => j pf'. 
    specialize (H0 j pf').
    apply unwrapScalarTree_spec in H0.
    rewrite H0. f_equal.
    rewrite /unwrap_ffun. rewrite ffunE => //.
  Qed.

  Global Instance scalarRefineCostInstance
    : @RefineCostClass N (scalarType scalar_val A)
        (@scalarCostInstance N _ A costClass _) _ _.

  Global Instance scalarRefineCostMaxInstance
         `(scalarAxiomInstance : @ScalarAxiomClass _ scalar_val)
    : @RefineCostMaxClass
        N (scalarType scalar_val A)
        (scalarCostMaxInstance costMaxClass scalar_val)
        (scalarCCostMaxInstance ccostMaxClass dyadic_scalar_val).
  Proof.
    rewrite /RefineCostMaxClass /scalarCostMaxInstance /scalarCCostMaxInstance.
    rewrite rat_to_Q_mul Dmult_ok.
    rewrite /scalar_val.
    have ->: (rat_to_Q (projT1 dyadic_scalar_val) == D_to_Q dyadic_scalar_val)%Q.
    { by rewrite dyadic_rat_to_Q. }
    rewrite Qmult_comm [Qmult (D_to_Q _) _]Qmult_comm.
    apply Qmult_le_compat_r => //.
    have H3 : rat_to_Q 0 = 0%Q by rewrite rat_to_Q0.
    rewrite -H3.
    have ->: (D_to_Q dyadic_scalar_val == rat_to_Q (projT1 dyadic_scalar_val))%Q.
    { by apply: dyadic_rat_to_Q. }
    apply le_rat_to_Q => //.
  Qed.

  Global Instance scalarCostMaxMaxInstance 
         `(scalarAxiomInstance : @ScalarAxiomClass _ scalar_val)
         (ccostMaxMax : @CCostMaxMaxClass N A
                                          _ _ )
    : @CCostMaxMaxClass N  (scalarType scalar_val A) _ _.
  Proof.
    split;
      rewrite /CCostMaxMaxClass;
    unfold CCostMaxMaxClass in ccostMaxMax;
    specialize (ccostMaxMax i (unwrapScalarTree m));
    rewrite  /ccost_fun;
    unfold Dle in *;
    repeat rewrite Dmult_ok;
    rewrite Qmult_comm;
    destruct ccostMaxMax.
    +
      have: (D_to_Q 0 == 0)%Q => [|ZeroZero] //.
      rewrite -> ZeroZero in *.
      apply Qmult_le_0_compat => //; eauto.
      have H5 : rat_to_Q 0 = 0%Q by rewrite rat_to_Q0.
      rewrite -H5.
      have ->: (D_to_Q dyadic_scalar_val == rat_to_Q (projT1 dyadic_scalar_val))%Q.
      { by apply: dyadic_rat_to_Q. }
      apply le_rat_to_Q => //.
    +
        have->: (Qmult (D_to_Q (dyadic_rat_to_D Hdyadic))
                     (D_to_Q ccostMaxClass) ==
               Qmult (D_to_Q ccostMaxClass)
                     (D_to_Q (dyadic_rat_to_D Hdyadic)))%coq_Qscope.
      rewrite Qmult_comm => //.
      apply Qmult_le_compat_r => //.
      have H5 : rat_to_Q 0 = 0%Q by rewrite rat_to_Q0.
      rewrite -H5.
      have ->: (D_to_Q dyadic_scalar_val == rat_to_Q (projT1 dyadic_scalar_val))%Q.
      { by apply: dyadic_rat_to_Q. }
      apply le_rat_to_Q => //.
  Qed.

  Global Instance scalar_cgame
         `{scalarA : @ScalarAxiomClass _ scalar_val}
    : @cgame
        N (scalarType scalar_val A)
        _ _ _ _ _ _ _ _ _ _ _ _ _
        (scalarGameInstance _ _ _ _ _).
End scalarCompilable.

Module ScalarCGameTest. Section scalarCGameTest.
  Context {A : finType} {N : nat} `{cgame N A}
          `{Hdyad: DyadicScalarClass}
          `{scalarA : @ScalarAxiomClass _ scalar_val}.
  Variable i' : OrdNat.t.
  Variable t' : M.t (@scalarType rat_realFieldType scalar_val A).
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
         (q : DRat)
  : CCostClass N (bias (projT1 q) A)
  :=
    fun (i : OrdNat.t) (m : M.t (bias (projT1 q) A)) =>
      (q + ccost i (unwrapBiasTree m))%D.
  
Instance biasCCostMaxInstance N (A : Type) `(cmax : CCostMaxClass N A) (q : DRat)
  : @CCostMaxClass N (bias (projT1 q) A) := (q + cmax)%D.

Instance biasCTypeInstance A (q : DRat)
         `(Enumerable A)
  : Enumerable (bias (projT1 q) A) :=
  map (@Wrap (Bias (projT1 q)) A) (enumerate A).

Section biasCompilable.
  Context {A N} {q : DRat} `{cgame N A}.

  Global Program Instance biasRefineTypeAxiomInstance
    : @RefineTypeAxiomClass (biasType (projT1 q) A) _.
  Next Obligation.
    clear gameClass ccostMaxMaxClass refineCostAxiomClass H  refineCostClass
          ccostClass costAxiomClass costMaxAxiomClass costClass refineTypeClass.
    generalize refineTypeAxiomCl; clear refineTypeAxiomCl.
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
    : @RefineTypeClass (biasType (projT1 q) A)  _ _.

  Lemma unwrapBiasTree_spec i (t : biasType (projT1 q) A) m:
    M.find i m = Some t ->
      M.find i (unwrapBiasTree m) = Some (unwrap t).
  Proof.
    clear refineTypeClass H gameClass ccostMaxMaxClass refineCostAxiomClass refineCostClass
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
    : @RefineCostAxiomClass _ (biasType (projT1 q) A) (biasCostInstance costClass) _.
  Next Obligation.
    clear refineTypeClass H gameClass
           costAxiomClass refineCostClass.
    rewrite /cost_fun /biasCostInstance /cost_fun.
    rewrite /(ccost) /biasCCostInstance /ccost_fun /(ccost).
    rewrite [rat_to_Q (_ + _)] rat_to_Q_red.
    rewrite Dadd_ok.
    rewrite -rat_to_Q_red.
    rewrite rat_to_Q_plus /scalar_val.
    rewrite /bias_val.
    have ->: (D_to_Q q == rat_to_Q (projT1 q))%Q.
    { by apply: dyadic_rat_to_Q. }
    move: (Qeq_dec (rat_to_Q q) 0%Q).
    move: refineCostAxiomClass; clear refineCostAxiomClass.
    rewrite /RefineCostAxiomClass /(ccost) => refineCostAxiomClass.
    specialize (refineCostAxiomClass pf) => H.
    rewrite ->(@refineCostAxiomClass(unwrapBiasTree m)) => //.
    move => j pf'. 
    specialize (H0 j pf').
    apply unwrapBiasTree_spec in H0.
    rewrite H0. f_equal.
    rewrite /unwrap_ffun. rewrite ffunE => //.
  Qed.

  Global Instance biasRefineCostInstance
    : @RefineCostClass N (biasType (projT1 q) A) (biasCostInstance costClass) _ _.

  Global Instance biasRefineCostMaxInstance
         `(biasAxiomInstance : @BiasAxiomClass _ (projT1 q))
    : @RefineCostMaxClass N (biasType (projT1 q) A)
        (biasCostMaxInstance _ _ _ costMaxClass biasAxiomInstance)
        (biasCCostMaxInstance _ _).
  Proof.
    rewrite /RefineCostMaxClass /biasCostMaxInstance /biasCCostMaxInstance
            rat_to_Q_plus Dadd_ok /bias_val.
    have ->: (D_to_Q q == rat_to_Q (projT1 q))%Q.
    { by apply: dyadic_rat_to_Q. }
    apply Qplus_le_compat => //.    
    apply Qle_refl.
  Qed.

  Global Instance biasCostMaxMaxInstance
         `{@BiasAxiomClass rat_realFieldType q}
         : @CCostMaxMaxClass N (biasType (projT1 q) A) _ _.
  Proof.
    split; 
    rewrite /CCostMaxMaxClass;
    unfold CCostMaxMaxClass in ccostMaxMaxClass;
    clear H gameClass;
    rename ccostMaxMaxClass into H4;
    specialize (H4 i (unwrapBiasTree m));
    rewrite  /ccost_fun
              /biasCCostInstance;
    rewrite /ccostmax_fun
            /biasCCostMaxInstance;
    destruct H4;
    unfold Dle in *; repeat rewrite Dadd_ok.
    +
      have: (D_to_Q 0 == 0)%Q => [| ZeroZero] //.
      clear -H0 H1 H ZeroZero.
      rewrite -> ZeroZero in *.
      {
        move: H1;
        generalize dependent
                   (D_to_Q ((ccost) i (unwrapBiasTree (A:=A) (q:=projT1 q) m))).
        unfold BiasAxiomClass in H0.
        unfold bias_val in *.
        have: (0 <= D_to_Q q)%Q => //.
        {
          apply le_rat_to_Q in H0=> //.
          clear -H0.
          move: H0.
          have->: ((rat_to_Q 0) = 0)%Q => //.
          rewrite <- dyadic_rat_to_Q => //.
        }
        intros H2 q0 H1.
        generalize dependent (D_to_Q q).
        intros.
        unfold Qle in *.
        simpl in *.
        ring_simplify in H2.
        ring_simplify in H1.
        ring_simplify.
        apply Z.add_nonneg_nonneg;
          apply Z.mul_nonneg_nonneg => //.
      }
      repeat rewrite Dadd_ok.
      apply Qplus_le_compat => //.
      my_omega.
  Qed.

  Global Instance bias_cgame `{@BiasAxiomClass rat_realFieldType q}
    : @cgame N (biasType (projT1 q) A) _ _ _ _ _ _
             (biasCostMaxAxiomInstance _ _ _ _ _ _ _ _)
             _ _ _ _ _ _ (biasGameInstance _ _ _ _ _).
End biasCompilable.

Module BiasCGameTest. Section biasCGameTest.
  Context {A : finType} {N : nat} `{cgame N A} {q : DRat}
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

  Definition unit_ccost (i : OrdNat.t) (m : M.t Unit) : D := 0.

  Global Instance unitCCostInstance
    : CCostClass N [finType of Unit] := unit_ccost.

  Global Program Instance unitRefineCostAxiomInstance
    : @RefineCostAxiomClass N [finType of Unit] _ _.
  Next Obligation.
    rewrite /(ccost) /(cost) /unitCostInstance /unitCCostInstance /unit_ccost.
    by rewrite DO_to_Q0 rat_to_Q0.
  Qed.
    
  Global Instance unitRefineCostInstance
    : @RefineCostClass N [finType of Unit] _ _ _.

  Global Instance unitCCostMaxInstance
    : @CCostMaxClass N [finType of Unit] := 0%D.

  Global Instance unitrefineCostMaxInstance
    : @RefineCostMaxClass _ _ (@unitCostMaxInstance N _) unitCCostMaxInstance.
  Proof.
    rewrite /RefineCostMaxClass /unitCostMaxInstance /unitCCostMaxInstance.
    rewrite /rat_to_Q => //.
  Qed.
  Global Instance unitCCostMaxMaxInstance
         : @CCostMaxMaxClass N [finType of Unit] _ _.
  Proof.
    rewrite /CCostMaxMaxClass.
    move => i m.
    rewrite /ccost_fun /ccostmax_fun /unitCCostInstance
            /unit_ccost /unitCCostMaxInstance => //.
  Qed.

  Global Instance unit_cgame : cgame (N:=N) (T:= [finType of Unit]) _ _ _ _ _.
End unitCompilable.

(***************************
 Affine Games are compilable 
 ***************************)

Section affineCompilable.
  Context {A N}
          `{scalA : DyadicScalarClass}
          `{scalB : DyadicScalarClass}
          `{cgame N A}
          `{Boolable A}
          (eqA : Eq A) (eqDecA : Eq_Dec eqA).

  Definition affine_preType :=
    ((@scalarType rat_realFieldType (@dyadic_scalar_val scalA) A) *
    (@scalarType rat_realFieldType (@dyadic_scalar_val scalB) (singletonType A)))%type.

  Global Instance affineTypePredInstance :
    PredClass (affine_preType) := affinePredInstance eqDecA.

  Definition affineType := [finType of {x : affine_preType | the_pred x}].

  Section affineGameTest.
    Variable i' : OrdNat.t.
    Variable t' : M.t (affine_preType).

    Check ccost_fun (N:=N) i' t'.
  End affineGameTest.
End affineCompilable.


(* Hints to help automatic instance derivation for typclasses eauto. *)
  Hint Extern 4 (RefineTypeAxiomClass ?t)=>
  refine (sigmaRefineTypeAxiomInstance _ _ _) : typeclass_instances.

  Hint Extern 4 (CostClass ?n ?r ?t) =>
  refine (sigmaCostInstance _) : typeclass_instances.

  Hint Extern 1 (ScalarAxiomClass ?r )=> done : typeclass_instances.

  Hint Extern 4 (CostAxiomClass ?c) =>
  refine (sigmaCostAxiomInstance _ _ _ _ _) : typeclass_instances.

  Hint Extern 4 (RefineCostAxiomClass ?c ?a) =>
  refine (sigmaRefineCostAxiomInstance _ _ _ _ _ _)
    : typeclass_instances.

  Hint Extern 4 (RefineCostAxiomClass ?c ?a) =>
  refine (sigmaCCostInstance _)
    : typeclass_instances.

  Hint Extern 4 (CostMaxAxiomClass ?cc ?cmc) =>
  refine (sigmaCostMaxAxiomInstance _ _ _ _ _ _ _)
    : typeclass_instances.

  Hint Extern 4 (RefineCostMaxClass ?cc ?cmc) =>
  compute; (try discriminate)
    : typeclass_instances.

  Hint Extern 4 (RefineTypeClass ?rtac) =>
  refine  (sigmaRefineTypeInstance _ _ _)
    : typeclass_instances.

  Hint Extern 4 (RefineCostClass ?rtac) =>
  refine (sigmaRefineCostInstance _ _)
    : typeclass_instances.

  Hint Extern 4 (CCostMaxMaxClass ?rtac ?m) =>
  refine (scalarCostMaxMaxInstance _ _)
    : typeclass_instances.

