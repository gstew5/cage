Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith Qreals Reals Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory Num.Def Num.Theory.

(** This file defines conversions between Ssreflect/MathComp and
    Coq Standard Library implementations of various numeric types, 
    such as: 
      - int <-> Z
      - rat <-> Q
      - rat -> R
 *)

Section int_to_Z.
  Variable i : int.

  Definition int_to_positive : positive :=
    match i with
    | Posz n => Pos.of_nat n
    | Negz n => Pos.of_succ_nat n
    end.

  Definition int_to_Z : Z :=
    match i with
    | Posz n => Z.of_nat n
    | Negz n => Z.neg (Pos.of_succ_nat n)
    end.

  Lemma posint_to_positive (H : (0 < i)%R) :
    Z.pos int_to_positive = int_to_Z.
  Proof.
    rewrite /int_to_positive /int_to_Z.
    case: i H=> //.
    move=> n H.
    rewrite -positive_nat_Z.
    f_equal.
    rewrite Nat2Pos.id=> //.
    by move=> H2; rewrite H2 in H.
  Qed.
End int_to_Z.

Lemma pos_of_succ_nat_mul n m :
  (Pos.of_succ_nat n * Pos.of_succ_nat m)%positive =
  Pos.of_succ_nat (m + (n * m.+1)%Nrec).
Proof.
  elim: n=> //=.
  by rewrite addn0.
  move=> n IH.
  rewrite Pos.mul_succ_l IH.
  rewrite -mulnE mulnS.
  rewrite 3!Pos.of_nat_succ.
  by rewrite -Nat2Pos.inj_add.
Qed.

Lemma opp_posz_negz (n : nat) : GRing.opp (Posz (n.+1)) = Negz n.
Proof. by elim: n. Qed.

Lemma pos_sub_pred p : Z.pos_sub p 1 = Z.pred (Z.pos p).
Proof.
  set (P := fun p0 => Z.pos_sub p0 1 = Z.pred (Z.pos p0)).
  change (P p).
  by apply: positive_ind.
Qed.  

Lemma pos_sub_succ1 m : 
  Z.pos_sub (Pos.of_succ_nat m.+1) 1 = Z.pos (Pos.of_succ_nat m).
Proof.
  rewrite pos_sub_pred.
  rewrite 2!Zpos_P_of_succ_nat.
  rewrite -!Zpred_succ /=.
  by rewrite Zpos_P_of_succ_nat.
Qed.

Lemma pos_sub_succ m n :  
  Z.pos_sub (Pos.succ (Pos.of_succ_nat m)) (Pos.of_succ_nat n) =
  Z.succ (Z.pos_sub (Pos.of_succ_nat m) (Pos.of_succ_nat n)).
Proof.
  rewrite -Pos2Z.add_pos_neg.
  rewrite Pos2Z.inj_succ.
  by rewrite Z.add_comm Z.add_succ_r.
Qed.

Lemma pos_sub_1succ n : 
  Z.pos_sub 1 (Pos.succ (Pos.of_succ_nat n)) =
  Z.neg (Pos.of_succ_nat n).
Proof.
  elim: n=> //= n IH.
  rewrite -Z.pos_sub_opp.
  rewrite -[Pos.succ (Pos.of_succ_nat n)]Pos2SuccNat.id_succ.
  by rewrite pos_sub_succ1.
Qed.
    
Lemma pos_of_succ_nat_sub n m :
  Z.pos_sub (Pos.of_succ_nat n) (Pos.of_succ_nat m) =
  int_to_Z (Posz n - Posz m).
Proof.
  elim: n m=> //= m.
  rewrite sub0r.
  case: m=> [//|m'].
  rewrite opp_posz_negz. simpl.
  rewrite -SuccNat2Pos.inj_succ.
  rewrite -Z.pos_sub_opp.
  rewrite -Pos2Z.opp_pos.
  f_equal.
  rewrite pos_sub_pred.
  rewrite Zpos_P_of_succ_nat.
  by rewrite -Zpred_succ.
  move=> IH n /=.
  rewrite pos_sub_succ.
  rewrite IH.
  rewrite /int_to_Z.
  rewrite intS.
  rewrite -addrA.
  case: (Posz m - Posz n)%R=> n'.
  { by rewrite /= Zpos_P_of_succ_nat. }
  move {IH m n}.
  elim: n'=> // n /= IH.
  have H: (subn n.+1 1 = n) by move {IH}; elim: n.
  by rewrite H pos_sub_1succ.
Qed.  

Lemma pos_of_succ_nat_plus n m : 
  (Pos.of_succ_nat n + Pos.of_succ_nat m)%positive =
  Pos.succ (Pos.of_succ_nat (n + m)).
Proof.
  elim: n m=> // m.
  rewrite add0n.
  rewrite Pos.of_nat_succ.
  by rewrite Pos.add_1_l.
  move=> IH m'.
  simpl.
  rewrite Pos.add_succ_l.
  by rewrite IH.
Qed.

Lemma int_to_Z_add_sub s r :
  int_to_Z (s + Negz r) = int_to_Z (s - (Posz r.+1)).
Proof. by elim: s. Qed.

Lemma int_to_Z_plus (s r : int) :
  Zplus (int_to_Z s) (int_to_Z r) = int_to_Z (s + r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_add.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [|sn'].
    { by rewrite add0r Zplus_0_l. }
    rewrite Pos2Z.add_pos_neg.
    rewrite int_to_Z_add_sub.
    rewrite subzSS.
    by rewrite pos_of_succ_nat_sub.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [|rn'].
    by simpl; rewrite subn0.
    rewrite pos_of_succ_nat_sub.
    symmetry; rewrite addrC.
    rewrite int_to_Z_add_sub.
    by rewrite subzSS.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_plus.
Qed.

Lemma of_succ_nat_of_nat_plus_1 (n : nat):
  Pos.of_succ_nat n = Pos.of_nat (n + 1).
Proof.
  elim n. auto.
  move => n' IHn /=.
  case H: ((n' + 1)%Nrec).
  by rewrite -addnE addn1 in H; congruence.
  by rewrite -H -addnE IHn.
Qed.

Lemma le_plus_minus_r (a : nat):
  (0 < a)%N ->
  a = (a - 1 + 1)%N.
Proof. move => H. by rewrite addnC subnKC. Qed.

Lemma int_to_positive_mul_1 (a b : nat) (H : (a <> 0)%N) :
  (a * b.+1)%N = ((a * b.+1 - 1).+1)%N.
Proof.
   rewrite -[(_ * _ - 1).+1] addn1 -le_plus_minus_r //. rewrite muln_gt0.
   apply /andP. split; auto. rewrite lt0n. apply /eqP. auto.
Qed.

Lemma foiln (a b c d : nat) :
  ((a + b) * (c + d) = a * c + b * c + a * d + b * d)%N.
Proof. by rewrite mulnDr mulnDl mulnDl addnA. Qed.

Lemma int_to_positive_mul (s r : int) :
  s <> Posz(0%N) ->
  r <> Posz(0%N) ->
  int_to_positive (s * r) = Pos.mul (int_to_positive s) (int_to_positive r).
Proof.
  case: s=> sn; move => Hs.
  - case: r=> rn; move => Hr.
    + simpl. rewrite Nat2Pos.inj_mul //; auto.
    + rewrite /GRing.mul /=. 
      have H0: ((sn * rn.+1)%N = ((sn * rn.+1 - 1).+1)%N).
      { apply: int_to_positive_mul_1. auto. }
      rewrite H0 -NegzE /= of_succ_nat_of_nat_plus_1 addn1 -H0.
      rewrite Nat2Pos.inj_mul; auto.
      rewrite of_succ_nat_of_nat_plus_1 addn1 //.
  - case: r=> rn; move => Hr.
      + rewrite /GRing.mul /=. 
        have H0: ((rn * sn.+1)%N = ((rn * sn.+1 - 1).+1)%N).
        { apply: int_to_positive_mul_1. auto. }
        rewrite H0 -NegzE /= of_succ_nat_of_nat_plus_1 addn1 -H0 mulnC.
        rewrite Nat2Pos.inj_mul; auto.
        rewrite of_succ_nat_of_nat_plus_1 addn1 //.
      + rewrite /GRing.mul /=.
        case H0: ((rn + (sn * rn.+1)%Nrec)%coq_nat).
        * have ->: ((rn = 0)%N).
          { rewrite -mulnE in H0. omega. }
          have ->: ((sn = 0)%N).
          { rewrite -mulnE -addn1 in H0.
            case H1: (sn == 0%N).
            move: H1 => /eqP H1. apply H1.
            move: H1 => /eqP /eqP H1. rewrite -lt0n in H1.
            have H2: ((0 < rn + sn * (rn + 1))%N).
            { rewrite addn_gt0. apply /orP. right. rewrite muln_gt0.
              apply /andP. split. auto. rewrite addn1 //. }
            have H3: ((rn + sn * (rn + 1))%N = 0%N). apply H0.
            rewrite H3 in H2. inversion H2. }
            by [].
        * rewrite -H0 -mulnE -Nat2Pos.inj_succ -add1n addnC.
          rewrite !of_succ_nat_of_nat_plus_1 -add1n -Nat2Pos.inj_mul.
          rewrite mulnDr muln1 addnC 2!addnA.
          have ->: (Pos.of_nat ((sn + 1) * (rn + 1))%coq_nat =
                    Pos.of_nat ((sn + 1) * (rn + 1))) by [].
          rewrite foiln mul1n !muln1 addnC addnA [(1 + _)%N] addnC.
          rewrite addnA -addnA [(1 + _)%N] addnC addnA //.
          by rewrite addn1.
          by rewrite addn1.
          rewrite -mulnE in H0. by rewrite addn1 H0.
Qed.

Lemma int_to_Z_mul (s r : int) :
  Zmult (int_to_Z s) (int_to_Z r) = int_to_Z (s * r).
Proof.
  case: s=> sn.
  case: r=> rn.
  simpl.
  by rewrite -Nat2Z.inj_mul.
  { simpl.
    rewrite /Z.of_nat.
    case: sn=> [//=|sn'].
    rewrite mulrC /=.
    f_equal.
    by rewrite pos_of_succ_nat_mul.
  }
  case: r=> rn.
  { simpl.
    rewrite /Z.of_nat.
    case: rn=> [//=|rn'].
    rewrite mulrC /=.
    f_equal.
    rewrite pos_of_succ_nat_mul.
    rewrite -mulnE.
    rewrite 2!mulnS.
    rewrite mulnC.
    rewrite addnA.
    rewrite [(rn' + sn)%N]addnC.
    by rewrite -addnA.
  }
  simpl.
  f_equal.
  by rewrite pos_of_succ_nat_mul.
Qed.

Lemma Zneg_Zlt r s :
  Pos.gt r s -> 
  Zlt (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.gt.
  by rewrite /Z.lt /= => ->.
Qed.  

Lemma Zneg_Zle r s :
  Pos.ge r s -> 
  Zle (Zneg r) (Zneg s).
Proof.
  rewrite /Pos.ge /Z.le /= => H; rewrite /CompOpp.
  by move: H; case: (r ?= s)%positive.
Qed.

Lemma int_to_Z_lt (s r : int) :
  ltr s r ->
  Zlt (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_lt.
    rewrite /ltr /= in H.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.lt (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Zlt_neg_0. }
    apply: Z.lt_le_trans.
    apply: H2.
      by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ltr /= => H.
  apply: Zneg_Zlt.
  move: (inj_lt _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.gt.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_gt_iff.
Qed.  

Lemma int_to_Z_le (s r : int) :
  ler s r ->
  Zle (int_to_Z s) (int_to_Z r).
Proof.
  case: s=> sn; case: r=> rn //.
  { simpl.
    move=> H; apply: inj_le.
    by apply/leP.
  }
  { simpl=> H.
    have H2: (Z.le (Z.neg (Pos.of_succ_nat sn)) 0).
    { by apply: Pos2Z.neg_is_nonpos. }
    apply: Z.le_trans.
    apply: H2.
    by apply: Zle_0_nat.
  }
  simpl.
  rewrite /ler /= => H.
  apply: Zneg_Zle.
  move: (inj_le _ _ (leP H)).
  rewrite 2!Pos.of_nat_succ => H2.
  rewrite /Pos.ge.
  rewrite -Nat2Pos.inj_compare=> //.
  move: H.
  move/leP. 
  simpl.
  by rewrite Nat.compare_ge_iff.
Qed.  

Section rat_to_Q.
  Variable r : rat.
  
  Definition rat_to_Q : Q :=
    let: (n, d) := valq r in
    Qmake (int_to_Z n) (int_to_positive d).
End rat_to_Q.

Section rat_to_Q_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R with R_ssr.  
  Delimit Scope R_scope with R.

  Lemma Z_of_nat_pos_of_nat (a : nat):
    (0 < a)%N ->
    Z.of_nat a =
    Z.pos (Pos.of_nat a).
  Proof.
    rewrite /Z.of_nat. case: a. move => H. inversion H.
    move => n H. rewrite of_succ_nat_of_nat_plus_1. rewrite addn1.
      by [].
  Qed.

Lemma int_to_Z_pos_of_nat (a : nat):
    (0 < a)%N ->
    int_to_Z (Posz a) =
    Z.pos (Pos.of_nat a).
  Proof.
    case: a. move => H. inversion H.
    move => n H. by rewrite -Z_of_nat_pos_of_nat.
  Qed.

  Lemma int_to_Z_pos_of_nat_mul (a : int) (b : nat) (H : (0 < b)%N):
    Zmult (int_to_Z a) (Z.pos (Pos.of_nat b)) = int_to_Z (a * Posz b).
  Proof.
    rewrite -int_to_Z_pos_of_nat //. by rewrite int_to_Z_mul.
  Qed.

  Lemma int_to_Z_inj (a b : int) :
    int_to_Z a = int_to_Z b ->
    a = b.
  Proof.
    rewrite /int_to_Z.
    case a=>n; case b=>n0; move => H.
    apply Nat2Z.inj_iff in H. auto.
    have H1: (Zle 0 (Z.of_nat n)).
    { apply Nat2Z.is_nonneg. }
    have H2: (Zlt (Z.neg (Pos.of_succ_nat n0)) 0).
    { apply Zlt_neg_0. }
    omega.
    have H1: (Zle 0 (Z.of_nat n0)).
    { apply Nat2Z.is_nonneg. }
    have H2: (Zlt (Z.neg (Pos.of_succ_nat n)) 0).
    { apply Zlt_neg_0. }
    omega.
    inversion H. apply SuccNat2Pos.inj_iff in H1. auto.
  Qed.

  Lemma int_to_Z_inj_iff (a b : int) :
    int_to_Z a = int_to_Z b <-> a = b.
  Proof.
    split. apply: int_to_Z_inj. move => H. by rewrite H. Qed.

  Lemma pos_muln (a b : nat) :
    Posz a * Posz b = Posz (muln a b).
  Proof. by []. Qed.

  Lemma le_0_pos_num_gcdn (a b : int) (H : 0 < a) :
    (0 < `|a| %/ gcdn `|b| `|a|)%N.
  Proof.
    rewrite divn_gt0.
    {
      case: (dvdn_gcdr `|a| `|b|)%N => H3.
      apply dvdn_leq => //.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
      by apply: dvdn_gcdr.
    }
    {
      rewrite gcdn_gt0. apply/orP; right.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
    }
  Qed.

  Lemma le_0_neg_num_gcdn (a b : int) (H : 0 < b) (H2 : a < 0) :
    (0 < `|a| %/ gcdn `|a| `|b|)%N.
  Proof.
    rewrite divn_gt0.
    {
      case: (dvdn_gcdl `|a| `|b|)%N => H3.
      apply dvdn_leq => //.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H2.
      case/andP: H2 => //.
    }
    {
      rewrite gcdn_gt0. apply/orP; right.
      rewrite absz_gt0.
      rewrite ltr_neqAle in H.
      case/andP: H => H1 H4.
      apply/eqP.
      move/eqP: H1 => H1 H5.
      symmetry in H5. contradiction.
    }
  Qed.

Lemma int_to_positive_to_Z (a : int) :
  0 < a ->
  Z.pos (int_to_positive a) = int_to_Z a.
Proof.
  rewrite /int_to_positive.
  rewrite /int_to_Z.
  case: a=> an H.
  by rewrite Z_of_nat_pos_of_nat.
  inversion H.
Qed.

  Lemma rat_to_Q_fracq_pos_leib (x y : int) :
    0 < y ->
    coprime `|x| `|y| ->
      (rat_to_Q (fracq (x,y))) = (int_to_Z x # int_to_positive y).
  Proof.
    move=> H0 H1.
    rewrite /fracq /rat_to_Q /=.
    rewrite gtr_eqF => //=.
    rewrite ltr_gtF => //=.
    rewrite /int_to_Z.
    case_eq x => n H2 => /=.
    {
      have H: gcdn n `|y| == 1%N.
      {
        rewrite /coprime in H1.
        apply /eqP.
        move/eqP: H1 => H1.
        rewrite -H1. subst => //.
      }
      move/eqP: H => H.
      rewrite H !div.divn1 mul1n.
      f_equal => //.
      induction y => //.
    }
    {
      rewrite NegzE in H2.
      have H: gcdn n.+1 `|y| == 1%N.
      {
        rewrite /coprime in H1.
        apply /eqP.
        move/eqP: H1 => H1.
        rewrite -H1. subst => //.
      }
      move/eqP: H => H.
      rewrite H !div.divn1 expr1z => /=.
      f_equal. do 2 f_equal.
      rewrite /muln_rec Nat.mul_1_r => //.
      induction y => //.
    }
  Qed.
  
  Lemma rat_to_Q_fracq_pos (x y : int) :
    0 < y -> 
    Qeq (rat_to_Q (fracq (x, y))) (int_to_Z x # int_to_positive y).
  Proof.
    move=> H.
    rewrite /fracq /rat_to_Q /=.
    have ->: (y == 0) = false.
    { rewrite lt0r in H. move: H => /andP [H1 H2].
      apply /eqP. apply /eqP. apply H1. }
    rewrite -int_to_Z_mul.
    have ->: y < 0 = false.
    { rewrite ltrNge in H. move: H => /negP H. apply /negP. auto. }
    simpl.
    case H2: (x < 0).
    { rewrite /nat_of_bool.
      rewrite expr1z.
      rewrite /Qeq /Qnum /Qden.
      rewrite posint_to_positive => //.
      rewrite Z_of_nat_pos_of_nat; last by apply: le_0_neg_num_gcdn.
      rewrite int_to_Z_pos_of_nat_mul; last by apply: le_0_neg_num_gcdn.
      rewrite int_to_Z_mul.
      rewrite -int_to_Z_pos_of_nat; last by apply: le_0_pos_num_gcdn.
      rewrite int_to_Z_mul.
      apply int_to_Z_inj_iff.
      rewrite [_%N * y] mulrC mulrA [y * -1] mulrC -mulrA.
      have H1: (`|y| = y%N) by apply: gtz0_abs.
      rewrite -{1}H1.
      have H3: ((@normr int_numDomainType y) = absz y) by [].
      rewrite H3 /=. rewrite pos_muln -muln_divCA_gcd.
      rewrite mulN1r -pos_muln -mulNr.
      have H4: (`|x| = - x).
      { apply ltz0_abs. by apply: H2. }
      have H5: ((@normr int_numDomainType x) = absz x) by [].
      by rewrite -H5 H4 opprK. }
    rewrite /nat_of_bool /Qeq /Qnum /Qden expr0z.
    apply negbT in H2. rewrite -lerNgt in H2.
    move: H2. case: x => xn H2; last by inversion H2.
    { rewrite lez_nat leq_eqVlt in H2.
      move: H2 => /orP [H2|H2].
      move: H2 => /eqP H2. subst.
      rewrite div0n /= //.
      rewrite Z_of_nat_pos_of_nat;
        last by rewrite gcdnC; apply: le_0_pos_num_gcdn.
      rewrite !int_to_Z_pos_of_nat_mul;
        try (rewrite gcdnC; apply: le_0_pos_num_gcdn => //);
        try (apply le_0_pos_num_gcdn => //).
      rewrite mul1r.
      rewrite int_to_positive_to_Z //.
      rewrite int_to_Z_mul.
      rewrite int_to_Z_inj_iff.
      rewrite mulrC.
      have H1: (`|y| = y%N) by apply: gtz0_abs.
      rewrite -{1}H1.
      have H3: ((@normr int_numDomainType y) = absz y) by [].
      rewrite H3 /=. rewrite 2!pos_muln. 
      by rewrite -muln_divCA_gcd. }
  Qed.

  Lemma lt_and_P_ne_0 (x : int) P :
    (0 < x) && P ->
    x <> 0.
  Proof.
    move => /andP [H0 H1].
    case H2: (x == 0).
    move: H2 => /eqP H2. by rewrite H2 in H0.
    by move: H2 => /eqP H2.
Qed.
    
  Lemma rat_to_Q_plus (r s : rat) :
    Qeq (rat_to_Q (r + s)) (Qplus (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.add /= /addq /addq_subdef.
    case: r; case=> a b /= H.
    case: s; case=> c d /= H2.
    have H3: (0 < b * d).
    { case: (andP H) => X _.
      case: (andP H2) => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qplus /=.
    rewrite int_to_positive_mul.
    rewrite -int_to_Z_plus.
    rewrite -2!int_to_Z_mul.
    rewrite posint_to_positive.
    rewrite posint_to_positive.
    by [].
    by case: (andP H).
    by case: (andP H2).
    apply: lt_and_P_ne_0 H.
    apply: lt_and_P_ne_0 H2.
  Qed.
  
  Lemma rat_to_Q_mul (r s : rat) :
    Qeq (rat_to_Q (r * s)) (Qmult (rat_to_Q r) (rat_to_Q s)).
  Proof.
    rewrite /GRing.mul /= /mulq /mulq_subdef /=.
    case: r; case => a b /= i.
    case: s; case => a' b' /= i'.
    have H3: (0 < b * b').
    { case: (andP i) => X _.
      case: (andP i') => Y _.
      apply: mulr_gt0 => //. }
    rewrite rat_to_Q_fracq_pos => //.
    rewrite /rat_to_Q /=.
    rewrite /Qmult /=.
    rewrite int_to_positive_mul.
    by rewrite -int_to_Z_mul.
    apply: lt_and_P_ne_0 i.
    apply: lt_and_P_ne_0 i'.
  Qed.

  Lemma rat_to_Q_red (r : rat) :
    rat_to_Q r = Qred (rat_to_Q r).
  Proof.
    admit.
  Admitted.
End rat_to_Q_lemmas.    

Section rat_to_R.
  Variable r : rat.

  Definition rat_to_R : R := Q2R (rat_to_Q r).
End rat_to_R.

Section rat_to_R_lemmas.
  Local Open Scope ring_scope.
  Delimit Scope R_scope with R.
  
  Lemma rat_to_R0 : rat_to_R 0 = 0%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_0_l. Qed.

  Lemma rat_to_R1 : rat_to_R 1 = 1%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rmult_1_l Rinv_1. Qed.

  Lemma rat_to_R2 : rat_to_R 2%:R = 2%R.
  Proof. by rewrite /rat_to_R /rat_to_Q /= /Q2R /= Rinv_1 Rmult_1_r. Qed.
  
  Lemma rat_to_R_lt (r s : rat) :
    lt_rat r s ->
    (rat_to_R r < rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qlt_Rlt.
    rewrite /Qlt.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /lt_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_lt.
  Qed.

  Lemma rat_to_R_le (r s : rat) :
    le_rat r s ->
    (rat_to_R r <= rat_to_R s)%R.
  Proof.
    move=> H.
    rewrite /rat_to_R /rat_to_Q /=.
    apply: Qle_Rle.
    rewrite /Qle.
    case: r H; case=> r1 r2 /= H1.
    case: s; case=> s1 s2 /= H2.
    rewrite /le_rat /numq /denq /= => H3.
    case: (andP H1)=> H1a _.
    case: (andP H2)=> H2a _.
    rewrite !posint_to_positive=> //.
    rewrite 2!int_to_Z_mul.
    by apply: int_to_Z_le.
  Qed.

  Lemma rat_to_R_plus (r s : rat) :
    rat_to_R (r + s) = (rat_to_R r + rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_plus.
    apply: Qeq_eqR.
    apply: rat_to_Q_plus.
  Qed.

  Lemma rat_to_R_mul (r s : rat) :
    rat_to_R (r * s) = (rat_to_R r * rat_to_R s)%R.
  Proof.
    rewrite /rat_to_R.
    rewrite -Q2R_mult.
    apply: Qeq_eqR.
    by apply: rat_to_Q_mul.
  Qed.

  Lemma rat_to_R_0_center (r : rat) : rat_to_R r = 0%R -> r == 0.
  Proof.
    move =>  H.
    (*have H0 : rat_to_R r = rat_to_R (-r) by
      rewrite -mulN1r rat_to_R_mul H Rmult_0_r => //. *)
    rewrite -numq_eq0.
    rewrite -rat_to_R0 /rat_to_R /rat_to_Q in H.
    rewrite /numq.
    destruct (valq r) as (r1, r2) => /=.
    simpl in H.
    apply eqR_Qeq in H.
    rewrite /Qeq in H. simpl in H.
    ring_simplify in H.
    induction r1 => //.
  Qed.

  Lemma rat_to_R_inv (r : rat) : (r != 0) -> rat_to_R r^-1 = Rinv (rat_to_R r).
  Proof.
    (*
    case H0 : (r == 0).
    - move/eqP: H0 => H0.
      rewrite H0. rewrite invr0 => //.
      rewrite /rat_to_R /rat_to_Q /Q2R => /=.
      rewrite Rmult_0_l.
    *)
    move => H.
    apply Rmult_eq_reg_l with (r := rat_to_R r).
    rewrite -rat_to_R_mul Rinv_r.
    rewrite mulfV; first by apply rat_to_R1.
    apply H.
    move => H0.
    apply rat_to_R_0_center in H0. apply negbTE in H. congruence.
    move => H0.
    apply rat_to_R_0_center in H0. apply negbTE in H. congruence.
  Qed. 
  Lemma rat_to_R_opp (r : rat) : rat_to_R (- r) = Ropp (rat_to_R r).
  Proof.
    have ->: -r = -1 * r by rewrite mulNr mul1r.
    have ->: (-rat_to_R r = -1 * rat_to_R r)%R.
    { by rewrite Ropp_mult_distr_l_reverse Rmult_1_l. }
    rewrite rat_to_R_mul; f_equal.
    rewrite /rat_to_R /rat_to_Q /Q2R /= Ropp_mult_distr_l_reverse Rmult_1_l.
    by apply: Ropp_eq_compat; rewrite Rinv_1.
  Qed.
End rat_to_R_lemmas.

Section Z_to_int.
  Variable z : Z.

  Definition Z_to_int : int :=
    match z with
    | Z0 => Posz 0
    | Zpos p => Posz (Pos.to_nat p)
    | Zneg p => Negz (Pos.to_nat p).-1
    end.
End Z_to_int.

Lemma Pos_to_natNS p : (Pos.to_nat p).-1.+1 = Pos.to_nat p.
Proof.
  rewrite -(S_pred _ 0) => //.
  apply: Pos2Nat.is_pos.
Qed.  

Lemma PosN0 p : Pos.to_nat p != O%N.
Proof.
  apply/eqP => H.
  move: (Pos2Nat.is_pos p); rewrite H.
  inversion 1.
Qed.  

Section Z_to_int_lemmas.
  Lemma Z_to_int_pos_sub p q :
    Z_to_int (Z.pos_sub q p) = (Posz (Pos.to_nat q) + Negz (Pos.to_nat p).-1)%R.
  Proof.
    rewrite Z.pos_sub_spec.
    case H: (q ?= p)%positive.
    {
      apply Pos.compare_eq_iff in H.
      rewrite NegzE H => //.
      case: (Pos2Nat.is_succ p) => n0 H1.
      rewrite H1 -pred_Sn addrN => //.
    }
    {
      rewrite NegzE => //;
      move: (Pos2Nat.is_pos p) => H0;
      rewrite Nat.succ_pred_pos => //.
      rewrite /Z_to_int NegzE prednK.
      rewrite -opprB. apply /eqP.
      rewrite eqr_opp. apply /eqP.
      rewrite nat_of_P_minus_morphism => /=.
      apply nat_of_P_lt_Lt_compare_morphism in H.
      generalize dependent (Pos.to_nat p);
      induction n => H0 H1;
        first by inversion H1.
      inversion H0.
      {
        rewrite H2 -minus_Sn_m; last by left.
        rewrite minus_diag [Posz n.+1] intS -addrA addrN => //.
      }
      {
        apply IHn in H2.
        rewrite -minus_Sn_m. rewrite !intS H2 addrA => //.
        omega. omega.
      } 
      case: (Pos.compare_lt_iff q p) => H1 _.
      apply Pos.compare_gt_iff. apply H1 in H => //.
      case: (Pos.compare_lt_iff q p) => H1 H2.
      apply H1 in H.
      rewrite nat_of_P_minus_morphism.
      rewrite subn_gt0. apply/ltP.
      apply nat_of_P_lt_Lt_compare_morphism => //.
      apply Pos.compare_gt_iff => //.
    }
    {
      rewrite NegzE => //;
      move: (Pos2Nat.is_pos p) => H0;
      rewrite Nat.succ_pred_pos => //.
      rewrite /Z_to_int.
      rewrite nat_of_P_minus_morphism => /=.
      apply nat_of_P_gt_Gt_compare_morphism in H.
      generalize dependent (Pos.to_nat q).
      induction n => H1;
        first by inversion H1.
      inversion H1.
      {
        rewrite H2 -minus_Sn_m; last by left.
        rewrite minus_diag [Posz n.+1] intS -addrA addrN => //.
      }
      {
        apply IHn in H2.
        rewrite -minus_Sn_m. rewrite !intS H2 addrA => //.
        omega.
      }
      by [].
    }
  Qed.  
  Lemma Z_to_int_plus (r s : Z) :
    Z_to_int (r + s) = (Z_to_int r + Z_to_int s)%R.
  Proof.
    case H: r => [|p|p].
    { by rewrite add0r Zplus_0_l. }
    { case H2: s => [|q|q].
      { by rewrite addr0. }
      { by rewrite /= Pos2Nat.inj_add. }
      by rewrite /= Z_to_int_pos_sub. }
    case H2: s => [|q|q].
    { by rewrite addr0. }
    { by rewrite /= Z_to_int_pos_sub. }
    rewrite /= Pos2Nat.inj_add 3!NegzE.
    rewrite !prednK; try (apply /ltP; apply Pos2Nat.is_pos).
    rewrite -oppz_add //.
    rewrite addn_gt0. apply /orP. left. apply /ltP.
    by apply: Pos2Nat.is_pos.
  Qed.
      
  Lemma Z_to_int_mul (r s : Z) :
    Z_to_int (r * s) = (Z_to_int r * Z_to_int s)%R.
  Proof.
    case H: r => [|p|p].
    { by rewrite /= mul0r. }
    { case H2: s => [|q|q].
      { by rewrite mulr0. }
      { by rewrite /= Pos2Nat.inj_mul. }
      rewrite /= 2!NegzE Pos2Nat.inj_mul.
      have ->: (Pos.to_nat q).-1.+1 = Pos.to_nat q.
      { apply: Pos_to_natNS. }
      rewrite mulrN.
      rewrite prednK //. rewrite muln_gt0. apply /andP.
      split; apply /ltP; apply: Pos2Nat.is_pos. }
    case H2: s => [|q|q].
    { by rewrite mulr0. }
    { rewrite /= Pos2Nat.inj_mul -2!opp_posz_negz Pos_to_natNS.
      rewrite -(S_pred (Pos.to_nat _ * _)%coq_nat 0); first by rewrite mulNr.
      apply /ltP. rewrite muln_gt0. apply /andP.
      split; apply /ltP; apply Pos2Nat.is_pos. }
    rewrite /= Pos2Nat.inj_mul -2!opp_posz_negz 2!Pos_to_natNS.
    by rewrite mulNr mulrN opprK.
  Qed.
End Z_to_int_lemmas.
      
Section Q_to_rat.
  Variable q : Q.

  Definition Q_to_rat : rat :=
    fracq (Z_to_int (Qnum q), Z_to_int (Zpos (Qden q))).
End Q_to_rat.

Section Q_to_rat_lemmas.
  Lemma Q_to_rat1 : Q_to_rat 1 = 1%R.
  Proof. by rewrite /Q_to_rat /= Pos2Nat.inj_1 fracqE /= divr1. Qed.
    
  Lemma Q_to_rat_plus (r s : Q) :
    Q_to_rat (r + s) = (Q_to_rat r + Q_to_rat s)%Q.
  Proof.
    rewrite /Q_to_rat !Z_to_int_plus.
    case: r => a b; case s => c d /=.
    rewrite !Z_to_int_mul /= addq_frac /=.
    f_equal; rewrite /addq_subdef //=; f_equal.
    by rewrite Pos2Nat.inj_mul.
    by apply: PosN0.
    by apply: PosN0.    
  Qed.

  Lemma Q_to_rat_mul (r s : Q) :
    Q_to_rat (r * s) = (Q_to_rat r * Q_to_rat s)%Q.
  Proof.
    rewrite /Q_to_rat /=; case: r => a b; case s => c d /=.
    rewrite Z_to_int_mul mulq_frac /mulq_subdef /=; f_equal.
    by rewrite Pos2Nat.inj_mul.
  Qed.
End Q_to_rat_lemmas.
