Require Import ZArith PArith QArith.

Record D : Set :=
  Dmake { num : Z;
          den : positive }.

Definition pow_pos (p r : positive) : positive :=
  Pos.iter (Pos.mul p) 1%positive r.

Lemma pow_pos_Zpow_pos p r : Zpos (pow_pos p r) = Z.pow_pos (Zpos p) r.
Proof.
  unfold pow_pos, Z.pow_pos.
  rewrite !Pos2Nat.inj_iter; generalize (Pos.to_nat r) as n; intro.
  revert p; induction n; auto.
  intros p; simpl; rewrite <-IHn; auto.
Qed.

Definition D_to_Q (d : D) :=
  Qmake (num d) (shift_pos (den d) 1).

Definition Dadd (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    if Pos.ltb y1 y2 then
      Dmake (Z.pow_pos 2 (y2 - y1) * x1 + x2) y2
    else if Pos.ltb y2 y1 then 
           Dmake (Z.pow_pos 2 (y1 - y2) * x2 + x1) y1
         else Dmake (x1 + x2) y1
  end.

Lemma Qdiv_mult (s q r : Q) :
  ~ s == 0 -> 
  (q / r) == (q * s) / (r * s).
Proof.
  intros H; unfold Qdiv.
  assert (q * s * /(r * s) == q * /r) as ->.
  { rewrite Qinv_mult_distr, (Qmult_comm (/r)), Qmult_assoc.
    rewrite <-(Qmult_assoc q), Qmult_inv_r, Qmult_1_r; auto.
    apply Qeq_refl. }
  apply Qeq_refl.
Qed.

Lemma Qdiv_1_r q : q / 1 == q.
Proof.
  unfold Qdiv, Qinv; simpl; rewrite Qmult_1_r.
  apply Qeq_refl.
Qed.

Lemma Zdiv_pos0 (x y : positive) : (Zpos (x~0) / Zpos (y~0) = Zpos x / Zpos y)%Z.
Proof.
  rewrite Pos2Z.inj_xO, (Pos2Z.inj_xO y).
  rewrite Zdiv_mult_cancel_l; auto.
  inversion 1.
Qed.  

Lemma Zpow_pos_2exp (x y : nat) :
  (y < x)%nat -> 
  Z.pow 2 (Z.of_nat (x - y)) = (Z.pow 2 (Z.of_nat x) / Z.pow 2 (Z.of_nat y))%Z.
Proof.
  intros H; rewrite <-!two_power_nat_equiv; unfold two_power_nat.
  revert y H; induction x; simpl.
  { destruct y; try solve[inversion 1]. }
  destruct y; simpl.
  { intros H; rewrite Zdiv_1_r; auto. }
  intros H.
  rewrite IHx.
  { rewrite Zdiv_pos0; auto. }
  apply lt_S_n; auto.
Qed.

Lemma Pos_iter_swap' T f g (r : T) (x : positive) :
  (forall t, f (g t) = t) -> 
  Pos.iter f (Pos.iter g r x) x = r.
Proof.
  rewrite 2!Pos2Nat.inj_iter.
  assert (H: exists y, Pos.to_nat x = Pos.to_nat y).
  { exists x; auto. }
  revert H; generalize (Pos.to_nat x) as n; intros n H.
  revert r; induction n; simpl; auto.
  intros r H2.
  destruct (Nat.eq_dec n 0).
  { subst n.
    simpl.
    rewrite H2; auto. }
  assert (H3: exists y, n = Pos.to_nat y).
  { exists (Pos.of_nat n).
    rewrite Nat2Pos.id; auto. }
  destruct H3 as [y H3].
  subst n.
  rewrite <-Pos2Nat.inj_iter.
  rewrite <-Pos.iter_swap.
  rewrite H2.
  rewrite Pos2Nat.inj_iter.
  apply IHn; auto.
  exists y; auto.
Qed.  

Lemma Pos_lt_Zpos_Zlt x y :  
  (x < y)%positive -> 
  (' x < ' y)%Z.
Proof.
  unfold Z.lt; simpl; rewrite <-Pos.ltb_lt.
  rewrite Pos.ltb_compare.
  destruct (Pos.compare x y); auto; try solve[inversion 1].
Qed.  

Lemma Zlt_le x y : (x < y -> x <= y)%Z.
Proof.
  unfold Z.le; intros H.
  generalize (Zlt_compare _ _ H).
  destruct (Z.compare x y); try solve[inversion 1|auto].
  intros _; inversion 1.
Qed.

Lemma Zpow_pos_div x y :
  (y < x)%positive -> 
  (Z.pow_pos 2 x # 1) * / (Z.pow_pos 2 y # 1) == Z.pow_pos 2 (x - y) # 1.
Proof.
  intros H; rewrite !Z.pow_pos_fold.
  assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
  { apply Pos2Z.inj_sub; auto. }
  rewrite Z.pow_sub_r; try omega.
  rewrite <-Z.pow_sub_r.
  { unfold Qmult, Qinv; simpl.
    assert (exists p, Z.pow_pos 2 y = Zpos p).
    { unfold Z.pow_pos.
      rewrite Pos2Nat.inj_iter.
      generalize (Pos.to_nat y); induction n.
      { simpl. exists 1%positive; auto. }
      simpl in IHn|-*.
      destruct IHn as [p H2]; rewrite H2; exists (p~0%positive); auto. }
    destruct H0 as [p H1]; rewrite H1; simpl.
    unfold Qeq; simpl; rewrite <-H1.
    rewrite Z.pos_sub_gt; auto.
    rewrite 2!Z.pow_pos_fold.
    assert (2 ^ ' (x - y) * 2 ^ ' y = 2 ^ ' x)%Z as ->.
    { assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
      { rewrite <-Z_pos_sub_gt.
        { rewrite <-Pos2Z.add_pos_neg.
          unfold Z.sub; auto. }
        rewrite Pos.gt_lt_iff; auto. }
      assert (Hbounds : (0 <= ' y <= ' x)%Z).
      { split.
        { apply Pos2Z.is_nonneg. }
        apply Zlt_le.
        apply Pos_lt_Zpos_Zlt; auto. }
      rewrite Z.pow_sub_r; auto; [|inversion 1].
      rewrite <-Z.shiftr_div_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_mul_pow2; [|apply Pos2Z.is_nonneg].
      rewrite <-Z.shiftl_1_l.
      rewrite Z.shiftr_shiftl_l; [|apply Pos2Z.is_nonneg].
      rewrite Z.shiftl_shiftl.
      { rewrite Z.sub_simpl_r; auto. }
      destruct Hbounds.
      apply Zle_minus_le_0; auto. }
    rewrite 2!Zmult_1_r; auto. }
  { inversion 1. }
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Zle, Z.compare; rewrite H; inversion 1. 
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Zle, Z.compare; rewrite H; inversion 1. 
Qed.

Lemma Qinv_neq (n : Q) : ~0 == n -> ~0 == / n.
Proof.
  unfold Qeq, Qinv; simpl.
  destruct (Qnum _); simpl; auto.
  { intros _ H.
    generalize (Pos2Z.is_pos (Qden n * 1)).
    rewrite <-H; inversion 1. }
  intros _ H.
  generalize (Zlt_neg_0 (Qden n * 1)).
  rewrite <-H; inversion 1.
Qed.  

Lemma Qdiv_neq_0 n m : ~n==0 -> ~m==0 -> ~(n / m == 0).
Proof.
  intros H H1 H2.
  unfold Qdiv in H2.
  apply Qmult_integral in H2; destruct H2; auto.
  assert (H2: ~0 == m).
  { intros H2; rewrite H2 in H1; apply H1; apply Qeq_refl. }
  apply (Qinv_neq _ H2); rewrite H0; apply Qeq_refl.
Qed.  

Lemma Qmake_neq_0 n m : (~n=0)%Z -> ~(n # m) == 0.
Proof.
  intros H; unfold Qeq; simpl; intros H2.
  rewrite Zmult_1_r in H2; subst n; apply H; auto.
Qed.

Lemma Zpow_pos_neq_0 n m : (n<>0 -> Z.pow_pos n m <> 0)%Z.
Proof.
  intros H0.
  unfold Z.pow_pos.
  apply Pos.iter_invariant.
  { intros x H H2.
    apply Zmult_integral in H2; destruct H2.
    { subst; apply H0; auto. }
    subst x; apply H; auto. }
  inversion 1.
Qed.

Lemma Zmult_pow_plus x y r :
  (r <> 0)%Z -> 
  x * inject_Z (Z.pow r ('y)) / inject_Z (Z.pow r ('y+'y)) ==
  x / inject_Z (Z.pow r ('y)).
Proof.
  intros H; unfold inject_Z.
  assert (Hy: (' y >= 0)%Z).
  { generalize (Pos2Z.is_nonneg y).
    unfold Z.le, Z.ge; intros H2 H3.
    destruct (Zle_compare 0 ('y)); auto. }
  rewrite Zpower_exp; auto.
  unfold Qdiv.
  rewrite <-Qmult_assoc.
  assert (r^('y) * r^('y) # 1 == (r^('y)#1) * (r^('y)#1)) as ->.
  { unfold Qmult; simpl; apply Qeq_refl. }
  rewrite Qinv_mult_distr.
  rewrite (Qmult_assoc (r^('y)#1)).
  rewrite Qmult_inv_r, Qmult_1_l.
  { apply Qeq_refl. }
  apply Qmake_neq_0; intros H2.
  apply (Zpow_pos_neq_0 _ _ H H2).
Qed.  

Lemma Dadd_ok d1 d2 :
  D_to_Q (Dadd d1 d2) == D_to_Q d1 + D_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold Qplus; simpl.
  rewrite !shift_pos_correct, Qmake_Qdiv, !Pos2Z.inj_mul, !shift_pos_correct.
  rewrite !Zmult_1_r, !inject_Z_plus, !inject_Z_mult.
  assert (inject_Z (Z.pow_pos 2 X) * inject_Z (Z.pow_pos 2 Z) =
          inject_Z (Z.pow_pos 2 (X + Z))) as ->.
  { rewrite <-inject_Z_mult.
    symmetry; rewrite !Zpower_pos_nat.
    rewrite Pos2Nat.inj_add, Zpower_nat_is_exp; auto. }
  destruct (Pos.ltb X Z) eqn:H.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 X))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 X)) ==
             inject_Z Y * inject_Z (Z.pow_pos 2 (Z - X)) + inject_Z W)) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-Qmult_assoc.
      assert ((Z.pow_pos 2 Z # 1) * / (Z.pow_pos 2 X # 1) ==
              Z.pow_pos 2 (Z - X) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_l.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 X)) ==
            inject_Z (Z.pow_pos 2 Z)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 X) ==
              inject_Z (Z.pow_pos 2 Z)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite (Qmult_comm (inject_Z (Z.pow_pos 2 X))).
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold D_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 Z = Z.pow_pos 2 Z * ' 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm; apply Qeq_refl; auto.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  destruct (Pos.ltb Z X) eqn:H'.
  { rewrite (Qdiv_mult (1 / inject_Z (Z.pow_pos 2 Z))).
    assert (((inject_Z Y * inject_Z (Z.pow_pos 2 Z) +
              inject_Z W * inject_Z (Z.pow_pos 2 X)) *
             (1 / inject_Z (Z.pow_pos 2 Z)) ==
             inject_Z Y + inject_Z W * inject_Z (Z.pow_pos 2 (X - Z)))) as ->.
    { unfold Qdiv; rewrite Qmult_1_l.
      rewrite Qmult_plus_distr_l.
      unfold inject_Z.
      rewrite <-(Qmult_assoc (W # 1)).
      assert ((Z.pow_pos 2 X # 1) * / (Z.pow_pos 2 Z # 1) ==
              Z.pow_pos 2 (X - Z) # 1) as ->.
      { rewrite Zpow_pos_div.
        apply Qeq_refl.
        rewrite <-Pos.ltb_lt; auto. }
      apply Qplus_inj_r.
      rewrite <-Qmult_assoc, Qmult_inv_r.
      { rewrite Qmult_1_r; apply Qeq_refl. }
      rewrite Zpower_pos_nat, Zpower_nat_Z.
      unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
      { omega. }
      omega. }
    assert (inject_Z (Z.pow_pos 2 (X + Z)) * (1 / inject_Z (Z.pow_pos 2 Z)) ==
            inject_Z (Z.pow_pos 2 X)) as ->.
    { unfold Qdiv.
      rewrite Qmult_assoc, Qmult_comm, Qmult_assoc.
      rewrite (Qmult_comm (/_)).
      assert (inject_Z (Z.pow_pos 2 (X + Z)) * / inject_Z (Z.pow_pos 2 Z) ==
              inject_Z (Z.pow_pos 2 X)) as ->.
      { rewrite Zpower_pos_is_exp, inject_Z_mult.
        rewrite <-Qmult_assoc, Qmult_inv_r.
        { rewrite Qmult_1_r; apply Qeq_refl. }
        unfold inject_Z; rewrite Zpower_pos_nat, Zpower_nat_Z.
        unfold Qeq; simpl; rewrite Zmult_1_r; apply Z.pow_nonzero.
        { omega. }
        omega. }
      rewrite Qmult_1_r; apply Qeq_refl. }
    unfold D_to_Q; simpl.
    rewrite <-inject_Z_mult, <-inject_Z_plus.
    assert (Z.pow_pos 2 X = Z.pow_pos 2 X * ' 1)%Z as ->.
    { rewrite Zmult_1_r; auto. }
    rewrite <-shift_pos_correct, <-Qmake_Qdiv.
    rewrite Zmult_comm, Z.add_comm; apply Qeq_refl.
    apply Qdiv_neq_0. { apply Q_apart_0_1. }
    unfold inject_Z; apply Qmake_neq_0.
    apply Zpow_pos_neq_0. inversion 1. }
  assert (H1: X = Z).
  { generalize H'; rewrite Pos.ltb_antisym.
    generalize H; unfold Pos.ltb, Pos.leb.
    destruct (X ?= Z)%positive eqn:H2; try solve[inversion 1|inversion 2].
    intros _ _.
    apply Pos.compare_eq; auto. }
  (* eq case *)
  subst Z; unfold D_to_Q; simpl; clear H H'.
  unfold Qdiv; rewrite Qmult_plus_distr_l.
  assert (inject_Z Y * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z Y / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }
  assert (inject_Z W * inject_Z (Z.pow_pos 2 X) *
          / inject_Z (Z.pow_pos 2 (X + X)) ==
          inject_Z W / inject_Z (Z.pow_pos 2 X)) as ->.
  { apply Zmult_pow_plus; inversion 1. }  
  unfold Qdiv; rewrite <-Qmult_plus_distr_l, Qmake_Qdiv, inject_Z_plus.
  unfold Qdiv; rewrite shift_pos_correct, Zmult_1_r; apply Qeq_refl.
Qed.

Definition Dmult (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    Dmake (x1 * x2) (y1 + y2)
  end.

Lemma shift_nat1_mult n m :
  (shift_nat n 1 * shift_nat m 1 = shift_nat n (shift_nat m 1))%positive.
Proof.
  induction n; simpl; auto.
  rewrite IHn; auto.
Qed.
 
Lemma Dmult_ok d1 d2 :
  D_to_Q (Dmult d1 d2) = D_to_Q d1 * D_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  unfold D_to_Q; simpl.
  unfold Qmult; simpl.
  rewrite !shift_pos_nat, Pos2Nat.inj_add, shift_nat_plus.
  rewrite shift_nat1_mult; auto.
Qed.

Definition Dopp (d : D) : D :=
  match d with
  | Dmake x y => Dmake (-x) y
  end.

Lemma Dopp_ok d : D_to_Q (Dopp d) = Qopp (D_to_Q d).
Proof.
  destruct d; simpl.
  unfold D_to_Q; simpl.
  unfold Qopp; simpl; auto.
Qed.

Definition Dsub (d1 d2 : D) : D := Dadd d1 (Dopp d2).

Lemma Dsub_ok d1 d2 :
  D_to_Q (Dsub d1 d2) == D_to_Q d1 - D_to_Q d2.
Proof.
  unfold Dsub.
  rewrite Dadd_ok.
  rewrite Dopp_ok.
  unfold Qminus; apply Qeq_refl.
Qed.  