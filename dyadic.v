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

Lemma inject_Z_div x y : inject_Z (x / ' y) == inject_Z x / inject_Z (' y).
Proof.
  rewrite <-Qmake_Qdiv.
  unfold inject_Z.
  unfold Qeq; simpl.
Admitted. (*TODO: Not sure this is true!*)

Lemma Qmult_div_lem x y : (x # 1) * / (y # 1) == (x / y) # 1.
Proof.
  unfold Qinv.
  destruct (Qnum _) eqn:H.
  { simpl in H; subst y.
    rewrite Qmult_0_r, Zdiv_0_r; apply Qeq_refl. }
  { simpl in H|-*; subst y.
    unfold Qmult; simpl.
    rewrite Zmult_1_r.
    rewrite !Qmake_Qdiv.
    assert (inject_Z 1 = 1%Q) as ->.
    { auto. }
    rewrite Qdiv_1_r.
    unfold inject_Z.
    unfold Qdiv, Qinv, Qmult; simpl.
    unfold Qeq; simpl.
    rewrite 2!Zmult_1_r.
Admitted.    

Lemma Zpow_pos_div x y :
  (y < x)%positive -> 
  (Z.pow_pos 2 x # 1) * / (Z.pow_pos 2 y # 1) == Z.pow_pos 2 (x - y) # 1.
Proof.
  intros H; rewrite !Z.pow_pos_fold.
  assert (Zpos (x - y) = (Zpos x - Zpos y)%Z) as ->.
  { apply Pos2Z.inj_sub; auto. }
  rewrite Z.pow_sub_r; try omega.
  rewrite Qmult_div_lem; apply Qeq_refl.
  split.
  { apply Pos2Z.is_nonneg. }
  unfold Zle, Z.compare; rewrite H; inversion 1. 
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
    admit. }
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
    admit. }
  assert (H1: X = Z).
  { generalize H'; rewrite Pos.ltb_antisym.
    generalize H; unfold Pos.ltb, Pos.leb.
    destruct (X ?= Z)%positive eqn:H2; try solve[inversion 1|inversion 2].
    intros _ _.
    apply Pos.compare_eq; auto. }
  subst Z; unfold D_to_Q; simpl; clear H H'.
  admit.
Admitted.

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