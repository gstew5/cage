Require Import ZArith PArith QArith.

Record D : Set :=
  Dmake { num : Z;
          den : positive }.

Definition pow_pos (p r : positive) : positive :=
  Pos.iter (Pos.mul p) 1%positive r.

Lemma pow_pos_plus (p r s : positive) :
  pow_pos p (r + s) = (pow_pos p r * pow_pos p s)%positive.
Admitted.

Definition D_to_Q (d : D) :=
  Qmake (num d) (pow_pos 2 (den d)).

Definition Dadd (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    if Pos.ltb y1 y2 then
      Dmake (Z.pow_pos 2 (y2 - y1) * x1 + x2) y2
    else 
      Dmake (Z.pow_pos 2 (y1 - y2) * x1 + x2) y1
  end.

Lemma Zpower_nat_is_exp' n m z :
  Zpower_nat z (n - m) = (Zpower_nat z n / Zpower_nat z m)%Z.
Admitted.                           

Lemma Dadd_ok d1 d2 :
  D_to_Q (Dadd d1 d2) = D_to_Q d1 + D_to_Q d2.
Proof.
  destruct d1, d2; simpl.
  generalize den0 as X; intro.
  generalize num0 as Y; intro.
  generalize den1 as Z; intro.
  generalize num1 as W; intro.
  destruct (Pos.ltb X Z) eqn:H.
  { unfold D_to_Q; simpl.
    rewrite Zpower_pos_nat.
    rewrite nat_of_P_minus_morphism.
    { rewrite Zpower_nat_is_exp'.
      unfold pow_pos.
      
      admit. }
    apply nat_of_P_gt_Gt_compare_complement_morphism.
    rewrite Pos.ltb_lt in H.
    rewrite Pos2Nat.inj_lt in H.
    omega. }
  admit.
Admitted.    

Definition Dmult (d1 d2 : D) : D :=
  match d1, d2 with
  | Dmake x1 y1, Dmake x2 y2 =>
    Dmake (x1 * x2) (y1 + y2)
  end.

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
  rewrite pow_pos_plus; auto.
Qed.