Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith Reals Rpower Ranalysis Fourier.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import numerics.

Delimit Scope R_scope with R.

Fixpoint big_sum (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c + big_sum cs' f)%R
  else 0%R.

Lemma big_sum_nmul (T : Type) (cs : seq T) (f : T -> R) :
  (big_sum cs (fun c => - f c) = - big_sum cs [eta f])%R.
Proof.
  elim: cs=> /=; first by rewrite Ropp_0.
    by move=> a l IH; rewrite Ropp_plus_distr IH.
Qed.      

Lemma big_sum_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_sum cs f = big_sum cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_sum_scalar T (cs : seq T) r f :
  (big_sum cs (fun c => r * f c) = r * big_sum cs (fun c => f c))%R.
Proof.
  elim: cs=> /=; first by rewrite Rmult_0_r.
    by move=> a l IH; rewrite IH /=; rewrite Rmult_plus_distr_l.
Qed.      

Fixpoint big_product (T : Type) (cs : seq T) (f : T -> R) : R :=
  if cs is [:: c & cs'] then (f c * big_product cs' f)%R
  else 1%R.

Lemma big_product_ext T (cs cs' : seq T) f f' :
  cs = cs' -> f =1 f' -> big_product cs f = big_product cs' f'.
Proof. by move=> <- H; elim: cs=> //= a l ->; f_equal; apply: H. Qed.

Lemma big_product_ge0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (0 <= big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rle_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  rewrite H2; apply: Rmult_le_compat.
  by apply: Rle_refl.
  by apply: Rle_refl.
  by apply: H; rewrite in_cons; apply/orP; left.
  apply: IH=> c H3; apply: H.
  by rewrite in_cons; apply/orP; right.
Qed.

Lemma big_product_gt0 (T : eqType) (cs : seq T) (f : T -> R) :
  (forall c, c \in cs -> 0 < f c)%R ->
  (0 < big_product cs f)%R.
Proof.
  elim: cs=> /=.
  { move=> _; apply: Fourier_util.Rlt_zero_1. }
  move=> a l IH H.
  have H2: (0 = 0 * 0)%R by rewrite Rmult_0_l.
  apply: Rmult_lt_0_compat.
  by apply: H; rewrite in_cons; apply/orP; left.
  by apply: IH=> c H3; apply: H; rewrite in_cons; apply/orP; right.
Qed.      
  
Lemma ln_big_product_sum (T : eqType) (cs : seq T) (f : T -> R) :
  (forall t : T, 0 < f t)%R -> 
  ln (big_product cs f) = big_sum cs (fun c => ln (f c)).
Proof.
  elim: cs=> /=; first by rewrite ln_1.
  move=> a l IH H; rewrite ln_mult=> //; first by rewrite IH.
    by apply: big_product_gt0.
Qed.    
    
Lemma big_product_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> 0 <= f c)%R ->
  (forall c, c \in cs -> 0 <= g c)%R ->     
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_product cs f <= big_product cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _ _ _; apply: Rle_refl. }
  move=> a l IH H1 H2 H3; apply Rmult_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
  { apply: big_product_ge0.
      by move=> c H4; apply: H1; rewrite in_cons; apply/orP; right. }
  { by apply: H3; rewrite in_cons; apply/orP; left. }
  apply: IH.
  { by move=> c H; apply: H1; rewrite in_cons; apply/orP; right. }
  { by move=> c H; apply: H2; rewrite in_cons; apply/orP; right. }
    by move=> c H; apply: H3; rewrite in_cons; apply/orP; right.
Qed.    

Lemma big_sum_le (T : eqType) (cs : seq T) (f : T -> R) g :
  (forall c, c \in cs -> f c <= g c)%R -> 
  (big_sum cs f <= big_sum cs g)%R.
Proof.
  elim: cs=> //=.
  { move=> _; apply: Rle_refl. }
  move=> a l IH H1; apply Rplus_le_compat.
  { by apply: H1; rewrite in_cons; apply/orP; left. }
    by apply: IH=> c H; apply: H1; rewrite in_cons; apply/orP; right.
Qed.    

Lemma rat_to_R_prod T (cs : seq T) (f : T -> rat) :
  rat_to_R (\prod_(c <- cs) (f c)) =  
  big_product cs (fun c => (rat_to_R (f c)))%R.
Proof.
  elim: cs=> //=; first by rewrite big_nil rat_to_R1.
  move=> a' l IH; rewrite big_cons.
  rewrite rat_to_R_mul IH.
    by f_equal; rewrite rat_to_R_plus rat_to_R_opp rat_to_R_mul.
Qed.    
