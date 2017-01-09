Set Implicit Arguments.
Unset Strict Implicit.

Require Import FunctionalExtensionality ProofIrrelevance.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Section finiteIso.
  Context (T : Type) (R : finType).
  Variables (f : T -> R) (g : R -> T).
  Hypothesis fg_id : forall t, g (f t) = t.
  Hypothesis gf_id : forall r, f (g r) = r.  
  
  Lemma T_eqP : Equality.axiom (fun x y : T => f x == f y).
  Proof.
    move => x y; case He: (f x == f y).
    { constructor.
      suff: g (f x) = g (f y); first by rewrite 2!fg_id.
      by move: (eqP He) => ->. }
    constructor => Hf; subst x.
    by rewrite eq_refl in He.
  Qed.

  Definition T_eqMixin := EqMixin T_eqP.
  Canonical T_eqType := Eval hnf in EqType T T_eqMixin.
  
  Definition T_enum : seq T := map g (enum R).

  Lemma T_enumP : Finite.axiom T_enum.
  Proof.
    move => x; rewrite /T_enum; move: (@enumP R (f x)) => <-; rewrite count_map.
    have ->: Finite.enum R = enum R by rewrite enumT.
    apply: eq_in_count => y H.
    rewrite /preim /pred1 /=; apply/eqP.
    case H2: (y == f x).
    { by move: (eqP H2) => ->; rewrite fg_id. }
    by move => H3; rewrite -H3 gf_id eq_refl in H2.
  Qed.

  Lemma R_of_TK : cancel f g.
  Proof. by move => x; rewrite fg_id. Qed.

  Definition T_choiceMixin := CanChoiceMixin R_of_TK.
  Canonical T_choiceType := Eval hnf in ChoiceType T T_choiceMixin.
  Definition T_countMixin := CanCountMixin R_of_TK.
  Canonical T_countType := Eval hnf in CountType T T_countMixin.
  
  Definition T_finMixin := Eval hnf in FinMixin T_enumP.  
  Definition iso_finType := Eval hnf in FinType T T_finMixin.
End finiteIso.

Definition depfinfun (I : finType) (T_ : I -> finType) := 
  forall ix : I, T_ ix.

Lemma depfinfun_eq (I : finType) (T_ : I -> finType) (f g : depfinfun T_) :
  (forall x, f x = g x) -> f = g.
Proof.
  move => H; apply: functional_extensionality_dep.
  apply: H.
Qed.

Module Pkg. Section pkg.
  Variables (I : finType) (T_ : I -> finType).
  Definition t := { ix : I & T_ ix }.
  Definition mk (ix : I) (x : T_ ix) : t := existT _ ix x.
  Definition get1 (f : t) : I := projT1 f.
  Definition get2 (f : t) : T_ (get1 f) := projT2 f.
End pkg. End Pkg.

Module Dynamic. Section dynamic.
  Variable I : finType.
  Variable T_ : I -> finType.
  Definition inv (f : {ffun I -> Pkg.t T_}) : bool := 
    [forall ix : I, projT1 (f ix) == ix].
  Definition t := {f : {ffun I -> Pkg.t T_} | inv f}.

  Lemma ext (f1 f2 : t) : projT1 f1 = projT1 f2 -> f1 = f2.
  Proof.
    case: f1 => x1 p1; case: f2 => x2 p2 /= H; subst x1.
    f_equal; apply: proof_irrelevance. (*FIXME: not strictly necessary here*)
  Qed.
  
  Definition lookup_lem (ix : I) (f : t) : Pkg.get1 ((projT1 f) ix) = ix.
  Proof.
    case: f => x p; rewrite /Pkg.get1 /=; case: x p => /= tx.
    by move/forallP/(_ ix)/eqP.
  Qed.

  Lemma T_eq x y : x = y -> T_ x = T_ y.
  Proof. by move => ->. Qed.
  
  Definition lookup (ix : I) (f : t) : T_ ix :=
    eq_rect _ _ (Pkg.get2 ((projT1 f) ix)) _ (T_eq (lookup_lem ix f)).
End dynamic. End Dynamic.

Section iso.
  Variable I : finType.
  Variable T_ : I -> finType.

  Program Definition dep2dynamic (f : depfinfun T_) : Dynamic.t T_ :=
    exist _ (finfun (fun ix => Pkg.mk (f ix))) _.
  Next Obligation. apply/forallP => ix; rewrite ffunE //. Qed.

  Definition dynamic2dep (f : Dynamic.t T_) : depfinfun T_ :=
    fun ix => Dynamic.lookup ix f.

  Lemma cancel1 f : dynamic2dep (dep2dynamic f) = f.
  Proof.
    apply: depfinfun_eq => y.
    rewrite /dynamic2dep /dep2dynamic /Dynamic.lookup /=.
    move: (Dynamic.T_eq _ _) => pf2; rewrite ffunE in pf2|-* => /=.
    move: pf2. move: (f y). move: (T_ y). clear f y. move => U f pf2.
    have ->: pf2 = erefl by apply: proof_irrelevance.
    by [].
  Qed.      

  Lemma cancel2 g : dep2dynamic (dynamic2dep g) = g.
  Proof.
    apply: Dynamic.ext.
    rewrite /dynamic2dep /dep2dynamic /Dynamic.lookup /=; apply/ffunP => x.
    rewrite ffunE; move: (Dynamic.T_eq _ _).
    case: g => /= g Hinv; rewrite /Pkg.get1.
    move: Hinv; move/forallP/(_ x)/eqP.
    case: (g x) => y p /= Heq; subst y => /= H.
    have ->: H = erefl by apply: proof_irrelevance.
    by []. 
  Qed.

  Canonical depfinfun_finType :=
    @iso_finType
      (depfinfun T_) [finType of Dynamic.t T_]
      _ _
      cancel1 cancel2.
End iso.

Section depfintype_check.
  Variable N : nat.
  Variable T : 'I_N -> finType.
  Definition ty := depfinfun T.
  Check [finType of ty].
  Check enum [finType of ty].
End depfintype_check.
