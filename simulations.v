Set Implicit Arguments.

Require Import Wellfounded Lexicographic_Product.

Class hasInit (X : Type) : Type := init : X -> Prop.
Class hasFinal (X : Type) : Type := final : X -> Prop.
Class hasStep (X : Type) : Type := step : X -> X -> Prop.
Class semantics {X} `{hasInit X} `{hasFinal X} `{hasStep X}.

Class hasOrd (X : Type) : Type := ord : X -> X -> Prop.
Class hasTransOrd {X} `{hasOrd X} :=
  transitive : forall x y z : X, ord x y -> ord y z -> ord x z.
Class hasWellfoundedOrd {X} `{hasTransOrd X} :=
  well_founded : well_founded ord.

Instance hasOrdLex {X Y} `{hasOrd X} `{hasOrd Y} : hasOrd (X * Y) :=
  fun xy' xy =>
    let (x,y) := xy in
    let (x',y') := xy' in
    ord x' x \/ x=x' /\ ord y' y.

Instance hasTransOrdLex
         {X Y}
         `{hasTransOrd X}
         `{hasTransOrd Y}
  : hasTransOrd (X:=(X * Y)).
Proof.
  intros [x1 x2] [y1 y2] [z1 z2]; unfold ord; simpl.
  intros [A1|[A1 A2]].
  { intros [B1|[B1 B2]].
    { left; eapply transitive; eauto. }
    subst z1; left; auto. }
  subst y1; intros [B1|[B1 B2]].
  { left; auto. }
  right; split; auto.
  eapply transitive; eauto.
Qed.

Instance hasWellfoundedOrdLex
         {X Y}
         `{hasWellfoundedOrd X}
         `{hasWellfoundedOrd Y}
  : hasWellfoundedOrd (X:=(X * Y)).
Proof.
  set (A := X).
  set (B (_ : A) := Y).
  set (R1 := fun (xy' xy : {x : A & B x}) =>
               ord (projT1 xy',projT2 xy') (projT1 xy,projT2 xy)).
  assert (C: Wf.well_founded R1).
  { eapply wf_incl; [|apply wf_lexprod; [apply H1|]; intros x; apply H4].
    intros [x' y'] [x y]; unfold R1; simpl.
    intros [A1|[A1 A2]].
    { apply Relation_Operators.left_lex; auto. }
    subst x'; apply Relation_Operators.right_lex; auto. }
  unfold hasWellfoundedOrd, Wf.well_founded in C|-*.
  intros [a b]; specialize (C (existT _ a b)).
  set (P := fun (xy : {x : A & B x}) => Acc ord (projT1 xy,projT2 xy)).
  change (P (existT _ a b)); apply Acc_ind with R1; auto.
  intros [x y] A1 A2; constructor; intros [x' y'] B1.
  change (P (existT _ x' y')); apply A2; auto.
Qed.  

Fixpoint stepN {X} `{semantics X} (n : nat) : X -> X -> Prop :=
  match n with
  | O => fun x y => x = y
  | S n' => fun x z => exists y, step x y /\ stepN n' y z
  end.

Definition step_plus {X} `{semantics X} : X -> X -> Prop :=
  fun x y => exists n, stepN (S n) x y.

Lemma stepN_trans {X} `{semantics X} n m x x'' x' :
  stepN n x x'' ->
  stepN m x'' x' ->
  stepN (n + m) x x'.
Proof.
  revert m x x'' x'; induction n.
  { intros m x x'' x' <-; auto. }
  intros m x x'' x' [x2 [A1 A2]] B.
  exists x2; split; auto.
  eapply IHn; eauto.
Qed.  

Lemma step_plus_trans {X} `{semantics X} x x'' x' :
  step_plus x x'' ->
  step_plus x'' x' ->
  step_plus x x'.
Proof.
  intros [n1 A1].
  intros [n2 A2].
  exists (n1 + S n2); simpl.
  generalize (stepN_trans _ _ _ _ _ A1 A2); auto.
Qed.  

Record simulation
       {S T ORD}
       `{sem_S : semantics S}
       `{sem_T : semantics T}
       `{ord_S : hasWellfoundedOrd ORD} :=
  mkSimulation {
      match_states : ORD -> S -> T -> Prop;
      init_diagram :
        forall s,
          init s ->
          (exists t, init t) /\
          (forall t, init t -> exists x, match_states x s t);
      final_diagram : forall x s t, match_states x s t -> final s -> final t;
      step_diagram : forall x s t,
          match_states x s t ->
          forall s',
            step s s' ->
            exists x',
            (ord x' x /\ match_states x' s' t) \/
            (exists t', step_plus t t' /\ match_states x' s' t')            
    }.

Lemma step_plus_diagram 
      {S T ordS}
      `{sem_S : semantics S}
      `{sem_T : semantics T}
      `{ord_S' : hasWellfoundedOrd ordS}
      `(sim_ST : simulation (ORD:=ordS) (sem_S:=sem_S) (sem_T:=sem_T))
  : forall x s t s',
    match_states sim_ST x s t ->
    step_plus s s' ->
    exists x',
      (ord x' x /\ match_states sim_ST x' s' t) \/
      (exists t', step_plus t t' /\ match_states sim_ST x' s' t').
Proof.
  intros x s t s' Hmatch [n Hstep]; revert x s t s' Hmatch Hstep.
  induction n.
  { intros x s t s' Hmatch [s'' [A1 A2]]; simpl in A2; subst.
    destruct (step_diagram sim_ST x s t Hmatch) with s'; auto.
    rename x0 into x'; destruct H7 as [[B1 B2]|[t' [B1 B2]]].
    { exists x'; left; split; auto. }
    exists x'; right; exists t'; split; auto. }
  intros x s t s' Hmatch [s2 [A1 [s3 [A2 A3]]]].
  destruct (step_diagram sim_ST x s t Hmatch) with s2; auto.
  rename x0 into x2; destruct H7 as [[B1 B2]|[t2 [B1 B2]]].
  assert (A4: stepN (Datatypes.S n) s2 s').
  { exists s3; split; auto. }
  { generalize (IHn _ _ _ _ B2 A4); intros [x' [[C1 C2]|[t' [C1 C2]]]].
    { exists x'; left; split; auto; apply transitive with x2; auto. }
    exists x'; right; exists t'; split; auto. }
  assert (A4: stepN (Datatypes.S n) s2 s').
  { exists s3; split; auto. }
  generalize (IHn _ _ _ _ B2 A4); intros [x' [[C1 C2]|[t' [C1 C2]]]].
  { exists x'; right; exists t2; split; auto. }
  exists x'; right; exists t'; split; auto.
  eapply step_plus_trans; eauto.
Qed.  

Lemma simulation_trans
      {S T R ordS ordT}
      `{sem_S : semantics S}
      `{sem_T : semantics T}
      `{sem_R : semantics R}
      `{ord_S' : hasWellfoundedOrd ordS}
      `{ord_T' : hasWellfoundedOrd ordT}
      `(sim_ST : simulation (ORD:=ordS) (sem_S:=sem_S) (sem_T:=sem_T))
      `(sim_TR : simulation (ORD:=ordT) (sem_S:=sem_T) (sem_T:=sem_R))
  : simulation (ORD:=(ordT*ordS)) (sem_S:=sem_S) (sem_T:=sem_R).
Proof.
  refine
    (mkSimulation (ORD:=(ordT*ordS))
       sem_S
       _
       (fun (x : (ordT * ordS)) (s : S) (r : R) =>
          exists t : T, match_states sim_ST (snd x) s t /\ match_states _ (fst x) t r) _ _ _).
  { (* init *)
    intros s A; destruct (init_diagram sim_ST) with s as [B1 B2]; auto.
    destruct B1 as [t B1].
    destruct (B2 t B1) as [x B3].
    destruct (init_diagram sim_TR) with t as [C1 C2]; auto.
    destruct C1 as [r C1].
    destruct (C2 r C1) as [x' C3].
    split. { exists r; auto. }
    intros r' D.
    destruct (C2 _ D) as [x'' E].
    exists (x'',x); exists t; split; auto.
    apply E. }
  { (* final *)
    intros [x y] s r [t [M1 M2]] F1.
    apply (final_diagram sim_TR) with x t; [apply M2|].
    eapply (final_diagram sim_ST); eauto. }
  intros [x y] s r [t [M1 M2]] s' Hstep.
  destruct (step_diagram sim_ST y s t M1) with s'; auto.
  rename x0 into y'.
  destruct H12 as [[A1 A2]|[t' [A1 A2]]].
  { exists (x, y'); left; split; auto.
    { unfold ord, hasOrdLex; right; split; auto. }
    exists t; split; auto. }
  generalize (step_plus_diagram sim_TR _ _ M2 A1).
  intros [x' [[B1 B2]|[r' [B1 B2]]]].
  { exists (x', y'); left; split; auto.
    left; auto.
    exists t'; split; auto. }
  exists (x',y'); right; exists r'; split; auto.
  exists t'; split; auto.
Qed.  
