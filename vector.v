Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii ProofIrrelevance List Permutation.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import strings compile orderedtypes dyadic numerics.

(** Dyadic-valued sparse vectors, implemented as balanced binary trees *)

Module Type PAYLOAD.
  Parameter t : Type. (* the low-level type *)
  Parameter t0 : t.   (* the "unit" value of type t *)
  Parameter eq0 : t -> bool.
  Parameter eq0P : forall x, reflect (x = t0) (eq0 x).
  Parameter u : Type. (* the high-level type *)
  (* one half of a bijection *)    
  Parameter u_of_t : t -> u.
  Parameter t_of_u : u -> t.
  Parameter t_of_u_t : forall t, t_of_u (u_of_t t) = t.
End PAYLOAD.  

Module Vector (B : BOUND) (P : PAYLOAD).
  Module Ix := MyOrdNatDepProps B. (* the indices *)
  Module M := Make Ix.             (* sparse maps *)
  Module MFacts := Facts M.
  Module MProps := Properties M.
  Notation n := B.n.          (* the dimensionality *)
  Definition t := (M.t P.t).  (* the type of computable vectors *)

  (** [SPARSITY INVARIANT]: 
      ~~~~~~~~~~~~~~~~~~~~~ 
      The map contains no key-value pairs (i,p) s.t. p = P.t0. That is, 
      it only implicitly represents keys that map to the zero of the 
      payload domain.
    *)

  Definition nonzero (p : P.t) : bool := ~~(P.eq0 p).

  Definition sparse (m : t) := forall i y, M.find i m = Some y -> nonzero y.

  (* operations *)
  Definition get (i : Ix.t) (m : t) : P.t :=
    match M.find i m with
    | None => P.t0
    | Some p => p
    end.

  (* update i -> p; maintains [SPARSITY_INVARIANT] *)
  Definition set (i : Ix.t) (p : P.t) (m : t) : t :=
    if P.eq0 p then M.remove i m
    else M.add i p m.

  (* assumes f P.t0 = P.t0 *)
  Definition map0 (f : P.t -> P.t) (m : t) : t :=
    M.map f m.

  (* assumes f i P.t0 t = t *)  
  Definition fold0 T (f : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
    M.fold f m t0.

  (* a slow fold0 that doesn't assume f i P.t0 t = t *)
  Definition foldr T (f : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
    List.fold_right (fun ix acc => f ix (get ix m) acc) t0 (enumerate Ix.t).
  
  (* does any (i, p) pair satisfy f? if so, which one? *)
  Fixpoint any_rec (f : Ix.t -> P.t -> bool) (m : t) (l : list Ix.t) : option (Ix.t * P.t) :=
    match l with
    | nil => None
    | i :: l' =>
      let p := get i m in 
      if f i p then Some (i, p)
      else any_rec f m l'
    end.
  
  Definition any (f : Ix.t -> P.t -> bool) (m : t) : option (Ix.t * P.t) :=
    match List.find (fun i => f i (get i m)) (enumerate Ix.t) with
    | None => None
    | Some ix => Some (ix, get ix m)
    end.

  (* construct a vector from list of ordered pairs l *)
  Definition of_list_INTERNAL (l : list (Ix.t * P.t)) : t :=
    MProps.of_list l.

  (* same as of_list_INTERNAL but filters out pairs (i,p) 
     s.t. p = P.t0, thus maintaining the [SPARSITY_INVARIANT] *)
  Definition of_list (l : list (Ix.t * P.t)) : t :=
    of_list_INTERNAL (List.filter (fun p : (Ix.t*P.t) => nonzero p.2) l).
  
  (* construct a vector from function f *)
  Definition of_fun (f : Ix.t -> P.t) : t :=
    of_list (List.map (fun ix => (ix, f ix)) (enumerate Ix.t)).

  (* SPARSITY PROOFS *)
  Definition mk_sparse (m : t) : t := of_fun (fun ix => get ix m).

  Lemma mk_sparse_sparse m : sparse (mk_sparse m).
  Proof.
    rewrite /mk_sparse /sparse /of_fun /of_list => i t.
    rewrite /of_list_INTERNAL /MProps.of_list.
    rewrite -MProps.F.find_mapsto_iff MProps.F.elements_mapsto_iff.
    elim: (enumerate Ix.t) => //=.
    { rewrite MProps.elements_empty; inversion 1. }
    move => a l /= IH.
    case H: (nonzero (get a m)) => //=.
    rewrite /MProps.uncurry /= => H2.
    move: H2; rewrite -MFacts.elements_mapsto_iff.
    rewrite MProps.F.add_mapsto_iff; case.
    { by case => H2 H3; rewrite H3 in H. }
    case => H2; rewrite MFacts.elements_mapsto_iff => H3.
    by apply: IH.
  Qed.    

  Lemma set_sparse m i t : sparse m -> sparse (set i t m).
  Proof.
    rewrite /sparse => H j k; rewrite /set; case: (P.eq0P t).
    { move => H2.
      case: (M.E.eq_dec i j) => H3.
      { rewrite MProps.F.remove_eq_o => //. }
      rewrite MProps.F.remove_neq_o => //; apply: H. }
    move => H2; case: (M.E.eq_dec i j) => H3.
    { rewrite MProps.F.add_eq_o => //; inversion 1; subst.
      apply/negP => H4; apply: H2; case: (P.eq0P k) H4 => //. }
    by rewrite MProps.F.add_neq_o => //; apply: H.
  Qed.    

  (* map0 is only sparse if (f t = P.t0 -> t = P.t0) *)
  Lemma map0_sparse m f :
    (forall t, f t = P.t0 -> t = P.t0) ->
    sparse m ->
    sparse (map0 f m).
  Proof.
    move => pf; rewrite /sparse /map0 => H i t; move: (H i t) => H' H2.
    rewrite MFacts.map_o /option_map in H2; move: H' H2.
    case: (M.find i m) => // a H' H2; inversion H2; subst; move {H2}.
    move: (pf a); case: (P.eq0P (f a)).
    { move => H3; move/(_ H3) => H4; subst a; elimtype False.
      by rewrite H3 /nonzero /= in H'; move: (H' erefl); case: (P.eq0P P.t0). }
    by move => H2 H3; apply/negP; move: H2; case: (P.eq0P (f a)).
  Qed.    
  
  (* REFINEMENT PROOFS *)
  Definition ty := {ffun 'I_n -> P.u}. (* high-level vectors *)

  Definition upd i p (f : ty) : ty :=
    [ffun i' => if i == i' then p else f i'].
  
  Lemma Ix_of_Ordinal_lem x :
    (x < n)%N -> 
    (N.to_nat (N.of_nat x) < n)%N.
  Proof. by rewrite Nat2N.id. Qed.
  
  Definition Ix_of_Ordinal (i : 'I_n) : Ix.t :=
    match i with
    | Ordinal x pf => @Ix.mk (N.of_nat x) (Ix_of_Ordinal_lem pf)
    end.
  
  Definition Ordinal_of_Ix (i : Ix.t) : 'I_n :=
    @Ordinal n (N.to_nat i.(Ix.val)) (Ix.pf i).

  Lemma Ix_of_Ordinal_Ix i : Ix_of_Ordinal (Ordinal_of_Ix i) = i.
  Proof.
    case: i => v pf /=.
    move: (Ix_of_Ordinal_lem _) => pf1; move: pf => pf2.
    move: pf1 pf2; rewrite N2Nat.id => pf1 pf2.
    f_equal.
    apply: proof_irrelevance.
  Qed.

  Lemma Ordinal_of_Ix_Ordinal i : Ordinal_of_Ix (Ix_of_Ordinal i) = i.
  Proof.
    case: i => m pf /=; rewrite /Ordinal_of_Ix /=.
    move: (Ix_of_Ordinal_lem _) => pf1; move: pf => pf2; move: pf1 pf2.
    rewrite Nat2N.id => pf1 pf2.
    f_equal.
    apply: proof_irrelevance.
  Qed.    

  (* the representation invariant *)
  Definition match_vecs (v : t) (f : ty) : Prop :=
    forall i : Ix.t, get i v = P.t_of_u (f (Ordinal_of_Ix i)).

  Section refinement_lemmas.
    Variables (v : t) (f : ty) (pf : match_vecs v f).

    Lemma match_vecs_get i :
      get i v = P.t_of_u (f (Ordinal_of_Ix i)).
    Proof. by apply: pf. Qed.

    Lemma match_vecs_set i p :
      match_vecs (set i p v) (upd (Ordinal_of_Ix i) (P.u_of_t p) f).
    Proof.
      move => j; rewrite /upd ffunE /set /get.
      case Heq: (P.eq0 p). (*P.t0 = p*)
      { move: (P.eq0P _ Heq) => <-.
        case: (Ix.eq_dec i j) => [px|px].
        { move: px; rewrite -Ix.eqP => H; rewrite H MProps.F.remove_eq_o; last first.
        { apply: N.eq_refl. }
        by subst i; rewrite eq_refl P.t_of_u_t. }
        have ->: (Ordinal_of_Ix i == Ordinal_of_Ix j = false).
        { case E: (Ordinal_of_Ix i == Ordinal_of_Ix j) => //.
          move: (eqP E) => F; elimtype False; apply: px.
          clear - E; move: E; case: i => i pfi; case: j => j pfj.
          rewrite /Ordinal_of_Ix /=; move/eqP; case; rewrite /Ix.eq /=.
          apply: N2Nat.inj. }
        rewrite MProps.F.remove_neq_o; last first.
        { move => H; apply: px.
          by case: i H => x pfx /=; case: j => y pfy /=. }
        by move: (P.eq0P _ Heq) => ->; apply: pf. }
      case: (Ix.eq_dec i j) => [px|px]. (*P.t0 <> p*)
      { move: px; rewrite -Ix.eqP => H; rewrite H MProps.F.add_eq_o; last first.
        { apply: N.eq_refl. }
        by subst i; rewrite eq_refl P.t_of_u_t. }
      have ->: (Ordinal_of_Ix i == Ordinal_of_Ix j = false).
      { case E: (Ordinal_of_Ix i == Ordinal_of_Ix j) => //.
        move: (eqP E) => F; elimtype False; apply: px.
        clear - E; move: E; case: i => i pfi; case: j => j pfj.
        rewrite /Ordinal_of_Ix /=; move/eqP; case; rewrite /Ix.eq /=.
        apply: N2Nat.inj. }
      rewrite MProps.F.add_neq_o; last first.
      { move => H; apply: px.
        by case: i H => x pfx /=; case: j => y pfy /=. }
      apply: pf.
    Qed.

    Lemma match_vecs_map0 (g : P.t -> P.t) (pf_g : g P.t0 = P.t0) :
      let g' := fun u => P.u_of_t (g (P.t_of_u u)) in
      match_vecs (map0 g v) [ffun i : 'I_n => g' (f i)].
    Proof.
      rewrite /map0 => j; rewrite ffunE /get MProps.F.map_o.
      case E: (M.find _ _) => /= [d|].
      { by move: (pf j) => <-; f_equal; f_equal; rewrite /get E P.t_of_u_t. }
      move: (pf j); rewrite /get E => H.
      by rewrite P.t_of_u_t -H pf_g.
    Qed.

    Lemma match_vecs_foldr
          T (tx : T) (g : Ix.t -> P.t -> T -> T)
          (pf_g : forall i t, g i P.t0 t = t) :
      let g' := fun i t => g (Ix_of_Ordinal i) (P.t_of_u (f i)) t in
      foldr g v tx =
      List.fold_right g' tx [seq (Ordinal_of_Ix ix) | ix <- enumerate Ix.t].
    Proof.
      rewrite /foldr; move: (enumerate Ix.t) => l.
      elim: l tx => // a l IH /= tx; f_equal => //.
      case: a => av apf; move: (Ix_of_Ordinal_lem _); rewrite N2Nat.id => pfix /=.
      by f_equal; apply: proof_irrelevance.
    Qed.    

    (* foldr and fold0 are equivalent assuming the composition operator is 
       symmetric, associative, and preserves zeros *)
    
    Definition foldr_aux1 T (g : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
      List.fold_right
        (fun ix acc => g ix (get ix m) acc) t0
        (List.filter (fun i => nonzero (get i m)) (enumerate Ix.t)).        

    Lemma foldr_foldr_aux1
          T (tx : T) (g : Ix.t -> P.t -> T -> T)
          (pf_g : forall i t, g i P.t0 t = t) :
      foldr g v tx = foldr_aux1 g v tx.
    Proof.
      rewrite /foldr /foldr_aux1; move: (enumerate Ix.t) => l.
      elim: l tx => // a l IH tx /=; case H: (nonzero (get a v)) => /=.
      { f_equal; apply: IH. }
      have H2: (get a v = P.t0).
      { move: H; rewrite /nonzero => H.
        have H2: ~~ ~~ (P.eq0 (get a v)) by rewrite H.
        by rewrite negb_involutive in H2; move: (P.eq0P _ H2). }
      rewrite H2 pf_g; apply: IH.
    Qed.

    Definition foldr_aux2 T (g : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
      List.fold_right
        (fun ix acc => g ix (get ix m) acc) t0
        (map fst (M.elements m)).

    Lemma foldr_permute
          (g : P.t -> P.t -> P.t)
          (gcom : forall t1 t2, g t1 t2 = g t2 t1)
          (gassoc : forall t1 t2 t3, g t1 (g t2 t3) = g (g t1 t2) t3)
          l1 l2 :
      Permutation l1 l2 ->
      let g' := (fun ix : Ix.t => [eta g (get ix v)]) in 
      List.fold_right g' P.t0 l1 = List.fold_right g' P.t0 l2.
    Proof.
      elim => //; first by move => x l l' H /= ->.
      { move => x y l /=; move: (fold_right _ _ _) => z.
        by rewrite [g (get _ _) (g _ _)]gcom -[g (g _ _) _]gassoc [g z _]gcom. }
      by move => l l' l'' H H2 H3 H4 g'; rewrite H2 H4.
    Qed.

    Lemma In_elements_find_Some_get x : 
      In x [seq i.1 | i <- M.elements (elt:=P.t) v] ->
      M.find x v = Some (get x v).
    Proof.
      rewrite -MProps.F.find_mapsto_iff => H.
      rewrite /get; apply: M.elements_2.
      rewrite MFacts.elements_o.
      elim: (M.elements _) H => // [][]k a l IH /=.
      rewrite /MFacts.eqb; case: (M.E.eq_dec x k) => //.
      { move => H _; constructor; constructor => //. }
      move => H; case.
      { by move => H2; subst x; elimtype False; apply: H. }
      move => H2; move: (IH H2).
      have H3: findA (fun y : Ix.t' => if M.E.eq_dec x y then true else false) l =
               findA (MFacts.eqb x) l.
      { clear IH H2; elim: l => // [][]q y l IH /=; rewrite IH.
        rewrite [MFacts.eqb x q]/MFacts.eqb /is_left.
        case: (M.E.eq_dec _ _) => //. }
      by rewrite -H3 => H4; apply: InA_cons_tl.
    Qed.      

    Lemma In_elements_find_Some x : 
      In x (M.elements (elt:=P.t) v) ->
      M.find x.1 v = Some x.2.
    Proof.
      rewrite -MProps.F.find_mapsto_iff => H.
      rewrite /get; apply: M.elements_2.
      elim: (M.elements _) H => // [][]k a l IH /=; case.
      { by move => ->; constructor. }
      by move => H; apply: InA_cons_tl; apply: IH.
    Qed.     
    
    Lemma In_elements_nonzero :
      sparse v ->
      forall x,
      In x [seq i.1 | i <- M.elements (elt:=P.t) v] ->
      nonzero (get x v) = true.
    Proof.
      move => H x; rewrite /get; move/In_elements_find_Some_get.
      rewrite /nonzero; move: (H x).
      by case: (M.find _ _) => // a; move/(_ a erefl).
    Qed.        

    Lemma filter_InA' A (l : list A) r g a
      : InA r a (List.filter g l) -> InA r a l.
    Proof.
      elim: l => // ax l IH /=; case H2: (g ax).
      { inversion 1; subst; first by constructor => //.
        by apply: InA_cons_tl; apply: IH. }
      by move => H3; apply: InA_cons_tl; apply: IH.
    Qed.      

    Lemma filtered_out A (l : list A) (r : A -> A -> Prop) g a
          (H0 : forall a a' : A, r a a' -> g a = g a')
      : InA r a l -> ~InA r a (List.filter g l) -> ~g a.
    Proof.
      elim: l => // ax l IH /=; case H2: (g ax).
      { inversion 1; subst.
        { by move => Hx Hy; apply: Hx; constructor. }
        move => Hx; apply: IH => //.
        by move => Hy; apply: Hx; apply: InA_cons_tl. }
      move => Hx Hy Hz; inversion Hx; subst.
      { by rewrite (H0 _ _ H1) H2 in Hz. }
      by apply: IH.
    Qed.
    
    Lemma filter_NoDupA A (l : list A) r g
      : NoDupA r l -> NoDupA r (List.filter g l).
    Proof.
      elim: l => // a l IH; inversion 1; subst => /=; case Hg: (g a).
      { constructor => //.
        { move => H4; apply: H2; apply: filter_InA'; apply: H4. }
        by apply: IH. }
      by apply: IH.
    Qed.
    
    Lemma Perm_elems_enum :
      sparse v -> 
      Permutation
        (List.filter (fun i : Ix.t => nonzero (get i v)) (enumerate Ix.t))
        [seq i.1 | i <- M.elements (elt:=P.t) v].
    Proof.
      move => Hsparse; apply: NoDup_Permutation.
      { assert (H:
          NoDupA (fun x : Ix.t => [eta eq x])
                 (List.filter (fun i : Ix.t => nonzero (get i v)) (enumerate Ix.t))).
        { by apply: filter_NoDupA; case: Ix.enum_ok => H _. }
        elim: (enumerate Ix.t) H => //=; first by move => _; constructor.
        move => a l IH; case: (nonzero (get a v)) => //; inversion 1; subst.
        constructor.
        { move => H4; apply: H2; clear - H4.
          elim: l H4 => // x l IH /=; case: (nonzero _) => //=; case.
          { by move => ->; constructor. }
            by move => H; apply: InA_cons_tl; apply: IH. }
          by apply: IH. }
      { move: (M.elements_3w v); elim: (M.elements _) => //=.
        { move => _; constructor. }
        move => []a b l IH; inversion 1; subst; constructor => /=.
        { clear - H1 => H2; apply: H1; elim: l H2 => // [] ax l IH /=; case.
          { by move => <-; constructor; case: ax. }
          by move => H; apply: InA_cons_tl; apply: IH. }
        by apply: IH. }
      move => x; rewrite filter_In; split.
      { case => H; rewrite /get/nonzero MProps.F.elements_o.
        elim: (M.elements _) => /=; first by case: (P.eq0P P.t0).
        case => a b l IH; rewrite /MProps.F.eqb /M.E.eq_dec.
        case H2: (Ix.eq_dec _ _) => [eqpf|eqpf] /=.
        { move => H3; left; clear - eqpf; move: eqpf.
          case: x => xv xpf; case: a => av apf /=; rewrite /Ix.eq /N.eq /= => H.
          subst xv; f_equal; apply: proof_irrelevance. }
        by move => H3; right; apply: IH. }
      move => H; split; first by case: Ix.enum_ok.
      by apply: In_elements_nonzero.
    Qed.
      
    Lemma foldr_aux1_aux2
          (Hsparse : sparse v)
          (g : P.t -> P.t -> P.t)
          (gcom : forall t1 t2, g t1 t2 = g t2 t1)
          (gassoc : forall t1 t2 t3, g t1 (g t2 t3) = g (g t1 t2) t3) :
      foldr_aux1 (fun _ => g) v P.t0 = foldr_aux2 (fun _ => g) v P.t0.
    Proof.
      rewrite /foldr_aux1/foldr_aux2; apply: foldr_permute => //.
      by apply: Perm_elems_enum.
    Qed.      

    Definition foldr_aux3 T (g : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
      List.fold_right
        (fun p acc => g p.1 p.2 acc) t0
        [seq (i.1, get i.1 m) | i <- M.elements m].

    Lemma foldr_aux2_aux3
          (g : P.t -> P.t -> P.t) :
      foldr_aux2 (fun _ => g) v P.t0 = foldr_aux3 (fun _ => g) v P.t0.
    Proof.
      rewrite /foldr_aux2 /foldr_aux3.
      elim: (M.elements _) => // [][]a b l IH /=.
      by f_equal; apply: IH => x H2. 
    Qed.

    Definition foldr_aux4 T (g : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
      List.fold_right
        (fun p acc => g p.1 p.2 acc) t0
        (M.elements m).

    Lemma foldr_aux3_aux4
          (g : P.t -> P.t -> P.t) :
      foldr_aux3 (fun _ => g) v P.t0 = foldr_aux4 (fun _ => g) v P.t0.
    Proof.
      rewrite /foldr_aux3 /foldr_aux4.
      move: (In_elements_find_Some).
      elim: (M.elements v) => // [][]a b l IH H /=; rewrite IH.
      { by rewrite /get (H (a,b)); last by constructor. }
      by move => x H2; apply: H; right.
    Qed.      

    Definition foldr_aux5 T (g : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
      List.fold_right
        (fun p acc => g p.1 p.2 acc) t0
        (List.rev (M.elements m)).

    Lemma foldr_aux4_aux5
          (g : P.t -> P.t -> P.t)
          (gcom : forall t1 t2, g t1 t2 = g t2 t1)
          (gassoc : forall t1 t2 t3, g t1 (g t2 t3) = g (g t1 t2) t3) :
      foldr_aux4 (fun _ => g) v P.t0 = foldr_aux5 (fun _ => g) v P.t0.
    Proof.
      move: P.t0 => tx; rewrite /foldr_aux4/foldr_aux5.
      move: (M.elements _) => l; elim: l tx => // a l IH tx /=.
      rewrite fold_right_app /= -IH; clear - gcom gassoc. 
      set (f := (fun _ => [eta g _])).
      elim: l tx => // ax l /=; rewrite /f /= => IH tx.
      rewrite -IH; set (y := fold_right _ _ _).
      by rewrite 2!gassoc [g a.2 _]gcom.
    Qed.

    Lemma fold0_foldr
          (Hsparse : sparse v)
          (g : P.t -> P.t -> P.t)
          (pf_g : forall t, g P.t0 t = t)           
          (gcom : forall t1 t2, g t1 t2 = g t2 t1)
          (gassoc : forall t1 t2 t3, g t1 (g t2 t3) = g (g t1 t2) t3) :
      fold0 (fun _ => g) v P.t0 = foldr (fun _ => g) v P.t0.
    Proof.
      rewrite /fold0 M.fold_1 -fold_left_rev_right.
      move: (foldr_aux4_aux5 gcom gassoc); rewrite /foldr_aux5 => <-.
      rewrite -foldr_aux3_aux4 -foldr_aux2_aux3 -foldr_aux1_aux2 //.
      rewrite foldr_foldr_aux1 //.
    Qed.      

    Lemma match_vecs_fold0 
          (Hsparse : sparse v)
          (g : P.t -> P.t -> P.t)
          (pf_g : forall t, g P.t0 t = t)           
          (gcom : forall t1 t2, g t1 t2 = g t2 t1)
          (gassoc : forall t1 t2 t3, g t1 (g t2 t3) = g (g t1 t2) t3) :
      let g' := fun i t => g (P.t_of_u (f i)) t in
      fold0 (fun _ => g) v P.t0 =
      List.fold_right g' P.t0 [seq (Ordinal_of_Ix ix) | ix <- enumerate Ix.t].
    Proof. by rewrite fold0_foldr //; apply: match_vecs_foldr. Qed.
    
    (* a single refinement lem for any would be better here... *)

    Lemma match_vecs_any_some g ix p :
      any g v = Some (ix, p) ->
      [/\ g ix p & P.t_of_u (f (Ordinal_of_Ix ix)) = p].
    Proof.
      rewrite /any; case H: (List.find _ _) => [ix'|//].
      case => H1 H2; split.
      { by case: (List.find_some _ _ H) => _; rewrite H2 H1. }
      by move: (pf ix); rewrite -H1 H2 => ->. 
    Qed.      

    Lemma match_vecs_any_none g :
      any g v = None ->
      forall i, g (Ix_of_Ordinal i) (P.t_of_u (f i)) = false.
    Proof.
      rewrite /any; case H: (List.find _ _) => [//|] _ i.
      have H2: In (Ix_of_Ordinal i) (enumerate Ix.t).
      { case: (Ix.enum_ok) => _; apply. }
      move: (List.find_none _ _ H (Ix_of_Ordinal i) H2) => <-; f_equal.
      by rewrite (pf (Ix_of_Ordinal i)) Ordinal_of_Ix_Ordinal.
    Qed.

    Lemma match_vecs_of_list_INTERNAL (l : list (Ix.t * P.t)) :
      NoDupA (M.eq_key (elt:=P.t)) l ->      
      match_vecs
        (of_list_INTERNAL l)
        [ffun i =>
         P.u_of_t
           (match findA (MProps.F.eqb (Ix_of_Ordinal i)) l with
            | None => P.t0
            | Some p => p
            end)].
    Proof.
      clear v f pf.
      elim: l; first by simpl => H ix; rewrite ffunE /get MProps.F.empty_o P.t_of_u_t.
      case => ix p l IH; inversion 1; clear H; subst => ix'; rewrite ffunE.
      move: (IH H3 ix'); rewrite /get ffunE 2!P.t_of_u_t Ix_of_Ordinal_Ix; clear IH.
      simpl; rewrite /MProps.uncurry /=; case: (Ix.eq_dec ix ix') => [pfx|pfx].
      { move: pfx; rewrite -Ix.eqP => <-.
        rewrite MProps.F.add_eq_o => //.
        have ->: MProps.F.eqb ix ix = true.
        { rewrite /MProps.F.eqb /M.E.eq_dec; case: (Ix.eq_dec _ _) => //.
          by rewrite -Ix.eqP. }
        by []. }
      rewrite MProps.F.add_neq_o => //.
      have ->: MProps.F.eqb ix' ix = false.
      { rewrite /MProps.F.eqb /M.E.eq_dec; case: (Ix.eq_dec _ _) => //.
        by move => X; elimtype False; apply: pfx. }
      by [].
    Qed.      
    
    Lemma of_list_of_list_INTERNAL (l : list (Ix.t * P.t)) i :
      NoDupA (M.eq_key (elt:=P.t)) l ->
      get i (of_list l) = get i (of_list_INTERNAL l).
    Proof.
      move => H; rewrite /get /of_list /of_list_INTERNAL.
      rewrite (MProps.of_list_1b _ H).
      have H': NoDupA (M.eq_key (elt:=P.t))
                      (List.filter (fun p : Ix.t * P.t => nonzero p.2) l).
      { apply filter_NoDupA => //. }
      rewrite (MProps.of_list_1b _ H').
      case H2: (findA _ _) => [x|].
      { move: H2; rewrite -findA_NoDupA => // H2.
        move: (filter_InA' H2).
        generalize (@findA_NoDupA _ P.t _ _ Ix.eq_dec _ i x H).              
        by rewrite /MProps.F.eqb /M.E.eq_dec => -> ->. }
      case H3: (findA _ _) => [y|//].
      move: H3; rewrite -findA_NoDupA => //.
      set (r := (fun _ _ => _ /\ _)) => H3.
      have H4: ~InA r (i,y) (List.filter (fun p => nonzero p.2) l).
      { clear - H2; elim: l H2 => //=; first by move => _; inversion 1.
        move => [] a b l IH => /=.
        case H: (nonzero b) => //=.
        case H2: (MProps.F.eqb i a) => // H3 H4; apply: IH => //.
        inversion H4; subst => //.
        clear - H H2 H1; move: H1; rewrite /r/N.eq/=; case => H5 ->.
        clear - H2 H5; elimtype False.
        move: H2; rewrite /MProps.F.eqb /M.E.eq_dec.
        case H6: (Ix.eq_dec i a) => //. }
      move: H4; set (g := (fun p : Ix.t * P.t => nonzero p.2)) => H4.
      have H5: forall a a' : Ix.t * P.t, r a a' -> g a = g a'.
      { by case => a pa; case => b pb; rewrite /r/g/nonzero /= => [][] Hx <-. }
      move: (@filtered_out _ l r g (i,y) H5 H3 H4).
      by rewrite /g /= /nonzero; move/negP; rewrite negb_involutive; move/P.eq0P.
    Qed.      
    
    Lemma match_vecs_of_list (l : list (Ix.t * P.t)) :
      NoDupA (M.eq_key (elt:=P.t)) l ->      
      match_vecs
        (of_list l)
        [ffun i =>
         P.u_of_t
           (match findA (MProps.F.eqb (Ix_of_Ordinal i)) l with
            | None => P.t0
            | Some p => p
            end)].
    Proof.
      move => H; rewrite /match_vecs => i; rewrite of_list_of_list_INTERNAL => //.
      by apply: match_vecs_of_list_INTERNAL.
    Qed.    

    Lemma match_vecs_of_fun (g : Ix.t -> P.t) :
      let: g' := [ffun i : 'I_n => P.u_of_t (g (Ix_of_Ordinal i))] in 
      match_vecs (of_fun g) g'.
    Proof.
      rewrite /of_fun; case: (Ix.enum_ok) => H Htot ix.
      have H2: (NoDupA (M.eq_key (elt:=P.t)) [seq (ix, g ix) | ix <- enumerate Ix.t]).
      { clear - H; move: H; move: (enumerate _) => l; elim: l => //=.
        move => a l IH; inversion 1; subst; constructor.
        { move => H4; apply: H2; clear - H4; elim: l H4 => //=.
          { inversion 1. }
          move => az l IH; inversion 1; subst.
          { constructor; rewrite /M.eq_key /M.Raw.Proofs.PX.eqk /= in H0.
            clear - H0; move: H0; case: a => v pf /=; case: az => v' pf' /=.
            rewrite /N.eq => H; subst v'; f_equal.
            apply: proof_irrelevance. }
          by apply: InA_cons_tl; apply: IH. }
        by apply: IH. }
      move: (match_vecs_of_list H2 ix) ->; rewrite 2!ffunE 2!P.t_of_u_t.
      rewrite /MProps.F.eqb Ix_of_Ordinal_Ix.
      move: (Htot ix) => H3.
      have H5:
        InA (fun p p' : Ix.t * P.t => Ix.eq p.1 p'.1 /\ p.2 = p'.2)
            (ix, g ix)
            [seq (ix, g ix) | ix <- enumerate Ix.t].
      { clear - H3; move: H3.
        move: (enumerate Ix.t) => l.
        elim: l => // a l IH; inversion 1; subst.
        { constructor; split => //. }
        by apply: InA_cons_tl; apply: IH. }      
      generalize (findA_NoDupA _ Ix.eq_dec ix (g ix) H2).
      rewrite /M.E.eq_dec; case: (findA _ _).
      { by move => a; case => H4 _; case: (H4 H5). }
      by case => H4 _; move: (H4 H5).
    Qed.

    Lemma match_vecs_mk_sparse :
      match_vecs (mk_sparse v) [ffun i => P.u_of_t (get (Ix_of_Ordinal i) v)].
    Proof. apply: (match_vecs_of_fun (fun ix => get ix v)). Qed.
  End refinement_lemmas.
End Vector.  

(* two-dimensional vectors *)

Module Matrix (B : BOUND) (P : PAYLOAD) <: PAYLOAD.
  Module Vec := Vector B P.
  Definition t := Vec.t.                    
  Definition t0 : t := Vec.M.empty _.
  Definition eq0 (d : t) := Vec.M.is_empty d.
  Lemma eq0P d : reflect (d=t0) (eq0 d).
  Proof.
    rewrite /eq0 /Vec.M.is_empty /Vec.M.Raw.is_empty /t0.
    case: d => x y /=; move: y; case: x => y; constructor => //.
    case H: Vec.M.empty => [z w]; inversion H; subst.
    f_equal; apply: proof_irrelevance.
  Qed.    
  Definition u := {m : t & {f : Vec.ty & Vec.match_vecs m f}}.
  Program Definition u_of_t (m : t) : u :=
    existT _ m _.
  Next Obligation.
    set (f := [ffun i : 'I_B.n =>
               P.u_of_t (Vec.get (Vec.Ix_of_Ordinal i) m)] : Vec.ty).
    refine (existT _ f _).
    by move => i; rewrite /f ffunE Vec.Ix_of_Ordinal_Ix P.t_of_u_t.
  Qed.
  Definition t_of_u (f : u) : t := projT1 f.
  Lemma t_of_u_t : forall t0 : t, t_of_u (u_of_t t0) = t0.
  Proof. by []. Qed.
End Matrix.

(* one-dimensional D-vectors *)

Module DPayload <: PAYLOAD.
  Definition t := DRed.t.   
  Definition t0 := 0%DRed.
  Definition eq0 (dx : t) :=
    if Deq_dec dx.(DRed.d) 0 then true else false.
  Lemma eq0P (dx : t) : reflect (dx=0%DRed) (eq0 dx).
  Proof.
    rewrite /eq0; case: (Deq_dec dx.(DRed.d) 0) => a; constructor.
    { case: dx a => /= d pf H; subst d; unfold DRed.t0.
      f_equal; apply: proof_irrelevance. }
    by inversion 1; case: dx H H0 a => d pf; case => H /= _; subst d.
  Qed.
  Definition u := dyadic_rat.
  Definition u_of_t (dx : t) := D_to_dyadic_rat dx.(DRed.d).
  Definition t_of_u (r : dyadic_rat) : t :=
    DRed.mk (Dred (dyadic_rat_to_D r)) (Dred_idem _).
  Lemma t_of_u_t : forall t0 : t, t_of_u (u_of_t t0) = t0.
  Proof.
    unfold t_of_u, u_of_t.
    intros [tx pf]; simpl.
    generalize (projT2 (D_to_dyadic_rat tx)) as x; intro.
    generalize (projT2 x) as y.    
    generalize (projT1 x) as d; intro.
    intros H.
    assert (H2: Dred (D_to_dyadic_rat tx) = tx).
    { pattern tx at 2.
      rewrite <-pf.
      apply Dred_complete.
      assert (H3: dyadic_rat_to_D (D_to_dyadic_rat tx) = tx).
      { unfold dyadic_rat_to_D, D_to_dyadic_rat.
        destruct tx; simpl in *.
        auto. }
      rewrite H3; apply Qeq_refl. }
    clear - H2.
    generalize (Dred_idem (D_to_dyadic_rat tx)).
    generalize pf.
    revert H2; clear pf; intros -> pf e.
    f_equal; apply proof_irrelevance.
  Qed.    
End DPayload.  

Definition Dabs (d : DRed.t) : DRed.t :=
  (if Dlt_bool d.(DRed.d) D0 then -d else d)%DRed.

Module DVector (B : BOUND).
  Module Vec := Vector B DPayload.

  Definition dot_product (v1 v2 : Vec.t) : DRed.t :=
    Vec.fold0 (fun ix d acc => (acc + (d * Vec.get ix v2))%DRed) v1 0%DRed.
  
  Definition linf_norm (v : Vec.t) : DRed.t :=
    Vec.fold0
      (fun _ d acc => if Dlt_bool acc.(DRed.d) (Dabs d).(DRed.d)
                      then Dabs d
                      else acc)
      v
      0%DRed.
End DVector.    

(* D-matrices *)

Module DMatrix (B : BOUND) := Matrix B DPayload.
