Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii ProofIrrelevance List.

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
  Parameter u : Type. (* the high-level type *)
  (* almost but not quite a bijection *)    
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
  
  (* operations *)
  Definition get (i : Ix.t) (m : t) : P.t :=
    match M.find i m with
    | None => P.t0
    | Some p => p
    end.

  Definition set (i : Ix.t) (p : P.t) (m : t) : t :=
    M.add i p m.

  (* assumes f P.t0 = P.t0 *)
  Definition map0 (f : P.t -> P.t) (m : t) : t :=
    M.map f m.

  (* assumes f i P.t0 t = t *)  
  Definition fold0 T (f : Ix.t -> P.t -> T -> T) (m : t) (t0 : T) : T :=
    M.fold f m t0.

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
  Definition of_list (l : list (Ix.t * P.t)) : t := MProps.of_list l.
  
  (* construct a vector from function f -- 
     WARNING: results in a nonsparse representation *)
  Definition of_fun (f : Ix.t -> P.t) : t :=
    of_list (List.map (fun ix => (ix, f ix)) (enumerate Ix.t)).
  
  (* the refinement relation *)
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
      case: (Ix.eq_dec i j) => [px|px].
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

    Lemma match_vecs_of_fun (g : Ix.t -> P.t) :
      let g' := [ffun i : 'I_n => P.u_of_t (g (Ix_of_Ordinal i))] in 
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
  End refinement_lemmas.
End Vector.  

Module DPayload <: PAYLOAD.
  Definition t := D.                    
  Definition t0 := 0%D.
  Definition u := dyadic_rat.
  Definition u_of_t := D_to_dyadic_rat.
  Definition t_of_u := dyadic_rat_to_D.
  Lemma t_of_u_t : forall t0 : t, t_of_u (u_of_t t0) = t0.
  Proof. by []. Qed.
End DPayload.  

Module DVector (B : BOUND) := Vector B DPayload.

    
  
      
        
        
        
      
  

  
    
  
  
  