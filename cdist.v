Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String Ascii.

(*The computable state representation is an FMap over 
  player indices, represented as positive.*)
Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import strings compile orderedtypes dyadic numerics dist games.

Definition upd {A : finType} {T : Type}
           (a : A) (t : T) (s : {ffun A -> T}) :=
  finfun (fun b => if a==b then t else s b).

Module Index.
Section index.
  Variable n : N.t.
  Variable n_gt0 : (0 < N.to_nat n)%N.  
  
  Record t : Type :=
    mk { val : N.t;
         pf : (N.to_nat val < N.to_nat n)%N }.

  Program Definition pred (i : t) : t :=
    @mk (N.pred (val i)) _.
  Next Obligation.
    move: (pf i); rewrite N2Nat.inj_pred.
    move: (N.to_nat (val i)) => n0 => H.
    apply/leP; apply: le_lt_trans; first by apply/leP; apply: leq_pred.
    by apply/leP.
  Qed.

  Program Definition max : t := @mk (N.pred n) _.
  Next Obligation.
    rewrite N2Nat.inj_pred; apply/ltP.
    move: (ltP n_gt0) => H.
    omega.
  Qed.
End index.
End Index.

(** Unnormalized functional weight distributions efficiently supporting: 
    - sampling 
    - weight update *)

Module AM.
Record t (A : Type) : Type :=
  mk {
      size : N.t;
      
      map :> M.t A;
            (* [wmap]: a map from positive indices in range 
                       [0, wsize) to values [a] *)
      pf :
        forall i : N.t,
          (N.to_nat i < N.to_nat size)%nat ->
          exists a, M.find i map = Some a
    }.

Fixpoint Nlength (A : Type) (l : list A) : N.t :=
  match l with
  | nil => 0
  | _ :: l' => N.succ (Nlength l')
  end.

Section functions.
  Variable A : Type.
  Variable w : t A.

  Definition index : Type := Index.t (size w).
  Definition index_key : index -> M.key := @Index.val (size w).
  Definition index_nat : index -> nat := @Index.val (size w).  

  Definition ordinal_of_index (i : index) : 'I_(N.to_nat (size w)) :=
    Ordinal (Index.pf i).
  
  Coercion index_key : index >-> M.key.
  
  Program Definition lookup (i : index) : A := 
    match M.find i (map w) with
    | None => _
    | Some a => a
    end.
  Next Obligation.
    move: (Index.pf i) => H.
    move: (pf H) => H2.
    elimtype False.
    by case: H2 => x H3; rewrite H3 in Heq_anonymous.
  Qed.

  Program Definition update
             (i : index)
             (a': A)
             (w : t A)
    : t A :=
    @mk
      _ 
      (size w)
      (M.add i a' (map w))
      _.
  Next Obligation.
    case (N.eqb_spec (index_key i) i0).
    { move => H2; subst i0; exists a'.
      rewrite MProps.F.add_eq_o => //. }
    move => Hneq; rewrite MProps.F.add_neq_o => //.
    by apply pf.
  Qed.      
  
  Program Definition swap (i j : index) : t A :=
    let a := lookup i in
    let b := lookup j in 
    @mk
      _
      (size w)
      (M.add i b (M.add j a (map w)))
      _.
  Next Obligation.  
    case: (N.eqb_spec (index_key i) i0).
    { move => H2; subst i0; exists (lookup j).
      rewrite MProps.F.add_eq_o => //. }
    move => H2.
    case: (N.eqb_spec (index_key j) i0).
    { move => H3; subst i0; exists (lookup i).
      rewrite MProps.F.add_neq_o => //.
      rewrite MProps.F.add_eq_o => //. }
    move => H3.
    rewrite MProps.F.add_neq_o => //.
    rewrite MProps.F.add_neq_o => //.
    by apply pf.
  Qed.      

  Definition split_aux (f : M.key -> A -> bool) : ((N.t*M.t A) * (N.t*M.t A)) :=
    M.fold 
      (fun i a (p : (N.t*M.t A) * (N.t*M.t A)) =>
         match p with
         | ((x,trues), (y,falses)) => 
           (if f i a then
              ((N.succ x, M.add i a trues), (y, falses))
            else
              ((x, trues), (N.succ y, M.add i a falses)))
         end)
      (map w)
      ((N0, M.empty _), (N0, M.empty _)).

  Program Definition split (f : M.key -> A -> bool) : (t A * t A) :=
    match split_aux f with
      | ((x,trues), (y,falses)) => 
        (@mk _ x trues _, @mk _ y falses _)
    end.
  Next Obligation.
  Admitted. (*TODO*)
  Next Obligation.
  Admitted. (*TODO*)    

  Program Definition fmap
             (B : Type)
             (f : A -> B)
    : t B :=
    @mk
      _
      (size w)
      (M.map f (map w))
      _.
  Next Obligation.
    rewrite MFacts.map_o.
    case: (pf H) => x ->; exists (f x) => //.
  Qed.                                 

  Definition fold
             (B : Type)
             (f : N.t -> A -> B -> B)
             (acc : B)
    : B := M.fold f (map w) acc.
End functions.

Section functions2.
  Variable A : Type.
  
  Program Definition init (a : A) : t A :=
    @mk _ 1 (M.add N0 a (M.empty _)) _.
  Next Obligation.
    exists a.
    rewrite Pos2Nat.inj_1 in H.
    have H2: i = N0.
    { case: i H => //.
      move => p; rewrite positive_N_nat => H.
      have H2: Pos.to_nat p = 0%nat.
      { move: H; move: (Pos.to_nat p) => n.
        elim: n => //. }
      apply: N2Nat.inj.
      rewrite positive_N_nat H2 //. }
    rewrite {}H2 MProps.F.add_eq_o //.
  Qed.    

  Fixpoint map_from_list (i : M.key) (acc : M.t A) (l : list A) : M.t A :=
    match l with
    | nil => acc
    | a :: l' => map_from_list (N.succ i) (M.add i a acc) l'
    end.
  
  Program Definition from_list (l : list A) : t A :=
    @mk _ (Nlength l) (map_from_list N0 (M.empty _) l) _.
  Next Obligation.
  Admitted. (*TODO*)

  Definition empty : t A := from_list nil.
End functions2.
End AM.

Module DIST.
Record t (A : Type) : Type :=
  mk {
      cpmf :> AM.t (AM.t (A*D))
           (* [cpmf]: a map from 
                - LEVEL 1: weight level i = [2^i, 2^{i+1})
                - LEVEL 2: weight array containing weights (a,d)
                           in the range of weight level i *)
    }.

Section functions.
  Variable A : Type.

  Definition empty : t A := mk (AM.empty _).
  
  Definition level_of (d : D) : N.t :=
    match d with
    | Dmake x y => N.pred (Npos (Plub_aux x y))
    end.

  (** PRECONDITION: a not in w[level_of(a)] *)
  Definition add_weight
             (a : A)
             (d : D)
             (c : t A)
    : option (t A) :=
    let l := level_of d in 
    let am :=
        match AM.lookup l (cpmf c) with
        | None => AM.empty _
        | Some am0 => am0
        end
    in 
    let am' := AM.add (a,d) am in
    Some (mk (AM.update l am' (cpmf c))).

  (** Updates [w] according to [f], returning the new array map 
      together with any pairs (a,d) that are now mis-leveled. *)
  Definition update_level
             (level : N.t)
             (f : A -> D -> D)
             (w : AM.t (A*D))
    : (option (AM.t (A*D)) * list (N.t*A*D)) :=
    let w' := AM.fmap (fun p : (A*D) => let (a,d) := p in (a, f a d)) w in
    let must_removes := 
        AM.fold
          (fun i (p' : (A*D)) l0 =>
             let (a,d') := p' in 
             if N.eqb (level_of d') level then l0
             else (i,a,d') :: l0)
          w'
          nil
    in
    ((*actually remove the "must_removes":*)
      List.fold_left
       (fun acc (p' : (N.t*A*D)) =>
          match p' with
          | (i, a, d') => 
            match acc with
            | None => None
            | Some w0 => AM.remove i w0
            end
          end)
       must_removes
       (Some w'),
     must_removes).

  Fixpoint update_weights_aux
           (num_levels : nat)
           (f : A -> D -> D)
           (acc : (option (AM.t (AM.t (A*D))) * list (N.t*A*D)))
    : (option (AM.t (AM.t (A*D))) * list (N.t*A*D)) :=
    match num_levels with
    | O => acc
    | S n' =>
      let level := N.of_nat n' in
      match acc with
      | (None, l0) => (None, l0)
      | (Some w, l0) => 
        match AM.lookup level w with
        | None => (None, l0)
        | Some w2 =>       
          match update_level level f w2 with
          | (None, _) => (None, l0)
          | (Some w3, removed) =>
            update_weights_aux
              n'
              f
              (Some (AM.update level w3 w), removed ++ l0)
          end
        end
      end
    end.
        
  Fixpoint add_weights_aux
             (l : list (A*D))
             (acc : option (t A))
    : option (t A) :=
    match l with
    | nil => acc
    | (a,d) :: l' =>
      match acc with
      | None => None
      | Some w => add_weights_aux l' (add_weight a d w)
      end
    end.

  Definition add_weights
             (l : list (A*D))
             (c : t A)
    : option (t A) :=
    add_weights_aux l (Some c).
  
  Definition update_weights
             (f : A -> D -> D)
             (c : t A)
    : option (t A) :=
    let num_levels := AM.size c in 
    match update_weights_aux num_levels f (Some (cpmf c), nil) with
    | (None, _) => None
    | (Some w, removed) =>
      let removed' :=
          map (fun p => match p with (_,a,d) => (a,d) end)
              removed
      in
      add_weights removed' (mk w)
    end.
End functions.
End DIST.

Definition d := AM.add 4 (AM.add 3 (AM.empty _)).
Definition v1 := AM.lookup 0 d.
Definition v2 := AM.lookup 1 d.
Definition v3 := AM.lookup 2 d.

Recursive Extraction v1 v2 v3.

Definition r1 := 
  match DIST.add_weight 1 (Dmake 3 2) (DIST.empty _) with
  | None => None
  | Some c => DIST.update_weights (fun _ d => Dmake 24 1) c
  end.

Definition r2 := 
  DIST.add_weights (((1, Dmake 3 2) :: (2, Dmake 24 1) :: nil))%nat (DIST.empty _).

Recursive Extraction r1 r2.
               
(** FIXME: In r1 and r2, why is size 0? *)  

Definition fun_of_t
           (A : Type)
           (Aeq : A -> A -> bool)
           (c : t A) : A -> Q :=
  fun a =>
    match findA (Aeq a) c with 
    | None => 0
    | Some d => D_to_Q d
    end.

Definition dist_t_match
           (A : finType)
           (Aeq : A -> A -> bool)           
           (c : t A)
           (d : dist A rat_realFieldType)           
  : Prop :=
  pmf d = finfun (fun a => Q_to_rat (fun_of_t Aeq c a)).

Section sampling.
  Variable T : Type. (* randomness oracle state *)
  Variable rand : T -> D*T.
  
  Fixpoint sample_aux
         (A : Type) (a0 : A)
         (acc r : D) (l : list (A*D)) : A :=
    match l with
    | nil => a0 (*should never occur*)
    | (a, w) :: l' =>
      if Dle_bool acc r && Dle_bool r (Dadd acc w) then
        eprint_string "Chose action " a
      else sample_aux a0 (Dadd acc w) r l'
    end.

  Definition sample
             (A : Type) (a0 : A)
             (c : t A)
             (t : T)
    : (A*T) :=
    let sum :=
        List.fold_left
          (fun acc1 (x:(A*D)) => let (a,q) := x in Dadd acc1 q)
          c (Dmake 0 1)
    in
    let (r, t') := rand t in
    let r' := Dmult r sum in
    (sample_aux a0 D0 r' c, t').

  Fixpoint prod_sample_aux
           (A : Type) (a0 : A)           
           (acc : M.t A * T)
           (n : nat)
           (p : nat -> t A)
    : (M.t A * T) :=
    match n with
    | O => acc
    | S n' =>
      let (a, t) := sample a0 (p n') (snd acc) in
      prod_sample_aux a0 (M.add (N.of_nat n') a (fst acc), t) n' p
    end.

  Definition prod_sample
             (num_players : nat)
             (A : Type) (a0 : A)
             (p : nat -> t A)
             (t : T)
    : (M.t A * T) :=
    prod_sample_aux a0 (M.empty _, t) num_players p.
End sampling.

Axiom rand_state : Type.
Extract Constant rand_state => "unit".
Axiom init_rand_state : rand_state.
Extract Constant init_rand_state => "()".

Axiom rand : rand_state -> (D*rand_state). (*in range [0,1]*)
Extract Constant rand =>
 "fun _ -> 
  let rec z_of_ocamlint i =
    let zzero = Z0 in
    let zone = Zpos XH in
    let ztwo = Zpos (XO XH) in
    if i = 0 then zzero
    else if i mod 2 = 0 then Z.mul ztwo (z_of_ocamlint (i/2))
    else Z.add (Z.mul ztwo (z_of_ocamlint (i/2))) zone
  in  
  let _ = Random.self_init () in
  let d = Random.int 256 in
  let zn = z_of_ocamlint d in 
  let peight = XO (XO (XO XH)) in
  let q = { num = zn; den = peight } 
  in
  Printf.eprintf ""Generated random r = %d"" d; prerr_newline ();
  Pair (q, ())".

Definition rsample A (a0 : A) (c : t A) : A :=
  fst (sample rand a0 c init_rand_state).

Definition rprod_sample A (a0 : A) (num_players : nat) (p : nat -> t A) : M.t A :=
  fst (prod_sample rand num_players a0 p init_rand_state).

Section rsample_cost.
  Context {A : Type} (a0 : A) {num_players : nat}.
  Context `{CCostInstance : CCostClass num_players A}.  

  Definition rsample_ccost (i : N.t) (a : A) (p : nat -> t A) : D :=
    let m := rprod_sample a0 num_players p in
    ccost i (M.add i a m).
End rsample_cost.

Section expected_rsample_cost.
  Context {A : finType} {Aeq : A -> A -> bool}.
  (*Aeq: not necessarily the equality associated with A's eqType instance.*)
  Context (a0 : A) {num_players : nat}.
  Context `{CGameInstance : cgame num_players A}.    

  Variable (p : nat -> t A).
  Variable (f : {ffun 'I_num_players -> dist A rat_realFieldType}).
  Hypothesis dists_match : forall i : 'I_num_players, dist_cdist_match Aeq (p i) (f i).
  
  Axiom rsample_ccost_expected :
    forall (i : 'I_num_players) (a : A),
      D_to_Q (rsample_ccost a0 (N.of_nat i) a p) =
      rat_to_Q (expectedValue (prod_dist f) (fun x => cost i (upd i a x))).
End expected_rsample_cost.

  
  




  
  

      