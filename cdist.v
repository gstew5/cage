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

(** Unnormalized functional weight distributions efficiently supporting: 
    - sampling 
    - weight update *)

Record array_map (A : Type) : Type :=
  mkWeightMap {
      wsize : N.t;
      wmap :> M.t A;
            (* [wmap]: a map from positive indices in range 
                       [0, wsize) to values [a] *)
    }.

Section array_map_functions.
  Variable A : Type.

  Definition array_map_ok
             (w : array_map A)
             (f : {ffun 'I_(N.to_nat (wsize w)) -> A}) :=
    forall (i : N.t) (pf : (N.to_nat i < N.to_nat (wsize w))%nat),
      M.find i (wmap w) = Some (f (Ordinal pf)).
  
  Definition am_lookup
             (i : N.t)
             (w : array_map A)
    : option A := M.find i (wmap w).

  Lemma am_lookup_ok i w f 
    (pf : (N.to_nat i < N.to_nat (wsize w))%nat) :  
    @array_map_ok w f ->
    am_lookup i w = Some (f (Ordinal pf)).
  Proof.
    unfold array_map_ok, am_lookup. 
    intros H; apply (H i pf).
  Qed.                                     
  
  Definition am_swap
             (i j : N.t)
             (w : array_map A)
    : option (array_map A) :=
    match am_lookup i w, am_lookup j w with
    | None, _ => None
    | _, None => None
    | Some a, Some a' => 
      Some
        (mkWeightMap
           (wsize w)
           (M.add i a' (M.add j a (wmap w))))
    end.

  (*Lemma am_swap_ok i j w w' f
        (pfi : (N.to_nat i < N.to_nat (wsize w))%nat)
        (pfj : (N.to_nat j < N.to_nat (wsize w))%nat) :
    let i0 := Ordinal pfi in
    let j0 := Ordinal pfj in 
    am_swap i j w = Some w' ->     
    @array_map_ok w f ->
    @array_map_ok w' (upd i0 (f j0) (upd j0 (f i0) f)).*)

  Definition am_remove
             (i : N.t)
             (w : array_map A)
    : option (array_map A) :=
    let j := N.pred (wsize w) in
    match am_swap i j w with
    | None => None
    | Some w' =>
      Some
        (mkWeightMap
           (N.pred (wsize w'))
           (M.remove j (wmap w')))
    end.

  (** Add a fresh weight pair (a,d) to w. *)
  Definition am_add
             (a : A)
             (w : array_map A)
    : array_map A :=
    mkWeightMap
      (N.succ (wsize w))
      (M.add (wsize w) a (wmap w)).
End array_map_functions.

Record cdist (A : Type) : Type :=
  mkCDist {
      cmax_weight : D;
      cpmf :> array_map (array_map A)
           (* [cpmf]: a map from 
                - LEVEL 1: weight level i = [2^i, 2^{i+1})
                - LEVEL 2: weight array containing weights (a,d)
                           in the range of weight level i *)
    }.

Section cdist_functions.
  Variable A : Type.

  Definition level_of (d : D) :=
    match d with
    | Dmake x y => Plub_aux x y
    end.

  Compute level_of (Dmake 345 27).
  Compute Zsize 345.
  Compute Pos.size 3.
  
  Definition add_weight
  
  

Definition fun_of_cdist
           (A : Type)
           (Aeq : A -> A -> bool)
           (c : cdist A) : A -> Q :=
  fun a =>
    match findA (Aeq a) c with 
    | None => 0
    | Some d => D_to_Q d
    end.

Definition dist_cdist_match
           (A : finType)
           (Aeq : A -> A -> bool)           
           (c : cdist A)
           (d : dist A rat_realFieldType)           
  : Prop :=
  pmf d = finfun (fun a => Q_to_rat (fun_of_cdist Aeq c a)).

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
             (c : cdist A)
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
           (p : nat -> cdist A)
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
             (p : nat -> cdist A)
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

Definition rsample A (a0 : A) (c : cdist A) : A :=
  fst (sample rand a0 c init_rand_state).

Definition rprod_sample A (a0 : A) (num_players : nat) (p : nat -> cdist A) : M.t A :=
  fst (prod_sample rand num_players a0 p init_rand_state).

Section rsample_cost.
  Context {A : Type} (a0 : A) {num_players : nat}.
  Context `{CCostInstance : CCostClass num_players A}.  

  Definition rsample_ccost (i : N.t) (a : A) (p : nat -> cdist A) : D :=
    let m := rprod_sample a0 num_players p in
    ccost i (M.add i a m).
End rsample_cost.

Section expected_rsample_cost.
  Context {A : finType} {Aeq : A -> A -> bool}.
  (*Aeq: not necessarily the equality associated with A's eqType instance.*)
  Context (a0 : A) {num_players : nat}.
  Context `{CGameInstance : cgame num_players A}.    

  Variable (p : nat -> cdist A).
  Variable (f : {ffun 'I_num_players -> dist A rat_realFieldType}).
  Hypothesis dists_match : forall i : 'I_num_players, dist_cdist_match Aeq (p i) (f i).
  
  Axiom rsample_ccost_expected :
    forall (i : 'I_num_players) (a : A),
      D_to_Q (rsample_ccost a0 (N.of_nat i) a p) =
      rat_to_Q (expectedValue (prod_dist f) (fun x => cost i (upd i a x))).
End expected_rsample_cost.

  
  




  
  

      