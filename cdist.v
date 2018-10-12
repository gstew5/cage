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

Require Import OUVerT.strings compile OUVerT.orderedtypes
        OUVerT.dyadic OUVerT.numerics OUVerT.dist games.

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
                       [0, size) to values [a] *)
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

Section functions0.
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

  Fixpoint map_from_list (l : list A) : N.t * M.t A :=
    List.fold_left
      (fun acc a =>
         let (i, m) := (acc : N.t * M.t A) in
         (N.succ i, M.add i a m))
      l
      (N0, M.empty _).

  Fixpoint map_from_keylist (l : list (M.key * A)) : M.t A :=
    match l with
    | nil => M.empty _
    | (i, a) :: l' => M.add i a (map_from_keylist l')
    end.

  Lemma map_from_list_fold_right l :
    map_from_list l =
    List.fold_right
      (fun a acc =>
         let (i, m) := (acc : N.t * M.t A) in
         (N.succ i, M.add i a m))
      (N0, M.empty _)
      (List.rev l).      
  Proof.
    rewrite fold_left_rev_right.
    rewrite /map_from_list.
    elim: l => //.
  Qed.    

  Fixpoint seq_upto (n : nat) : list N.t :=
    match n with
    | O => nil
    | S n' => rcons (seq_upto n') (N.of_nat n') 
    end.

  Lemma seq_upto_length n : seq.size (seq_upto n) = n.
  Proof. by elim: n => // n /=; rewrite size_rcons => ->. Qed.
  
  Lemma seq_upto_nth (n m : nat) :
    (m < n)%nat -> 
    nth N0 (seq_upto n) m = N.of_nat m.
  Proof.
    elim: n m => // n IH m H /=; rewrite nth_rcons.
    case H2: (m < seq.size (seq_upto n))%N.
    { rewrite IH => //.
      by rewrite seq_upto_length in H2. }
    case H3: (_ == _).
    { move: (eqP H3) => ->.
      by rewrite seq_upto_length. }
    rewrite seq_upto_length in H2, H3.
    elimtype False.
    move: {H}(ltP H); move/lt_n_Sm_le/le_lt_or_eq; case.
    { by move/ltP; rewrite H2. }
    by move => H4; subst m; rewrite eq_refl in H3.
  Qed.

  (** WORK-IN-PROGRESS: 
  Lemma map_from_list_keylist l i :
    M.find i (snd (map_from_list l)) =
    M.find i (map_from_keylist (zip (seq_upto (seq.size l)) l)).
  Proof.
    rewrite map_from_list_fold_right.
    rewrite /map_from_keylist.
    move: (M.empty A) i 0%num.
    elim: l => // a l IH m i n /=.
    rewrite fold_right_app /= IH /=.
    (** NoDupA !!! *)
  Abort.
    
  Lemma map_from_list_index_gt l (n n' : N.t) m m' :
    List.fold_right
      (fun a acc =>
         let (i, m) := (acc : N.t * M.t A) in
         (N.succ i, M.add i a m))
      (n, m)
      l = (n', m') ->
  
  Lemma map_from_list_fold_right'_aux l (n : N.t) m :
    List.fold_right
      (fun a acc =>
         let (i, m) := (acc : N.t * M.t A) in
         (N.succ i, M.add i a m))
      (n, m)
      (List.rev l) =
    List.fold_right
      (fun a acc =>
         let (i, m) := (acc : N.t * M.t A) in
         (N.pred i, M.add i a m))
      (n + Nlength l, m)%num
      l.
  Proof.
    elim: l n m => /=.
    { by move => n m; rewrite N.add_0_r. }
    move => a l IH n m; rewrite fold_right_app /= IH.
    have ->: (N.succ n + Nlength l = n + N.succ (Nlength l))%num.
    { rewrite N.add_succ_l; symmetry; rewrite [(n + _)%num]N.add_comm N.add_succ_l.
      by rewrite [(Nlength l + _)%num]N.add_comm. }
    
    case: (fold_right
     (fun (a0 : A) (acc : N.t * M.t A) =>
      let (i, m0) := acc in (N.pred i, M.add i a0 m0))
     ((n + N.succ (Nlength l))%num, M.add n a m) l) => //.

    
    rewrite IH.
    
    rewrite fold_left_rev_right.
    rewrite /map_from_list.
    elim: l => //.
  Qed.    

  Lemma map_from_list_domain_default l (i : N.t) (a : A) :
    (i < fst (map_from_list l))%nat ->
    M.find i (snd (map_from_list l)) = Some (List.nth (N.to_nat i) l a).
  Proof.
    rewrite map_from_list_fold_right.
    elim: (List.rev l) i => // ax l' IH i /= H.
    move: H IH; case: (fold_right _ (0%num, M.empty A) l') => a0 b /= H IH.
    
    case H2: (N.eq_dec a0 i) => [Hx|Hx].
    { subst i; move {H2 H}.
      rewrite MProps.F.add_eq_o => //.
    have H3: (i < a0)%N.
    { rewrite nat_of_bin_succ in H.
      apply/ltP; move: (ltP H) => H3. clear - H3 Hx.
      have H4: nat_of_bin a0 <> nat_of_bin i.
      { by move => H4; apply: Hx; apply: nat_of_bin_inj. }
      omega. }
    case: (IH _ H3) => x H4; exists x.
    rewrite MProps.F.add_neq_o => //.
  Qed.
  *)

  Lemma map_from_list_domain l (i : N.t) :
    (i < fst (map_from_list l))%nat ->
    exists a, M.find i (snd (map_from_list l)) = Some a.
  Proof.
    rewrite map_from_list_fold_right; elim: (List.rev l) i => // a l' IH i /= H.
    move: H IH; case: (fold_right _ (0%num, M.empty A) l') => a0 b /= H IH.
    case H2: (N.eq_dec a0 i) => [Hx|Hx].
    { subst i; move {H2 H}.
      by rewrite MProps.F.add_eq_o => //; exists a. }
    have H3: (i < a0)%N.
    { rewrite nat_of_bin_succ in H.
      apply/ltP; move: (ltP H) => H3. clear - H3 Hx.
      have H4: nat_of_bin a0 <> nat_of_bin i.
      { by move => H4; apply: Hx; apply: nat_of_bin_inj. }
      omega. }
    case: (IH _ H3) => x H4; exists x.
    rewrite MProps.F.add_neq_o => //.
  Qed.
  
  Program Definition from_list (l : list A) : t A :=
    @mk _ (fst (map_from_list l)) (snd (map_from_list l)) _.
  Next Obligation.
    apply: map_from_list_domain.
    by apply: N2Nat_lt.
  Qed.

  Definition empty : t A := from_list nil.
End functions0.

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

  Program Definition bump (n : N.t) : Index.t (N.succ n) :=
    @Index.mk _ n _.
  Next Obligation.
    rewrite N2Nat.inj_succ; apply/ltP; omega.
  Qed.    
  
  (* Append [a] at the end of array map [w]. *)
  Program Definition add (a : A) : t A :=
    @mk
      A
      (N.succ (size w))
      (M.add (Index.val (bump (size w))) a (map w))
      _.
  Next Obligation.
    case: (N.eqb_spec (size w) i).
    { move => H2; subst i.
      exists a; rewrite MProps.F.add_eq_o //. }
    move => H2; rewrite MProps.F.add_neq_o => //.
    apply pf.
    have H3: N.to_nat (size w) <> N.to_nat i.
    { by rewrite N2Nat.inj_iff. }
    rewrite N2Nat.inj_succ in H.
    move: H H3; move: (N.to_nat (size w)) => x; move: (N.to_nat i) => y.
    move/ltP => H H3; apply/ltP; omega.
  Qed.    

  (** Add [a] at level [i], regardless whether [i] is already 
      present in the array map. If [i >= size], then this operation 
      may require the addition of a new array cell at index [size]. *)

  Program Definition update_add (i : N.t) (a : A) : t A :=
    (match N.ltb i (size w) as o return _ = o -> _ with
     | true => fun pf => update (@Index.mk _ i _) a
     | false => fun _ => add a
     end) erefl.
  Next Obligation.
    move: pf0; rewrite N.ltb_lt => H.
    apply/ltP; rewrite /N.lt N2Nat.inj_compare in H.
    by rewrite nat_compare_lt.
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
  
  Definition split_aux
             (f : M.key -> A -> bool) : list A * list A :=
    M.fold 
      (fun i a (p : list A * list A) => 
         match p with
         | (trues, falses) => 
           if f i a then (a :: trues, falses)
           else (trues, a :: falses)
         end)
      (map w)
      (nil, nil).

  Definition split (f : M.key -> A -> bool) : (t A * t A) :=
    let (trues, falses) := split_aux f in
    (from_list trues, from_list falses).

  Program Definition fmapi
             (B : Type)
             (f : M.key -> A -> B)
             (f_pf : forall (x y : M.key) (e : A), N.eq x y -> f x e = f y e)             
    : t B :=
    @mk
      _
      (size w)
      (M.mapi f (map w))
      _.
  Next Obligation.
    rewrite MFacts.mapi_o => //.
    case: (pf H) => x ->; exists (f i x) => //.
  Qed.                                 

  Program Definition fmap
             (B : Type)
             (f : A -> B)
    : t B := @fmapi _ (fun (_ : M.key) (a : A) => f a) _.
  
  Definition fold
             (B : Type)
             (f : N.t -> A -> B -> B)
             (acc : B)
    : B := M.fold f (map w) acc.

  Definition to_list : list (M.key * A) := M.elements (map w).
End functions.

(** Representation invariant wrt. functions of type {ffun 'I_size -> A} *)

Section rep.
  Variable A : Type.
  
  Definition rep (w : t A) (f : {ffun 'I_(N.to_nat (size w)) -> A}) : Prop :=
    forall (i : index w), lookup i = f (ordinal_of_index i).

  Variable w : t A.
  Variable f : {ffun 'I_(N.to_nat (size w)) -> A}.
  Hypothesis w_rep : rep f.

  Lemma lookup_ok : forall i : index w, lookup i = f (ordinal_of_index i).
  Proof. apply: w_rep. Qed.

  (** WIP Lemma empty_ok : *)
End rep.    
End AM.

Module DIST.
Record row (A : Type) : Type :=
  mkRow { row_weight : D;
          row_max : D;
          row_arraymap : AM.t (A*D) }.
  
Record t (A : Type) : Type :=
  mk {
      cpmf :> M.t (row A)
           (* [cpmf]: a map from 
                - LEVEL 1: weight level i = [2^i, 2^{i+1})
                - LEVEL 2: weight array containing weights (a,d)
                           in the range of weight level i, along 
                           with the total probability mass for that level *)
    }.

Section functions.
  Variable A : Type.
  
  Definition empty : t A := mk (M.empty _).
  
  (** We assume all weights are between 0 and 1. *)
  
  Definition level_of (d : D) : N.t :=
    match d with
    | Dmake (Zpos x) y => N.sub (N.pos y) (N.log2 (N.pos x))
    | Dmake 0 _ => 0
    | Dmake (Zneg _) _ => 0
    end.

  Compute level_of (Dmake 1 1). (*=1*)
  Compute level_of (Dmake 1 2). (*=2*)  
  (* level_of spec: forall d, 2^{-(level_of d)} <= d < 2^{-(level_of d) - 1}*)

  Program Definition add_weight (a : A) (d : D) (w : t A) : t A :=
    let r := 
        match M.find (level_of d) w with
        | None => mkRow 0%D 0%D (AM.empty _)
        | Some m => m
        end
    in
    let r' :=
        mkRow (Dadd d r.(row_weight))
              (Dmax d r.(row_max))
              (AM.add r.(row_arraymap) (a,d))
    in mk (M.add (level_of d) r' (cpmf w)).
  
  Fixpoint add_weights
             (l : list (A*D))
             (w : t A)
    : t A :=
    match l with
    | nil => w
    | (a,d) :: l' => add_weights l' (add_weight a d w)
    end.

  Definition sum_weights (m : AM.t (A*D)) : D :=
    AM.fold m
      (fun _ (p : A*D) acc => let (a,d') := p in Dadd acc d')
      0%D.

  Definition max_weight (m : AM.t (A*D)) : D :=
    AM.fold m
      (fun _ (p : A*D) acc => let (a,d') := p in Dmax acc d')
      0%D.

  Definition min_weight (m : AM.t (A*D)) : D :=
    AM.fold m
      (fun _ (p : A*D) acc => let (a,d') := p in Dmax d' acc)
      0%D.

      
  (** Updates [w] according to [f], returning the new array map 
      together with any pairs (a,d) that are now mis-leveled (stored 
      in the proj2 array map). *)
  Definition update_level
             (f : A -> D -> D)
             (level : N.t)             
             (m : row A)             
    : (row A * AM.t (A*D)) :=
    (* w': the updated weights *)
    let w' := AM.fmap m.(row_arraymap) (fun p : (A*D) => let (a,d) := p in (a, f a d)) in
    (* split the entries that are now mis-leveled *)
    let g := fun i (p : (A*D)) => let (a,d') := p in N.eqb (level_of d') level in
    let (stay, go) := AM.split w' g in
    (mkRow (sum_weights stay) (max_weight stay) stay, go).

  Lemma update_level_pf f (x y : M.key) w :
    N.eq x y -> update_level f x w = update_level f y w.
  Proof. by move => ->. Qed.
  
  Definition update_weights
             (f : A -> D -> D)
             (w : M.t (row A))
    : t A :=
    let w'':= M.mapi (update_level f) w in
    let w' := M.map fst w'' in
    let removed := M.fold (fun i p l0 => AM.to_list (snd p) ++ l0) w'' nil in
    add_weights
      (List.map snd removed) (mk w').

  (** The distribution's total weight *)
  Definition weight (w : t A) : D :=
    M.fold (fun i r d0 => Dadd r.(row_weight) d0) w D0.

End functions.
End DIST.

Section sampling.
  Variable T : Type. (* randomness oracle state *)
  Variable rand : T -> D*T.
  Variable rand_range : T -> N.t -> N.t*T. (* generate a random integer in range *)
  Hypothesis rand_range_ok :
    forall t n,
      let (n', t') := rand_range t n in 
      (N.to_nat n' < N.to_nat n)%N.
  
  Fixpoint cdf_sample_aux
           (A : Type) (a0 : A)
           (acc r : D) (l : list (D*A))
    : (D * A) :=
    match l with
    | nil => (D0, a0) (*should never occur*)
    | (w, a) :: l' =>
      if Dle_bool acc r && Dle_bool r (Dadd acc w) then
        (w, a)
      else cdf_sample_aux a0 (Dadd acc w) r l'
    end.
  
  (** Use inverse transform sampling to select row. *)
  Definition cdf_sample_row
             (A : Type)
             (w : DIST.t A)
             (t : T)
    : (DIST.row A * T) :=
    let sum := DIST.weight w in  
    let (r, t') := rand t in
    let r' := Dmult r sum in
    let w := cdf_sample_aux
               (DIST.mkRow D0 D0 (AM.empty _))
               D0
               r'
               (map (fun (p : M.key * DIST.row A) =>
                       let (_, r) := p in
                       (r.(DIST.row_weight), r))
                    (M.elements (DIST.cpmf w))) in
    (snd w, t').

  (** Sample a value in range [0..size-1] *)
  Program Definition sample_index
             (t : T)
             (size : N.t)
    : (Index.t size * T) :=
    (@Index.mk size (fst (rand_range t size)) _, snd (rand_range t size)).
  Next Obligation.
    move: (rand_range_ok t size).
    case: (rand_range t size) => //.
  Qed.    

  (** Rejection-sample within row. *)  
  Fixpoint rejection_sample_row_aux
             (A : Type)
             (a0 : A)
             (r : DIST.row A)
             (t : T)
             (n : nat)
    : (A * T) :=
    let w_max := r.(DIST.row_max) in
    let w := r.(DIST.row_arraymap) in 
    let size := w.(AM.size) in 
    match n with
    | O => (a0, t)
    | S n' =>
      let (i, t2) := sample_index t size in
      let (a, d) := AM.lookup i in 
      let (u, t') := rand t2 in      
      if Dle_bool (Dmult u w_max) d then
        (a, t')
      else rejection_sample_row_aux a0 r t' n'
    end.

  Definition rejection_sample_row 
             (A : Type)
             (a0 : A)
             (r : DIST.row A)
             (t : T)
    : (A * T) :=
    rejection_sample_row_aux a0 r t 1000.

  (** The overall sampling procedure. *)
  Definition sample
             (A : Type)
             (a0 : A)
             (w : DIST.t A)
             (t : T)
    : (A * T) :=
    let (r, t2) := cdf_sample_row w t in
    rejection_sample_row a0 r t2.
  
  Fixpoint prod_sample_aux
           (A : Type)
           (a0 : A)
           (acc : M.t A * T)
           (n : nat)
           (p : nat -> DIST.t A)
    : (M.t A * T) :=
    match n with
    | O => acc
    | S n' =>
      let (a, t) := sample a0 (p n') (snd acc) in
      prod_sample_aux a0 (M.add (N.of_nat n') a (fst acc), t) n' p
    end.

  Definition prod_sample
             (num_players : nat)
             (A : Type)
             (a0 : A)
             (p : nat -> DIST.t A)
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
  let _ = Random.self_init () in
  let d = Random.int 256 in
  let zn = Big.of_int d in
  let peight = Big.of_int 8 in
  let q = { num = zn; den = peight }
  in
  Printf.eprintf ""Generated random r = %d"" d; prerr_newline ();
  (q, ())".

(** PRECONDITION: [rand_range t n]: n is Npos p for some p *)
Axiom rand_range : rand_state -> N.t -> (N.t*rand_state). (*in range [0,size-1]*)
Extract Constant rand_range =>
 "fun _ size ->
  let _ = Random.self_init () in
  let d = Random.int (Big.to_int size)
  in
  Printf.eprintf ""Generated in-range random i = %d"" d; prerr_newline ();
  (Big.of_int d, ())".

Axiom rand_range_ok :
  forall t n,
    let (n', t') := rand_range t n in 
    (N.to_nat n' < N.to_nat n)%N.

Definition rsample A (a0 : A) (c : DIST.t A) : A :=
  fst (sample rand rand_range_ok a0 c init_rand_state).

Definition rprod_sample A (a0 : A) (num_players : nat) (p : nat -> DIST.t A) : M.t A :=
  fst (prod_sample rand rand_range_ok num_players a0 p init_rand_state).

Section rsample_cost.
  Context {A : Type} (a0 : A) {num_players : nat}.
  Context `{CCostInstance : CCostClass num_players A}.  

  Definition rsample_ccost (i : N.t) (a : A) (p : nat -> DIST.t A) : D :=
    let m := rprod_sample a0 num_players p in
    ccost i (M.add i a m).
End rsample_cost.

Section expected_rsample_cost.
  Context {A : finType} {Aeq : A -> A -> bool}.
  (*Aeq: not necessarily the equality associated with A's eqType instance.*)
  Context (a0 : A) {num_players : nat}.
  Context `{CGameInstance : cgame num_players A}.    

  Variable (p : nat -> DIST.t A).
  Variable (f : {ffun 'I_num_players -> dist A rat_realFieldType}).
  (* TO BE UPDATED:
  Hypothesis dists_match : forall i : 'I_num_players, dist_cdist_match Aeq (p i) (f i).
  
  Axiom rsample_ccost_expected :
    forall (i : 'I_num_players) (a : A),
      D_to_Q (rsample_ccost a0 (N.of_nat i) a p) =
      rat_to_Q (expectedValue (prod_dist f) (fun x => cost i (upd i a x))).*)
End expected_rsample_cost.

(* Definition fun_of_t *)
(*            (A : Type) *)
(*            (Aeq : A -> A -> bool) *)
(*            (c : t A) : A -> Q := *)
(*   fun a => *)
(*     match findA (Aeq a) c with  *)
(*     | None => 0 *)
(*     | Some d => D_to_Q d *)
(*     end. *)

(* Definition dist_t_match *)
(*            (A : finType) *)
(*            (Aeq : A -> A -> bool)            *)
(*            (c : t A) *)
(*            (d : dist A rat_realFieldType)            *)
(*   : Prop := *)
(*   pmf d = finfun (fun a => Q_to_rat (fun_of_t Aeq c a)). *)
      