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
        OUVerT.dyadic OUVerT.numerics cdist MWU.weightsextract
        lightserver.

(** Axiomatized client oracle *)
Axiom ax_st_ty : Type.
Extract Constant ax_st_ty => "unit".
Axiom empty_ax_st : ax_st_ty.
Extract Constant empty_ax_st => "()".
  
(** A channel *)
Axiom ax_chan : Type.
Extract Constant ax_chan => "Unix.file_descr".
Axiom ax_bogus_chan : ax_chan.
Extract Constant ax_bogus_chan => "Unix.stderr".
  
Axiom ax_send : forall OUT : Type, ax_st_ty -> OUT -> (ax_chan * ax_st_ty).
Extract Constant ax_send =>
(* Create socket, connect to server, send action, return socket. *)
(* Need to know IP address of the server, but it's also possible to do
   host name resolution. *)
"fun _ a ->
   let _ = Printf.eprintf ""Sending...""; prerr_newline () in
   let sd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
   Unix.connect sd (Unix.ADDR_INET
     (Unix.inet_addr_of_string ""127.0.0.1"", 13337));
   let out_chan = Unix.out_channel_of_descr sd in
   Marshal.to_channel out_chan a [];
   flush out_chan;
   Printf.eprintf ""Sent value...""; prerr_newline ();
   (sd, ())".

Axiom ax_recv : forall IN : Type, ax_st_ty -> ax_chan -> (IN * ax_st_ty).
Extract Constant ax_recv =>
(* Read the player actions from the socket; close the socket *)
"fun _ sd ->
   let _ = Printf.eprintf ""Receiving...""; prerr_newline () in
   let in_chan = Unix.in_channel_of_descr sd in
   let cost_vector = Marshal.from_channel in_chan in
   close_in in_chan;
   Printf.eprintf ""Received cost vector...""; prerr_newline ();
   (cost_vector, ())".

(*MOVE*)
Axiom seq : forall (A B : Type) (a : A) (f : A -> B), B.
Extract Constant seq =>
"fun a b -> 
 let x = a in 
 b x".
Axiom seqP :
  forall A B (a : A) (f : A -> B),
    seq a f = f a.
(*END MOVE*)  

Module AxClientOracle (C : CONFIG).
  Module Wire := WireFormat_of_CONFIG C.
  Definition OUT := Wire.CLIENT_TO_SERVER.
  Definition IN := Wire.SERVER_TO_CLIENT.  
  
  Section clientCostVectorShim.
  Variable num_players : nat.
  Context `{game_instance : GameType C.A.t}.
  
  Definition send (st : ax_st_ty) (l : list (C.A.t*D))
    : ax_chan * ax_st_ty :=
    (*TODO: constructing this DIST.t each time is wasteful -- 
      the DIST datastructure should eventually be factored into weightsextract.v*)
    let: d := DIST.add_weights l (DIST.empty _) in
    seq (seq (eprint_string "Weights table..." tt)
             (fun _ => seq (eprint_newline tt)
                           (fun _ => print_Dvector l tt)))
        (fun _ => seq (rsample a0 d)
                        (fun x => seq (eprint_string "Chose action " tt)
                                    (fun _ => seq (eprint_showable x tt)
                                                  (fun _ => seq (eprint_newline tt)
                                                                (fun _ => ax_send st x))))).
  
  (** The cost vector for [player]. [p] is a map from player indices 
      to their sampled strategies. *)
  Definition cost_vector (p : M.t C.A.t) (player : N) : list (C.A.t * D) :=
    List.fold_left
    (fun l a => (a, ccost player (M.add player a p)) :: l)
      (enumerate C.A.t)
      nil.

  Lemma cost_vector_nodup p player :
    NoDupA (fun p q => p.1 = q.1) (cost_vector p player).
  Proof.
    rewrite /cost_vector -fold_left_rev_right.
    generalize enum_nodup; move: (enumerate C.A.t) => l H.
    have H2: NoDupA (fun x : C.A.t => [eta eq x]) (List.rev l).
    { apply NoDupA_rev => //.
      by constructor => // => x y z -> <-. }
    move {H}; move: H2; move: (List.rev l) => l0.
    elim: l0 => //= a l0 IH H2; constructor.
    { move => H3.
      have H4: InA (fun x y => x=y) a l0.
      { clear -H3; move: H3; elim: l0 => //=.
        { inversion 1. }
        move => a0 l IH H; inversion H; subst.
        { by simpl in H1; subst a0; constructor. }
        by apply: InA_cons_tl; apply: IH. }
      by inversion H2; subst. }
    by apply: IH; inversion H2; subst.
  Qed.      

  Definition recv (st : ax_st_ty) (ch : ax_chan) : list (C.A.t*D) * ax_st_ty :=
    seq (ax_recv _ st ch)
        (fun pst' =>
           let: (player, p, st') := pst' in
           (cost_vector p player, st')).
  
  Lemma recv_ok :
    forall st ch a,
    exists d,
      [/\ In (a,d) (recv st ch).1
        , Dle (-D1) d & Dle d D1].
  Proof.
    rewrite /recv /cost_vector => st ch a.
    case: (ax_recv _ _ _) => [][]a0 b b0; rewrite seqP => /=.
    generalize (enum_total); move/(_ a) => H.
    exists ((ccost) a0 (M.add a0 a b)).
    split => //.
    { rewrite -fold_left_rev_right.
      have H2: In a (List.rev (enumerate C.A.t)).
      { by rewrite -in_rev. }
      move: H2 {H}; elim: (List.rev (enumerate C.A.t)) => // a1 l IH.
      inversion 1; subst; first by left.
      by right; apply: IH. }
    { generalize (ccost_ok (M.add a0 a b) a0); case => H1 H2.
      apply: Qle_trans; last by apply: H1.
      by []. }
    by generalize (ccost_ok (M.add a0 a b) a0); case. 
  Qed.    

  Lemma recv_nodup :
    forall st ch, NoDupA (fun p q => p.1 = q.1) (recv st ch).1.
  Proof.
    move => st ch; rewrite /recv seqP.
    case E: (ax_recv _ st ch) => [[x y] z] /=.
    apply: cost_vector_nodup.
  Qed.
  End clientCostVectorShim.

  Program Instance client_ax_oracle
            {num_players : nat}
           `{GameType C.A.t num_players}
    : @ClientOracle C.A.t :=
    @mkOracle C.A.t 
      ax_st_ty empty_ax_st
      ax_chan ax_bogus_chan
      (fun _ _ => (true,_)) (*presend*)
      (@recv num_players _ _)
      (fun _ _ => true) (*prerecv*)     
      (@send num_players _ _ _ _ _)
      _
      _.
  Next Obligation.
    eauto using (@recv_ok num_players _ _ _ _ _).
  Defined.
  Next Obligation.
    eauto using (@recv_nodup num_players _ _ _).
  Defined.

End AxClientOracle.