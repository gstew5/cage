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

Require Import strings compile orderedtypes dyadic numerics cdist weightsextract lightserver.

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
   Pair (sd, ())".

Axiom ax_recv : forall IN : Type, ax_st_ty -> ax_chan -> (IN * ax_st_ty).
Extract Constant ax_recv =>
(* Read the player actions from the socket; close the socket *)
"fun _ sd ->
   let _ = Printf.eprintf ""Receiving...""; prerr_newline () in
   let in_chan = Unix.in_channel_of_descr sd in
   let cost_vector = Marshal.from_channel in_chan in
   close_in in_chan;
   Printf.eprintf ""Received cost vector...""; prerr_newline ();
   Pair (cost_vector, ())".

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
  Context `{GameTypeInstance : GameType C.A.t num_players}.
  
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
  Admitted. (*TODO*)

  Definition recv (st : ax_st_ty) (ch : ax_chan) : list (C.A.t*D) * ax_st_ty :=
    seq (ax_recv _ st ch)
        (fun pst' =>
           let: (player, p, st') := pst' in
           (cost_vector p player, st')).
  
  Lemma recv_ok :
    forall st ch a,
    exists d,
      [/\ In (a,d) (recv st ch).1
        , Dle D0 d & Dle d D1].
  Proof. Admitted. (*TODO*)

  Lemma recv_nodup :
    forall st ch, NoDupA (fun p q => p.1 = q.1) (recv st ch).1.
  Proof.
    move => st ch; rewrite /recv seqP.
    case E: (ax_recv _ st ch) => [[x y] z] /=.
    apply: cost_vector_nodup.
  Qed.
  End clientCostVectorShim.

  Instance client_ax_oracle {num_players} `{GameType C.A.t num_players}
    : @ClientOracle C.A.t num_players _ _ _ _ :=
    @mkOracle _ _ _ _ _ _
      ax_st_ty empty_ax_st
      ax_chan ax_bogus_chan
      (@recv num_players _ _)
      (@send num_players _ _ _ _)
      (@recv_ok num_players _ _ _ _)
      (@recv_nodup num_players _ _ _ _).
End AxClientOracle.