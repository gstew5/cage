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

Require Import strings compile orderedtypes dyadic numerics cdist weightsextract.

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

Axiom ax_send : forall A : Type, ax_st_ty -> A -> (ax_chan * ax_st_ty).
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

Axiom seq : forall (A B : Type) (a : A) (f : A -> B), B.
Extract Constant seq =>
"fun a b -> 
   let x = a in 
   b x".

Definition send (A : Type) `{Showable A} (a0 : A) (st : ax_st_ty) (l : list (A*D))
  : ax_chan * ax_st_ty :=
  (*TODO: constructing this DIST.t each time is wasteful -- 
    the DIST datastructure should eventually be factored into weightsextract.v*)
  let: d := DIST.add_weights l (DIST.empty _) in  
  seq (rsample a0 d)
      (fun x => seq (eprint_string "Chose action " tt)
                    (fun _ => seq (eprint_showable x tt)
                                  (fun _ => seq (eprint_newline tt)
                                                (fun _ => ax_send st x)))).

Axiom recv : forall A : Type, ax_st_ty -> ax_chan -> (list (A*D) * ax_st_ty).
Extract Constant recv =>
(* Read cost vector from socket, close the socket *)
"fun _ sd ->
   let _ = Printf.eprintf ""Receiving...""; prerr_newline () in
   let in_chan = Unix.in_channel_of_descr sd in
   let cost_vector = Marshal.from_channel in_chan in
   close_in in_chan;
   Printf.eprintf ""Received cost vector...""; prerr_newline ();
   Pair (cost_vector, ())".

Axiom recv_ok :
  forall A (a : A) st ch,
  exists q,
    [/\ In (a, q) (recv _ st ch).1
      , Dle D0 q & Dle q D1].
Axiom recv_nodup :
  forall (A : Type) st ch, NoDupA (fun p q => p.1 = q.1) (recv A st ch).1.

Instance client_ax_oracle : ClientOracle ax_st_ty ax_chan :=
  mkOracle ax_bogus_chan send recv_ok recv_nodup.

(** Test extraction: *)

Extraction "interp" MWU.
