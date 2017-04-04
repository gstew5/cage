Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith.

(*Avoid clash with Ssreflect*)
Delimit Scope Q_scope with coq_Qscope.
Definition Qcoq := Q.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import numerics dyadic combinators games compile orderedtypes.
Require Import weightsextract client lightserver.

(* 1. CONFIG -> GameType 

   FIXME: assumes ccost is in range. This is a result of refinement assumptions
   but hasn't been propagated correctly yet. 

 *)

Module GameType_of_CONFIG (C : CONFIG).
  Definition A_cost_instance := C.A.cost_instance C.num_players.
  Existing Instance A_cost_instance.
  (* FIXME: Wrt. the axioms below, we need to propagate the following assumptions: 
      1) There's a cgame associated with C.A, which should imply 
      2) a refineCostClass instance for (ccost), and
      3) a refineTypeClass instance for (enumerate). *)
  Axiom ccost_ok : forall (p : M.t C.A.t) (player : N), (*TODO: result of cgame*)
      (0 <= (ccost) player p)%D /\ ((ccost) player p <= 1)%D.
  Axiom enum_nodup :
    SetoidList.NoDupA (fun x : C.A.t => [eta eq x]) (enumerate C.A.t). (*TODO: result of cgame*)
  Axiom enum_total : forall a : C.A.t, List.In a (enumerate C.A.t). (*TODO: result of cgame*)
  Definition gametype_instance : @GameType C.A.t C.num_players _ _ _ :=
    @mkGameType C.A.t C.num_players _ _ _ C.A.t0 ccost_ok enum_nodup enum_total.
End GameType_of_CONFIG.

(* 2. CONFIG -> Client *)

Module Client_of_CONFIG (C : CONFIG).
  (* the client module *)
  Module MWU := MWU C.A.
  (* its GameType instance *)
  Module GT := GameType_of_CONFIG C.
  Existing Instance GT.gametype_instance.
  (* other required instances *)  
  Existing Instance C.A.enumerable.
  Definition A_cost_instance := C.A.cost_instance C.num_players.
  Existing Instance A_cost_instance.
  Module ClientOracle := AxClientOracle C.
  Existing Instance ClientOracle.client_ax_oracle.
  Definition mwu0 (eps : D) (nx : N.t) :=
    MWU.interp (weightslang.mult_weights C.A.t nx) (MWU.init_cstate eps).
  Definition mwu := mwu0 C.epsilon C.num_rounds.
End Client_of_CONFIG.

(* 3. CONFIG -> Server *)
  
Module Server_of_CONFIG (C : CONFIG).
  Module Server := Server C.
  Module ServerOracle := AxServerOracle C.
  Existing Instance ServerOracle.ax_oracle.
  Definition run := Server.server (@Server.init_state result _ _).
End Server_of_CONFIG.
