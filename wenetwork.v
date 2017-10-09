Set Implicit Arguments.
Unset Strict Implicit.

Require Import QArith String.
Require Import ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.FSets.FMapAVL Coq.FSets.FMapFacts.
Require Import Structures.Orders NArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Import GRing.Theory Num.Def Num.Theory.

Require Import orderedtypes dyadic compile.

Require Import networkSemantics weightslang weightsextract.

Module WE_NodePkg (A : MyOrderedType).
  Module M := MWU A. Import M.

  Section WE_NodePkg.
    Variable node : Type.
    Variable server_id : node.
    Variable epsQ : D. 
  
  Record ClientPkg : Type :=
    mkClientPkg
      { sent : list (A.t*D)
      ; received : list (A.t*D)
      ; received_ok :
          NoDupA (fun p q => p.1 = q.1) received /\ 
          forall a,
          exists d,
            [/\ In (a,d) received
             , Dle (-D1) d & Dle d D1]
      }.

  Definition init_map := List.map (fun a => (a, D1)) (enumerate A.t).

  Program Definition init_ClientPkg : ClientPkg :=
    @mkClientPkg nil init_map _.
  Next Obligation.
  Admitted.

  Definition simple_oracle_recv
             (pkg : ClientPkg)
             (_ : unit)
    : list (A.t*D) * ClientPkg
    := (pkg.(received), pkg).

  Definition simple_oracle_send
             (pkg : ClientPkg)             
             (d : list (A.t*D))
    : unit * ClientPkg             
    := (tt, mkClientPkg d pkg.(received_ok)).

  Program Instance simpleClientOracle : @ClientOracle A.t := 
    @weightsextract.mkOracle
      _
      ClientPkg
      init_ClientPkg
      unit
      tt
      simple_oracle_recv
      simple_oracle_send
      _ _.
  Next Obligation.
    destruct st.(received_ok) as [A B].
    destruct (B a) as [d [B1 B2]].
    exists d; split; auto.
  Qed.
  Next Obligation.
    destruct st.(received_ok) as [A B]; auto.
  Qed.    

  Definition client_state := (node * com A.t * cstate)%type.

  Definition client_init (id : node) : client_state :=
    match interp (mult_weights_init A.t) (init_cstate epsQ) with
    | None => (id, @CSkip A.t, init_cstate epsQ)
    | Some st => (id, @CSkip A.t, st)
    end.
  
  Definition msg : Type := list (A.t*D).

  Definition event := unit.

  Definition msg_of_cstate (id : node) (st : cstate) : list (packet node msg) :=
    (id, st.(SOracleSt).(sent), server_id) :: nil.

  Program Definition install_cost_vec
          (cost_vec : list (A.t*D))
          (st : cstate)
    : cstate :=
    mkCState
      st.(SCosts)
      st.(SPrevCosts)
      st.(SWeights)
      st.(SEpsilon)
      st.(SOutputs)
      st.(SChan)
      (@mkClientPkg
        st.(SOracleSt).(sent)
        (*TODO: will need to decide here whether cost_vec satisfies received_ok*)
        st.(SOracleSt).(received)
        _).
  Next Obligation.
  Admitted.
            
  Definition client_recv (m : msg) (from : node) (cst : client_state)
    : client_state * seq (packet node msg) * seq event
    := let st := install_cost_vec m cst.2
       in match interp (mult_weights_body A.t) st with
          | None =>
            (cst, nil, nil) 
          | Some st' => 
            ((cst.1.1, @CSkip A.t, st') : client_state,
             (cst.1.1, st'.(SOracleSt).(sent), server_id) :: nil,
             nil)
          end.
                   
  Definition client : NodePkg node msg event :=
    @mkNodePkg
      _ _ _
      client_state
      (fun id =>
         match client_init id with
         | (x, c, cst) => ((x,c,cst), msg_of_cstate x cst, nil)
         end)
      client_recv
      (server_id (*bogus*), @CSkip A.t, init_cstate epsQ).
  End WE_NodePkg.
End WE_NodePkg.  