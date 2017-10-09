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

Require Import orderedtypes dyadic compile listlemmas.

Require Import networkSemantics weightslang weightsextract.

Module WE_NodePkg (A : MyOrderedType).
  Module M := MWU A. Import M.

  Section WE_NodePkg.
    Variable enum_ok : @Enum_ok A.t _.
    Variable node : Type.
    Variable server_id : node.
    Variable epsQ : D. 

  Definition premsg : Type := list (A.t*D).
    
  Definition premsg_ok (m : premsg) :=
    NoDupA (fun p q => p.1 = q.1) m /\ 
    forall a,
    exists d,
      [/\ In (a,d) m
        , Dle (-D1) d & Dle d D1].

  Record msg : Type :=
    mkMsg
      { the_msg :> premsg
      ; msg_ok : premsg_ok the_msg }.

  Inductive MSG : Type :=
  | TO_SERVER : premsg -> MSG
  | TO_CLIENT : msg -> MSG.
  
  Record ClientPkg : Type :=
    mkClientPkg
      { sent : premsg
      ; received : msg }.

  Definition init_map := List.map (fun a => (a, D1)) (enumerate A.t).

  Lemma init_map_ok : 
    NoDupA (fun p q : A.t * D => p.1 = q.1) init_map /\
    (forall a : A.t,
        exists d : D,
          [/\ In (a, d) init_map, ({| num := -2; den := 1 |} <= d)%DRed & (d <= 1)%DRed]).
  Proof.
    case: enum_ok => H1 H2; split; first by apply: nodupa_fst_pair.
    move => a; exists 1%D; split => //; rewrite /init_map; move: (H2 a).
    move: (enumerate A.t); elim => //= ax l IH; case.
    { by move => ->; left. }
    by move => H3; right; apply: IH.
  Qed.
  
  Definition init_ClientPkg : ClientPkg :=
    @mkClientPkg nil (mkMsg init_map_ok).

  Definition simple_oracle_recv
             (pkg : ClientPkg)
             (_ : unit)
    : list (A.t*D) * ClientPkg
    := (pkg.(received).(the_msg), pkg).

  Definition simple_oracle_send
             (pkg : ClientPkg)             
             (d : list (A.t*D))
    : unit * ClientPkg            
    := (tt, mkClientPkg d pkg.(received)).

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
    destruct st.(received) as [A B].
    destruct B as [B C].
    destruct (C a) as [d [B1 B2]].
    exists d; split; auto.
  Qed.
  Next Obligation.
    destruct st.(received) as [A B]; destruct B; auto.
  Qed.    

  Definition client_state := (node * com A.t * cstate)%type.

  Definition client_init (id : node) : client_state :=
    match interp (mult_weights_init A.t) (init_cstate epsQ) with
    | None => (id, @CSkip A.t, init_cstate epsQ)
    | Some st => (id, @CSkip A.t, st)
    end.

  Definition event := unit.

  Definition MSG_of_cstate (id : node) (st : cstate) : list (packet node MSG) :=
    (id, TO_SERVER (st.(SOracleSt).(sent)), server_id) :: nil.

  Definition install_cost_vec
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
        st.(SOracleSt).(received)).
            
  Definition client_recv
             (m : MSG)
             (from : node)
             (cst : client_state)
    : client_state * seq (packet node MSG) * seq event
    := match m with
       | TO_CLIENT m' => 
         let st := install_cost_vec m'.(the_msg) cst.2
         in match interp (mult_weights_body A.t) st with
            | None =>
              (cst, nil, nil) 
            | Some st' => 
              ((cst.1.1, @CSkip A.t, st') : client_state,
               (cst.1.1, TO_SERVER (st'.(SOracleSt).(sent)), server_id) :: nil,
               nil)
            end
       | TO_SERVER _ => (cst, nil, nil)
       end.
                   
  Definition client : NodePkg node MSG event :=
    @mkNodePkg
      _ _ _
      client_state
      (fun id =>
         match client_init id with
         | (x, c, cst) => ((x,c,cst), MSG_of_cstate x cst, nil)
         end)
      client_recv
      (server_id (*bogus*), @CSkip A.t, init_cstate epsQ).
  End WE_NodePkg.
End WE_NodePkg.  