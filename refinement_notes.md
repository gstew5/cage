# Top-level Refinement Layers

* [toverdi.v]: Verdi semantics and simulation from verdi to World (the state type of LOW and INT and INTRel) (QUESTION: Do we impose a hypothesis on executions of the Verdi network semantics? That there's no infinite chain of silent events?)
* [networkSemanticsNoBatch.v]: LOW to INT (Sam -- IN PROGRESS) 
* [networkSemanticsNoBatch.v]: INT to INTRel (Currently broken; Sam will fix)
* HOLE
* [we2wl.v]: INTRel(WE) to INTRel(WL) (Nate/Gordon -- IN PROGRESS)
* [wlnetwork.v]: INTRel(WL) to machine (DONE)

# Languages

* [toverdi.v]: Verdi network language (parameterized by client and server `NodePkg`s?)
* [networkSemanticsNoBatch.v]: main datatype is `World`, file defines the LOW, INT, and INTRel semantics. LOW and INT operate on `World`; INTRel operates on `RWorld`s
* [wenetwork.v]: `NodePkg`s for `WE`-level MWU server and client
* [wlnetwork.v]: `NodePkg`s for `WL`-level MWU server and client
* [machine.v]: machine

# Assumptions

LOW to INT makes the following assumptions about the `World` (in particular, the instantiation of `NodePkg`): 
1. Nodes are "honest": When they produce a new message, it's correctly labeled with origin and always sent to Server (if being sent from Client) and vice versa.
2. On init steps, Clients send one message to Server, Server sends no messages.
3. There's a unique Server.
4. There's a finite number of Clients.
5. Clients send exactly one message when poked (recv).
6. ?

At some point, we need to prove that these assumptions hold of the specific `WE` `NodePkg`s for MWU. (Nathan/Sam/Gordon)

# Action Items

1. Finish LOW to INT (Sam)
2. Finish INTRel(WE) to INTRel(WL) (Nate/Gordon)
3. Prove that LOW to INT assumptions are satisfied by the WE MWU NodePkgs.
