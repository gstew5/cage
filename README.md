# Cage 

![John Cage: Variations I](/img/cage_variations.jpg?raw=true "John Cage: Variations I")

Cage is a library and set of tools in Ssreflect-Coq for implementing and verifying convergence and quality bounds on game-based distributed systems such as [distributed routers](https://github.com/gstew5/cage/blob/master/routing.v) and [load balancers](https://github.com/gstew5/cage/blob/master/loadbalancing.v). Cage includes, as a subcomponent, a verified implementation of the multiplicative weights update ([MWU](https://www.cs.princeton.edu/~arora/pubs/MWsurvey.pdf)) algorithm: 

* High-level implementation of MWU [weights.v](https://github.com/gstew5/cage/blob/master/weights.v) 
* MWU DSL [weightslang.v](https://github.com/gstew5/cage/blob/master/weightslang.v)
* MWU DSL interpreter, along with correctness results [weightsextract.v](https://github.com/gstew5/cage/blob/master/weights.v)

An introduction to the research ideas underlying Cage (in the form of a technical paper) is forthcoming. 

## Prerequisites

* Coq 8.5
* Ssreflect 1.6
* OCaml (>= 4.02.1)

## Build Instructions

* Type `make` in the toplevel directory.
