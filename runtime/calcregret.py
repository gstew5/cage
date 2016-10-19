#!/usr/bin/python

import sys
import re
import math

# Given the output of [./mwu.native], calculate 
# the client's regret at each iteration t=0..T-1.
#
# USAGE: ./calcregret.py [client_output_file] epsilon

filename = sys.argv[1]
epsilon = float(sys.argv[2])
f = open(filename, 'r')

processing_costs = False
t = 0
costs_tbl = {}
chosen_tbl = {}
costs_tbl[0] = {}

for line in f:
    if processing_costs:
        costs = re.sub("[,]", " ", line).split()
        if costs[0] == "Generated": processing_costs = False
        else: costs_tbl[t-1][costs[0]] = float(costs[1]) / float(costs[2])

    words = re.sub("[^\w]", " ", line).split()        
    if words[0] == "Received": processing_costs = True
    if words[0] == "Chose":
        chosen_tbl[t] = words[2]        
        t = t + 1
        costs_tbl[t-1] = {}

# avg. cost of action a in [0, t]
def avg_cost_of(a, t):
    acc = 0
    for i in xrange(0, t+1):
        acc = acc + costs_tbl[t][a]
    return acc / (t+1)

# running avg. cost in [0, t]
def avg_cost(t):
    acc = 0
    for i in xrange(0, t+1):
        acc = acc + costs_tbl[i][chosen_tbl[i]]
    return acc / (t+1)

# min average cost in [0, t]
def opt(t):
    c = avg_cost(t)
    for a in costs_tbl[0]:
        if avg_cost_of(a, t) < c:
            c = avg_cost_of(a, t)
    return c

def size_statespace():
    return len(costs_tbl[0])

def predicted_regret(t):
    return epsilon + math.log(size_statespace()) / (epsilon * float(t+1))

costs_tbl.pop(len(costs_tbl) - 1)   # = {}
chosen_tbl.pop(len(chosen_tbl) - 1) # = we don't care because no cost vector was returned

for t in costs_tbl:
    print "ROUND", t
    print "Chose", chosen_tbl[t]
    print "Optimal", opt(t)    
    print "Cost", avg_cost(t)
    print "Regret", (avg_cost(t) - opt(t))
    print "Regret bound", predicted_regret(t)
    for a in costs_tbl[t]:
        print " ", a, costs_tbl[t][a]


        
