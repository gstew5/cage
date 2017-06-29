#!/usr/bin/python

from __future__ import division # enable python3 division of integers
import sys
import re
import math

# Given the output of [./mwu.native], calculate
# the client's regret at each iteration t=0..T-1.
#
# USAGE: ./calcregret.py [infile] [outfile] [epsilon] 

infile = sys.argv[1]
outfile = sys.argv[2]
epsilon = float(sys.argv[3])
f = open(infile, 'r')
of = open(outfile, 'a')

processing_costs = False
processing_weights = False
t = 0
costs_tbl = {}
chosen_tbl = {}
costs_tbl[0] = {}
weights_tbl = {}
weights_tbl[0] = {}

for line in f:
    if processing_costs:
        costs = re.sub("[,]", " ", line).split()
        if costs[0] == "Weights": processing_costs = False
        else: costs_tbl[t-1][costs[0]] = float(int(costs[1]) /
                                               int(costs[2]))

    if processing_weights:
        weights = re.sub("[,]", " ", line).split()
        if weights[0] == "Generated": processing_weights = False
        else:
            weights_tbl[t][weights[0]] = float(int(weights[1]) /
                                               int(weights[2]))
        
    words = re.sub("[^\w]", " ", line).split()
    if words[0] == "Received": processing_costs = True
    if words[0] == "Weights":
        weights_tbl[t] = {}
        processing_weights = True
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

# expected cost at t
def exp_cost(t):
    acc = 0
    gamma = 0 # the sum of the weights at t
    m = weights_tbl[t]

    for i in xrange(0, len(weights_tbl[t])):
        gamma = gamma + m[m.keys()[i]]
    
    for i in xrange(0, len(weights_tbl[t])):
        action = m.keys()[i]
        acc = acc + m[action]*costs_tbl[t][action]
    return acc / gamma

# time-averaged cumulative expected cost in [0, t]
def avg_exp_cost(t):
    acc = 0
    for i in xrange(0, t+1):
        acc = acc + exp_cost(t)
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
    return epsilon + math.log(size_statespace(), math.e) / (epsilon * float(t+1))

def best_predicted_regret(t):
    return 2 * math.sqrt(math.log(size_statespace(), math.e) / float(t+1))

costs_tbl.pop(len(costs_tbl) - 1)   # = {}
chosen_tbl.pop(len(chosen_tbl) - 1) # = we don't care because no cost vector was returned

for t in costs_tbl:
    # for debugging, we print the following to stdout
    print "ROUND", t
    print "Chose", chosen_tbl[t]
    print "Optimal", opt(t)    
    #print "Cost", avg_cost(t)
    print "Cost", avg_exp_cost(t)    
    #regret = avg_cost(t) - opt(t)
    regret = avg_exp_cost(t) - opt(t)    
    print "Regret", regret
    print "Regret bound", predicted_regret(t)
    for a in costs_tbl[t]:
        print " ", a, costs_tbl[t][a]
        
    # for later aggregation and plotting, we print the following data to [outfile]:
    #   round_number, optimal avg cost, client's avg cost, client's regret, regret bound
    print >> of, t, ",", opt(t), ",", avg_exp_cost(t), ",", regret, ",", predicted_regret(t), ",", best_predicted_regret(t)
        
