#!/usr/bin/python

import sys
import csv
import matplotlib.pyplot as plt
import matplotlib.font_manager as fmr
import numpy as np

# Given the output of [./calcregret.py infile datafile epsilon],
# plot the data in datafile.
#
# USAGE: ./plotregret.py [datafile]

datafile = sys.argv[1]
opt = {}     # optimal cost
opt_mean = {}
opt_std = {}
cost = {}     # client cost cost
cost_mean = {}
cost_std = {}
regret = {}  # client regret
regret_mean = {}
regret_std = {}
bound = {}   # analytical regret bound
bound_mean = {}
bound_std = {}

with open(datafile, 'r') as csvfile:
    reader = csv.reader(csvfile, delimiter=',')
    l = list(reader)
    # initialize dictionaries
    for row in l:
        opt[int(row[0])] = []
        opt_mean[int(row[0])] = 0
        opt_std[int(row[0])] = 0
        cost[int(row[0])] = []
        cost_mean[int(row[0])] = 0
        cost_std[int(row[0])] = 0
        regret[int(row[0])] = []
        regret_mean[int(row[0])] = 0
        regret_std[int(row[0])] = 0
        bound[int(row[0])] = []
        bound_mean[int(row[0])] = 0
        bound_std[int(row[0])] = 0
    for row in l:
        opt[int(row[0])].append(float(row[1]))
        cost[int(row[0])].append(float(row[2]))
        regret[int(row[0])].append(float(row[3]))
        bound[int(row[0])].append(float(row[4]))                        

for k in opt:
    opt_mean[k] = np.mean(opt[k])
    opt_std[k] = np.std(opt[k])
for k in cost:
    cost_mean[k] = np.mean(cost[k])
    cost_std[k] = np.std(cost[k])
for k in regret:
    regret_mean[k] = np.mean(regret[k])
    regret_std[k] = np.std(regret[k])
for k in bound:
    bound_mean[k] = np.mean(bound[k])
    bound_std[k] = np.std(bound[k])

with plt.xkcd():
    fig = plt.figure()
    plt.title('Experimental Regret: Routing Game', size=18)
    plt.yscale('log')
    plt.minorticks_off()
    plt.xlim([-1,regret_mean.keys()[len(regret_mean.keys())-1]+1])
    plt.xticks(range(len(regret_mean)), regret_mean.keys())
    plt.plot(range(len(bound_mean)), bound_mean.values(), 'c--')
    (_, caps, _) = plt.errorbar(    
        range(len(cost_mean)), cost_mean.values(),
        yerr=cost_std.values(), fmt='bo', capsize=4, elinewidth=2)
    for cap in caps: cap.set_markeredgewidth(2)    
    plt.plot(range(len(opt_mean)), opt_mean.values(), 'g-')        
    (_, caps, _) = plt.errorbar(
        range(len(regret_mean)), regret_mean.values(),
        yerr=regret_std.values(), fmt='rD', capsize=4, elinewidth=2)
    for cap in caps: cap.set_markeredgewidth(2)
    plt.tick_params(axis='both', which='major', labelsize=16)
    plt.xlabel('#Iterations', size=18)
    plt.legend(['Regret Bound','MWU Cost','Optimal Cost','MWU Regret'])            

plt.show()    
