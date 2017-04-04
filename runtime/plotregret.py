#!/usr/bin/python

import sys
import csv
import matplotlib.pyplot as plt
import matplotlib.font_manager as fmr
from matplotlib.ticker import ScalarFormatter
import numpy as np
import scipy.stats as ss

# Given the output of [./calcregret.py infile datafile epsilon],
# plot the data in datafile.
#
# USAGE: ./plotregret.py [datafile] [sample-size] [confidence-level]

datafile = sys.argv[1]
samplesize = int(sys.argv[2])
confidencelevel = float(sys.argv[3])
opt = {}     # optimal cost
opt_mean = {}
opt_std = {}
cost = {}     # client cost cost
cost_mean = {}
cost_std = {}
regret = {}  # client regret
regret_mean = {}
regret_std = {}
regret_sem = {} # standard error of regret sample mean
bound = {}   # analytical regret bound
bound_mean = {}
bound_std = {}
bestbound = {}   # best analytical regret bound, assuming right epsilon
bestbound_mean = {}
bestbound_std = {}

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
        bestbound[int(row[0])] = []
        bestbound_mean[int(row[0])] = 0
        bestbound_std[int(row[0])] = 0
    for row in l:
        opt[int(row[0])].append(float(row[1]))
        cost[int(row[0])].append(float(row[2]))
        regret[int(row[0])].append(float(row[3]))
        bound[int(row[0])].append(float(row[4]))
        bestbound[int(row[0])].append(float(row[5]))        

for k in opt:
    opt_mean[k] = np.mean(opt[k])
    opt_std[k] = np.std(opt[k])
for k in cost:
    cost_mean[k] = np.mean(cost[k])
    cost_std[k] = np.std(cost[k])
for k in regret:
    regret_mean[k] = np.mean(regret[k])
    regret_std[k] = np.std(regret[k])
    regret_sem[k] = ss.sem(regret[k])    
for k in bound:
    bound_mean[k] = np.mean(bound[k])
    bound_std[k] = np.std(bound[k])
for k in bestbound:
    bestbound_mean[k] = np.mean(bestbound[k])
    bestbound_std[k] = np.std(bestbound[k])

fig = plt.figure(figsize=(8,8), dpi=120)
    
# These are the "Tableau 20" colors as RGB.
# From: http://www.randalolson.com/2014/06/28/how-to-make-beautiful-data-visualizations-in-python-with-matplotlib/
tableau20 = [(31, 119, 180), (174, 199, 232), (255, 127, 14), (255, 187, 120),
             (44, 160, 44), (152, 223, 138), (214, 39, 40), (255, 152, 150),
             (148, 103, 189), (197, 176, 213), (140, 86, 75), (196, 156, 148),
             (227, 119, 194), (247, 182, 210), (127, 127, 127), (199, 199, 199),
             (188, 189, 34), (219, 219, 141), (23, 190, 207), (158, 218, 229)]

# Scale the RGB values to the [0, 1] range, which is the format matplotlib accepts.
for i in range(len(tableau20)):
    r, g, b = tableau20[i]
    tableau20[i] = (r / 255., g / 255., b / 255.)

# Remove the plot frame lines. They are unnecessary chartjunk.
ax = plt.subplot(111)
ax.spines["top"].set_visible(False)
ax.spines["bottom"].set_visible(False)
ax.spines["right"].set_visible(False)
ax.spines["left"].set_visible(False)

# Ensure that the axis ticks only show up on the bottom and left of the plot.
# Ticks on the right and top of the plot are generally unnecessary chartjunk.
ax.get_xaxis().tick_bottom()
ax.get_yaxis().tick_left()
## END Randal Olson stuff

plt.title('Load Balancing', size=32)
plt.yscale('symlog',linthreshy=0.01) #so we properly support negative values (error bars)
plt.minorticks_off()
plt.xlim([-1,regret_mean.keys()[len(regret_mean.keys())-1]+1])
plt.plot(range(len(bound_mean)), bound_mean.values(), '--', color=tableau20[0], linewidth=4)
plt.plot(range(len(cost_mean)), cost_mean.values(), '-', color=tableau20[1], linewidth=4)

degrees_freedom = np.full(len(regret_sem), samplesize-1)
errorbars = ss.t.ppf((1+confidencelevel)/2., degrees_freedom)*regret_sem.values()

(_, caps, _) = plt.errorbar(
    range(len(regret_mean)),
    regret_mean.values(),
    yerr=errorbars,
    fmt='D',
    capsize=4,
    elinewidth=2,
    color=tableau20[6])
    
plt.plot(range(len(opt_mean)), opt_mean.values(), '-', color=tableau20[4], linewidth=4)
plt.tick_params(axis='both', which='major', labelsize=20)
plt.xlabel('Iterations', size=24)
plt.ylabel('Regret, Cost', size=24)    
plt.legend(['Regret Bound','MWU Cost','MWU Regret','Best Fixed Action'], fontsize=20, loc='upper right')
for axis in [ax.xaxis, ax.yaxis]:
    axis.set_major_formatter(ScalarFormatter())

plt.show()    
