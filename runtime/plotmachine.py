#!/usr/bin/python

import sys, csv
from math import log, sqrt
import matplotlib.pyplot as plt
import matplotlib.font_manager as fmr
from matplotlib.ticker import ScalarFormatter
import numpy as np
import scipy.stats as ss

# Parse args
datafile                       = sys.argv[1]
num_clients, size_A            = map(int, sys.argv[2:4])
lam, mu, eta, eta_ideal, OPT   = map(float, sys.argv[4:9])

# This corresponds to [r] in perstep_weights_noregret' in weights.v.
eta_diff = eta - eta_ideal

# Normal regret bound per player (perstep_weights_noregret in weights.v).
# This is the one currently used in mwu_ultBounds in machine.v.
def regret1(t):
    return (eta + log(size_A) / (eta * t))

# Better regret bound (perstep_weights_noregret')
def regret2(t):
    return (1 + eta_diff) * sqrt(log(size_A) / t) + \
        sqrt(log(size_A) / t) / (1 + eta_diff)

# Ideal regret bound
def regret3(t):
    return 2 * sqrt(log(size_A) / t)

# Compute bound on social cost given a regret bound function.
def social_cost_bound(regret_bound_f, t):
    return lam / (1 - mu) * OPT + num_clients * regret_bound_f(t) / (1 - mu)

# Read in the social costs data
social_costs = np.loadtxt(datafile, delimiter=',')

# Total number of iterations
T = social_costs.shape[0]

# Compute the social cost bounds for each iteration
social_cost_bounds1 = [social_cost_bound(regret1, t) for t in range(1, T+1)]
social_cost_bounds2 = [social_cost_bound(regret2, t) for t in range(1, T+1)]
social_cost_bounds3 = [social_cost_bound(regret3, t) for t in range(1, T+1)]
cost_ratios         = [x / OPT for x in social_costs]

############
# PLOT STUFF

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

plt.title('Routing', size=32)
# plt.yscale('symlog',linthreshy=0.01) #so we properly support negative values (error bars)
plt.minorticks_off()
plt.ylim([0,5])
# plt.xlim([-1,regret_mean.keys()[len(regret_mean.keys())-1]+1])
plt.plot(range(T), social_costs, '-', color=tableau20[0], linewidth=4)
# plt.plot(range(len(bestbound_mean)), bestbound_mean.values(), '--',
#          color=tableau20[0], linewidth=4)
plt.plot(range(T), cost_ratios, '-', color=tableau20[1], linewidth=4)
plt.plot(range(T), social_cost_bounds1, '--', color=tableau20[2], linewidth=4)
plt.plot(range(T), social_cost_bounds2, '--', color=tableau20[3], linewidth=4)
plt.plot(range(T), social_cost_bounds3, '--', color=tableau20[4], linewidth=4)

plt.plot(range(T), np.full(T, OPT), '-', color=tableau20[5], linewidth=4)

# degrees_freedom = np.full(len(regret_sem), samplesize-1)
# errorbars = ss.t.ppf((1+confidencelevel)/2., degrees_freedom)*regret_sem.values()

# (_, caps, _) = plt.errorbar(
#     range(len(regret_mean)),
#     regret_mean.values(),
#     yerr=errorbars,
#     fmt='D',
#     capsize=4,
#     elinewidth=2,
#     color=tableau20[6],
#     label='MRU Regret')

# plt.plot(range(len(opt_mean)), opt_mean.values(), '-', color=tableau20[4],
#          linewidth=4)

plt.tick_params(axis='both', which='major', labelsize=20)
plt.xlabel('Iterations', size=24)
plt.ylabel('Cost', size=24)
# plt.legend(['Regret Bound','MWU Cost','MWU Regret','Best Fixed Action'], fontsize=20, loc='upper right')
plt.legend(['Social Cost', 'Cost Ratio', 'Cost Bound 1', 'Cost Bound 2',
            'Ideal Cost Bound', 'Optimal Cost'], fontsize=20, loc='upper right')
# plt.legend(['Social Cost', 'Cost Ratio', 'Cost Bound 1', 'Cost Bound 2',
#             'Optimal Cost'], fontsize=20, loc='upper right')
for axis in [ax.xaxis, ax.yaxis]:
    axis.set_major_formatter(ScalarFormatter())

plt.savefig('machine.png')
plt.show()
