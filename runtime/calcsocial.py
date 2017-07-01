#!/usr/bin/python

# This script takes the results from running calcregret.py for each
# client and computes the average social cost (sum of client costs) at
# each time step t. By cost we mean the time-averaged cumulative cost up
# to time t.

import sys, csv
import numpy as np

num_clients = int(sys.argv[1])
num_rounds = int(sys.argv[2])
infile_prefix = sys.argv[3]
outfile = sys.argv[4]

data = []

for i in range(1, num_clients+1):
    with open(infile_prefix + str(i) + '.txt', 'r') as f:
        client_data = np.array(list(csv.reader(f, delimiter=',')))
        # Average client data over all rounds
        client_data = np.mean(np.array(np.split(client_data, num_rounds))
                              .astype(float), axis=0)
        data.append(client_data)

# Sum over all clients
data = np.sum(np.array(data), axis=0)

# Extract costs
costs = data[:,2]

# Write to output file
costs.tofile(outfile, sep=',')
