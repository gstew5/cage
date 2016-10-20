#!/bin/bash

EPSILON=0.25
OUTFILE=out.txt

# kill ./server.native if it's currently running
pkill -f ./server.native

# fire up server, sending eoutput to serverout.txt
./server.native &> serverout.txt &

# run the client 10 times
for i in {1..10}; do
    ./mwu.native &> "clientout$i.txt"
    if [ $? -eq 0 ]; then
	echo "Client $i successful"
    else
	echo "Client $i failed"
	exit 1
    fi
done

# kill server (so it releases socket)
pkill -f ./server.native

# calculate and record regret to $OUTFILE
if [ -e $OUTFILE ]; then
    rm $OUTFILE
fi

for i in {1..10}; do
    ./calcregret.py "clientout$i.txt" $OUTFILE $EPSILON
done

# plot regret
./plotregret.py $OUTFILE




