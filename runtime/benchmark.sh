#!/bin/bash

./server.native &> serverout.txt &

for i in {1..100}; do
    ./mwu.native &> "clientout$i.txt" &
done

for i in {1..100}; do
    ./calcregret.py "clientout$i.txt" 0.25 >> out.txt
done

./plotregret.py out.txt




