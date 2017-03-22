

EPSILON=0.03125
OUTFILE=out.txt
CLIENTS=10
ROUNDS=20
CONFIDENCE=0.99
# settings above for routing1.v

# kill ./server.native if it's currently running
pkill -f ./server.native
# fire up server, sending eoutput to serverout.txt
./server.native &> serverout.txt &

# $ROUNDS rounds
PIDS=()
for i in $(seq 1 $ROUNDS); do
    # spool up clients, making sure that they run concurrently
    for j in $(seq 1 $CLIENTS); do
	echo "Spooling up client $j"
	./mwu.native &> "clientout$i$j.txt" & PIDS[$j]=$!
    done
    # wait for clients
    for j in $(seq 1 $CLIENTS); do
	wait ${PIDS[$j]}
    done 
    if [ $? -eq 0 ]; then
	echo "Round $i successful"
	# kill server (so it releases socket)
	pkill -f ./server.native
	# fire up server, sending eoutput to serverout.txt
	./server.native &> serverout.txt &
    else
	echo "Round $i failed"
	exit 1
    fi
done

# Calculate and record regret to $OUTFILE.
# Run ./calcregret.py once per round, specialized in each
# round to the last client (j=$CLIENTS).
if [ -e $OUTFILE ]; then
    rm $OUTFILE
fi

for i in $(seq 1 $ROUNDS); do
    ./calcregret.py "clientout$i$CLIENTS.txt" $OUTFILE $EPSILON
done

# # plot regret
./plotregret.py $OUTFILE $ROUNDS $CONFIDENCE




