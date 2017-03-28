

EPSILON=0.125
OUTFILE=out.txt
CLIENTS=5
ROUNDS=50
CONFIDENCE=0.95
# settings above for routing1.v

# $ROUNDS rounds
PIDS=()
for i in $(seq 1 $ROUNDS); do
    # fire up server, sending eoutput to serverout.txt
    ./server.native &> serverout.txt &
    # spool up clients, making sure that they run concurrently
    for j in $(seq 1 $CLIENTS); do
	echo "Spooling up client $j"
	./mwu.native &> "round${i}client${j}.txt" & PIDS[$j]=$!
    done
    # wait for clients
    for j in $(seq 1 $CLIENTS); do
	wait ${PIDS[$j]}
    done 
    if [ $? -eq 0 ]; then
	echo "Round $i successful"
	# fire up server, sending eoutput to serverout.txt
	./server.native &> serverout.txt &
    else
	echo "Round $i failed"
	exit 1
    fi
    # kill server (so it releases socket)
    pkill -f ./server.native
    # kill all clients
    pkill -f ./mwu.native
done

# Calculate and record regret to $OUTFILE.
# Run ./calcregret.py once per round, specialized in each
# round to the last client (j=$CLIENTS).
if [ -e $OUTFILE ]; then
    rm $OUTFILE
fi

for i in $(seq 1 $ROUNDS); do
    ./calcregret.py "round${i}client${CLIENTS}.txt" $OUTFILE $EPSILON
done

# # plot regret
./plotregret.py $OUTFILE $ROUNDS $CONFIDENCE




