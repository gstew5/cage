# EPSILON=0.135
# ETA=0.105
# ETA_IDEAL=0.10481470739 # ideal value of eta
ETA=0.0625
ETA_IDEAL=0.06051479953
REGRET_OUTFILE=out
SOCIAL_OUTFILE=social
CLIENTS=5
ROUNDS=10
SIZE_A=3
LAMBDA=1.666
MU=0.333
OPT=0.203125
# OPT=0.1015625
CONFIDENCE=0.95
# settings above for routing1.v with num_iters = 100

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
	# fire up server, sending output to serverout.txt
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
for i in $(seq 1 $CLIENTS); do
    file="${REGRET_OUTFILE}${i}.txt"
    if [ -e $file ]; then
	rm $file
    fi
done

for i in $(seq 1 $ROUNDS); do
    for j in $(seq 1 $CLIENTS); do
	./calcregret.py "round${i}client${j}.txt" \
			"${REGRET_OUTFILE}${j}.txt" $ETA
    done
done

# Calculate and record average social cost at each timestep to $SOCIAL_OUTFILE
./calcsocial.py $CLIENTS $ROUNDS $REGRET_OUTFILE "${SOCIAL_OUTFILE}.txt"

# plot
./plotmachine.py "${SOCIAL_OUTFILE}.txt" $CLIENTS $SIZE_A $LAMBDA \
		 $MU $ETA $ETA_IDEAL $OPT
