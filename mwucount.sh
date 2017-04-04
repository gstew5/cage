#!/bin/sh

# Use coqwc to count the number of lines of proof and spec in
# files related to the implementation of MWU.

MWUFILES="weights.v weightsextract.v weightslang.v dyadic.v neps_exp_le.v compile.v dist.v numerics.v orderedtypes.v extrema.v bigops.v strings.v"

eval "coqwc "$MWUFILES""

# Check for admits in MWU-related files

eval "grep -e "admit" -e "Admitted" "$MWUFILES""
