#!/bin/sh
set -eu
BASE_LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="/tmp:${BASE_LEAN_PATH}"
mkdir -p /tmp/Generated
lean -o /tmp/Generated/CountVotesForCandidate.olean Generated/CountVotesForCandidate.lean
lean -o /tmp/Generated/ElectLeaderByMaxId.olean Generated/ElectLeaderByMaxId.lean
lean -o /tmp/Generated/FilterAliveNodes.olean Generated/FilterAliveNodes.lean
lean -o /tmp/Generated/HasMajority.olean Generated/HasMajority.lean
lean -o /tmp/Generated/NextNodeInRing.olean Generated/NextNodeInRing.lean
lean -o /tmp/Generated/ShouldAcceptTerm.olean Generated/ShouldAcceptTerm.lean
lean Generated/All.lean
