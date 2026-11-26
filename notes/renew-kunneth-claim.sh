#!/bin/bash
# Renew the Tau Ceti task claim for the general-ring Künneth spectral sequence (COORDINATION.md §3).
set -euo pipefail
cd /tmp/TauCeti-kunneth2
key=author/AlgebraicTopology/general-ring-kunneth-spectral-sequence
ref=refs/tauceti-claims/$key
git fetch -q origin "+$ref:$ref"
old=$(git rev-parse "$ref")
prev=$(git log -1 --format=%B "$ref")
acq=$(printf '%s' "$prev" | python3 -c 'import json,sys;print(json.load(sys.stdin)["acquired_at"])')
now=$(date +%s); exp=$((now + 72*3600))
main=$(git rev-parse origin/main)
msg=$(printf '{"schema":"tauceti-claim/v1","owner":"kim-em-claude-45d6b5d6-eac4-4e91-addb-8d1daecbc7d4","host":"persica","pid":%d,"acquired_at":%d,"expires_at":%d,"resource":"%s","observed_branch_oid":"%s"}' $$ "$acq" "$exp" "$key" "$main")
tree=$(git hash-object -t tree /dev/null)
new=$(git commit-tree "$tree" -m "$msg")
git push -q --force-with-lease="$ref:$old" origin "$new:$ref"
echo "renewed until $(date -r $exp)"
