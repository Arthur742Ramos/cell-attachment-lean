#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source ./env.sh
module="${1%.lean}"
mkdir -p ".lake/build/lib/lean/$(dirname "$module")"
"$CELL_LEAN_BIN" -o ".lake/build/lib/lean/$module.olean" -i ".lake/build/lib/lean/$module.ilean" "$module.lean"
