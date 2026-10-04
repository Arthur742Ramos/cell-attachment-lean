_CELL_PROJECT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export CELL_LEAN_BIN="/workspace/shared/economics-next-proof/.toolchain/elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean"
export PATH="$(dirname "$CELL_LEAN_BIN"):$PATH"
export LEAN_PATH="$_CELL_PROJECT/.lake/build/lib/lean"
for _CELL_PACKAGE in /workspace/shared/economics-next-proof/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$_CELL_PACKAGE/.lake/build/lib/lean"
done
unset _CELL_PACKAGE _CELL_PROJECT
