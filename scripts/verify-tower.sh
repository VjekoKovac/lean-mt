#!/usr/bin/env bash
# Elaborate MT's dyadic refinement and optionally replay its proof closure.
set -eu
export LEAN_ABORT_ON_PANIC=1
cd "$(dirname "$0")/.."
mkdir -p .lake
out=$(mktemp -d "$PWD/.lake/mt-tower-check.XXXXXXXX")
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/MT"
set -x
lake env lean -o "$out/MT/Tower.olean" MT/Tower.lean
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean checks/TowerAxioms.lean' _ "$out"
case "${1:-}" in
  "") exit 0 ;;
  --replay) ;;
  *) echo "Usage: $0 [--replay]" >&2; exit 2 ;;
esac
# Primitive declarations required by Lean's export checker (Lean v4.35.0, Lake.CLI.Check).
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec leanexport MT.Tower -- "$@"' _ "$out" \
  Quot Quot.mk Quot.lift Quot.ind MT.Tower.dyadic_totally_real_fields \
  propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod \
  Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat \
  List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam \
  > "$out/tower.ndjson"
leanchecker --from-export "$out/tower.ndjson"
python3 - "$out" <<'PY'
import json
import pathlib
import sys
out = pathlib.Path(sys.argv[1])
(out / "nanoda.json").write_text(json.dumps({
    "use_stdin": False,
    "export_file_path": str(out / "tower.ndjson"),
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": True,
    "num_threads": 2,
    "nat_extension": True,
    "string_extension": True,
}))
PY
nanoda_bin "$out/nanoda.json"
