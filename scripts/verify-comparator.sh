#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarRegistry/PalomarTemplate's verify-comparator.sh
# (Apache-2.0, reference commit in docs/submission.md). The committed config
# always targets the paper's main theorem. An explicit milestone selection
# replaces only theorem_names in the temporary *local* config.
cd "$(dirname "$0")/.."
case "${1:-full}" in
  full|milestone) mode="${1:-full}" ;;
  *) echo "usage: $0 [full|milestone]" >&2; exit 2 ;;
esac
for cmd in lake lean bwrap python3; do
  command -v "$cmd" > /dev/null || { echo "Missing command: $cmd" >&2; exit 2; }
done
prefix=$(lean --print-prefix)
for checker in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$checker" || { echo "Missing toolchain executable: $checker" >&2; exit 2; }
done
tmp_config=$(mktemp)
trap 'rm -f "$tmp_config"' EXIT
python3 - "$mode" "$prefix" "$tmp_config" <<'PY'
import json
from pathlib import Path
import sys

mode, prefix, out = sys.argv[1:]
config = json.loads(Path("comparator.json").read_text())
required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
if set(config) != required:
    sys.exit("Unexpected fields in comparator.json")
if (config["challenge_module"], config["solution_module"], config["theorem_names"]) != (
    "Challenge", "Solution", ["MT.powerlossMT"]
):
    sys.exit("The committed config must select the full MT.powerlossMT target")
if set(config["permitted_axioms"]) - {"propext", "Classical.choice", "Quot.sound"}:
    sys.exit("Axiom outside the project allowlist")
if mode == "milestone":
    config["theorem_names"] = [
        "MT.localConstant_mono",
        "MT.powerLoss_of_transfer_and_amplification",
        "MT.Seed.exists_bounded_seed",
    ]
config["external_kernels"] = {
    "nanoda": [str(Path(prefix) / "bin" / "nanoda_bin")],
    "con-ron": [str(Path(prefix) / "bin" / "con-ron")]
}
print(f"Compared declarations ({mode}): " + ", ".join(config["theorem_names"]), flush=True)
Path(out).write_text(json.dumps(config) + "\n")
PY
lake --version
lean --version
lake comparator --config "$tmp_config"
