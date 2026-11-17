#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
project_dir="$repo_root/zeta5"
output_dir="$repo_root/verification/latest"
mkdir -p "$output_dir"
rm -f "$output_dir/PASSED"
python3 "$repo_root/ci/verify_archive.py" | tee "$output_dir/archive-before.log"
cd "$project_dir"
lean --version | tee "$output_dir/lean-version.log"
python3 - "$output_dir/lean-version.log" <<'PY'
import sys
from pathlib import Path
version = Path(sys.argv[1]).read_text()
if "version 4.33.1," not in version or "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
    sys.exit("Wrong Lean version or compiler commit; refusing to change the pin")
PY
# Build the large generated certificate modules one at a time. An unrestricted
# first build can start the analytic grid and 24 arithmetic blocks concurrently
# and exceed the available memory. This changes scheduling only.
{
  lake build Zeta5.Certificate.AnalyticGrid
  for block in $(seq -w 0 23); do
    lake build "Zeta5.Certificate.ExtendedArithmetic.Block$block"
  done
} 2>&1 | tee "$output_dir/certificates-build.log"
lake build 2>&1 | tee "$output_dir/build.log"
python3 "$repo_root/ci/check_dependencies.py" | tee "$output_dir/dependencies.json"
lake env lean --trust=0 evidence/FinalAudit.lean 2>&1 | tee "$output_dir/final-audit.log"
lake env lean --trust=0 "$repo_root/ci/ReleaseAudit.lean" 2>&1 | tee "$output_dir/release-audit.log"

# The original traversal writes a tracked historical evidence file. Preserve
# those archived bytes and retain the new result separately, including on error.
closure_file="$project_dir/evidence/final_constant_closure.json"
closure_backup=$(mktemp)
cp "$closure_file" "$closure_backup"
restore_closure() {
  cp "$closure_backup" "$closure_file"
  rm -f "$closure_backup"
}
trap restore_closure EXIT
lake env lean Zeta5/Reuse/FinalTrustAudit.lean 2>&1 | tee "$output_dir/trust-audit.log"
cp "$closure_file" "$output_dir/final_constant_closure.json"
restore_closure
trap - EXIT
python3 - "$output_dir/final_constant_closure.json" <<'PY'
from pathlib import Path
import json, sys
d = json.loads(Path(sys.argv[1]).read_text())
assert d["theorem"] == "Zeta5.irrational_zeta_five"
assert len(d["axioms"]) == 3
assert set(d["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
assert d["constant_count"] == len(set(d["constants"])) == 81789
assert not {"sorryAx", "prelim_decay_2", "prelim_decay_3"} & set(d["constants"])
print("PASS: exact axioms and 81,789 transitive constants; forbidden declarations absent")
PY
python3 "$repo_root/ci/verify_archive.py" | tee "$output_dir/archive-after.log"
python3 "$repo_root/ci/check_dependencies.py" > "$output_dir/dependencies.json"
git -C "$repo_root" rev-parse HEAD > "$output_dir/commit.txt"
printf '%s\n' 'All required build, theorem, dependency, and axiom checks passed.' > "$output_dir/PASSED"
