"""Create a reproducible source checkpoint without toolchains or build caches."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
TASK = ROOT.parents[1]
OUTPUT = TASK / "artifacts" / "zeta5_lean_verification_checkpoint.zip"
OUTPUT.parent.mkdir(parents=True, exist_ok=True)

def closure():
    pending = ["Zeta5"]
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        path = ROOT / (name.replace(".", "/") + ".lean")
        text = path.read_text()
        pending.extend(re.findall(r"^import (Zeta5[\w.]*)", text, re.M))
    return sorted(seen)

now = datetime.now(timezone.utc).isoformat()
payloads = {}
for path in ROOT.rglob("*"):
    rel = path.relative_to(ROOT)
    if not path.is_file() or any(part.startswith(".") or part == "__pycache__" for part in rel.parts):
        continue
    if rel.parts[0] == "evidence" and not any(word in path.name for word in
            ("checkpoint", "certificate", "analytic_grid", "arithmetic_cells", "Audit")):
        continue
    if path.suffix in {".olean", ".ilean", ".o", ".c", ".zip", ".pyc"}:
        continue
    payloads["zeta5/" + rel.as_posix()] = path.read_bytes()

for path in (ROOT.parent / "reuse_ledger").glob("*"):
    if path.is_file():
        payloads["zeta5/reuse_ledger/" + path.name] = path.read_bytes()

manuscript = TASK / "sources" / "zeta5_journal.tex"
if manuscript.exists():
    payloads["zeta5/inputs/zeta5_journal.tex"] = manuscript.read_bytes()

checked = closure()
status = f"""ZETA(5) LEAN VERIFICATION CHECKPOINT
Snapshot time (UTC): {now}

STATUS: THE INDEPENDENT IRRATIONALITY PROOF IS NOT FULLY VERIFIED.
The root Zeta5.lean imports completed components. The latest recorded root
build and selected transitive axiom audits are in evidence/. Any additional
source files not imported by the root may still be in progress.

Pinned Lean: v4.33.1
Pinned Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474
Pinned PrimeNumberTheoremAnd: 650d31264be65f4cd6e70c45d8b25d86d482a761
Four-value reference commit: fd23dd59e5d638c9684eb2d7776fb51e8b427b55
Reference repository: https://github.com/morley988/four-odd-zeta

The conditional endpoint refers to the actual rational determinant and to
Mathlib's Riemann zeta value. The physical Stieltjes identity and strict
positivity and full analytic asymptotic estimate are now proved. The global
arithmetic normalizer estimate remains an explicit hypothesis. Actual local
small-prime, restriction-rank, upper-band, and large-prime bounds are proved.
The finite 2048-node calculation and its actual integral interpretation are
kernel checked with ordinary decide, as are all 3060 cells in the extended
arithmetic certificate. No numerical admission or native_decide is needed.
The relevant prime number theorem also passes a transitive axiom
audit; two unrelated admissions elsewhere in its upstream source are not
dependencies of the theorem used here.

Reproduce after installing the pinned Lean toolchain:
  lake exe cache get
  lake build
  lake env lean evidence/CheckpointAudit.lean
  python3 scripts/certificate_explicit.py

Root import closure ({len(checked)} own modules):
""" + "\n".join(checked) + "\n"
payloads["zeta5/CHECKPOINT.txt"] = status.encode()
manifest = "".join(hashlib.sha256(data).hexdigest() + "  " + name + "\n"
                   for name, data in sorted(payloads.items()))
payloads["zeta5/MANIFEST.sha256"] = manifest.encode()
with zipfile.ZipFile(OUTPUT, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for name, data in sorted(payloads.items()):
        archive.writestr(name, data)
print(json.dumps({"path": str(OUTPUT), "bytes": OUTPUT.stat().st_size,
                  "root_module_count": len(checked), "files": len(payloads)}))
