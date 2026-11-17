"""Package the completed proof and its reproducibility evidence.

No build cache or toolchain is included. The final theorem and audit must have
already succeeded; this script packages their source and recorded output.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
TASK = ROOT.parents[1]
ARTIFACTS = TASK / "artifacts"
ARTIFACTS.mkdir(parents=True, exist_ok=True)

root_log = (ROOT / "evidence/final_root_build.log").read_text()
kernel_log = (ROOT / "evidence/final_kernel_audit.log").read_text()
trust_log = (ROOT / "evidence/final_trust_audit.log").read_text()
assert "Build completed successfully" in root_log
assert "Zeta5.irrational_zeta_five" in kernel_log
assert "[propext, Classical.choice, Quot.sound]" in kernel_log
assert "error:" not in kernel_log
assert "all 24 arithmetic block fits and upper bounds" in trust_log
closure_data = json.loads((ROOT / "evidence/final_constant_closure.json").read_text())
assert set(closure_data["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
assert "sorryAx" not in closure_data["constants"]

pending, modules = ["Zeta5"], set()
while pending:
    name = pending.pop()
    if name in modules:
        continue
    modules.add(name)
    source = (ROOT / (name.replace(".", "/") + ".lean")).read_text()
    pending.extend(re.findall(r"^import (Zeta5[\w.]*)", source, re.M))

payloads = {}
def add(path, name=None):
    path = Path(path)
    payloads["zeta5/" + (name or path.relative_to(ROOT).as_posix())] = path.read_bytes()

for name in ["Zeta5.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
             "README.md", "VERIFICATION_REPORT.txt"]:
    add(ROOT / name)
for path in sorted((ROOT / "Zeta5").rglob("*.lean")):
    add(path)
for path in sorted((ROOT / "scripts").glob("*.py")):
    add(path)

evidence = [
    "FinalAudit.lean", "CheckpointAudit.lean", "final_root_build.log",
    "verified_endpoint_build.log", "final_kernel_audit.log",
    "final_trust_audit.log", "final_constant_closure.json", "environment.json",
    "ARITHMETIC_SEMANTIC_AUDIT.txt", "NormalizerPrimeTailAxioms.lean",
    "normalizer_prime_tail_axioms.log", "extended_arithmetic_certificate.json",
    "analytic_grid_data.json", "arithmetic_cells.json", "certificate_run.txt",
    "extended_certificate_assembly.log", "analytic_grid_compile.log",
    "arithmetic_cells_compile.log", "local_arithmetic_axioms.lean",
    "local_arithmetic_axioms.log", "restriction_axioms.lean", "restriction_axioms.log",
]
for name in evidence:
    add(ROOT / "evidence" / name)

analytic = ROOT.parent / "analytic_notes"
for name in ["final_semantic_review.txt", "FinalEndpointSemanticAudit.lean",
             "final_endpoint_semantic_axioms.log", "EndpointSemanticAudit.lean",
             "endpoint_semantic_axioms.log", "ArithmeticRateAxioms.lean"]:
    add(analytic / name, "evidence/independent_analytic/" + name)

ledger = ROOT.parent / "reuse_ledger"
for name in ["REUSE_LEDGER.txt", "source_inventory.json", "direct_reuse_comparison.json"]:
    add(ledger / name, "reuse_ledger/" + name)
add(ROOT / "evidence/final_constant_closure.json", "reuse_ledger/final_constant_closure.json")
add(ROOT / "evidence/final_trust_audit.log", "reuse_ledger/final_trust_audit.log")

manuscript = TASK / "sources/zeta5_journal.tex"
if manuscript.exists():
    add(manuscript, "inputs/zeta5_journal.tex")

metadata = {
    "status": "unconditional theorem verified",
    "theorem": "Zeta5.irrational_zeta_five",
    "type": "Irrational (riemannZeta 5).re",
    "axioms": closure_data["axioms"],
    "transitive_constant_count": closure_data["constant_count"],
    "root_own_module_count": len(modules),
    "root_own_modules": sorted(modules),
    "numerical_obligations_deferred": 0,
    "packaged_utc": datetime.now(timezone.utc).isoformat(),
}
payloads["zeta5/VERIFICATION.json"] = (json.dumps(metadata, indent=2) + "\n").encode()
manifest = "".join(hashlib.sha256(data).hexdigest() + "  " + name + "\n"
                   for name, data in sorted(payloads.items()))
payloads["zeta5/MANIFEST.sha256"] = manifest.encode()

output = ARTIFACTS / "zeta5_lean_verified.zip"
with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for name, data in sorted(payloads.items()):
        z.writestr(name, data)

report = ARTIFACTS / "zeta5_lean_verification_report.txt"
reuse = ARTIFACTS / "zeta5_lean_reuse_ledger.txt"
shutil.copyfile(ROOT / "VERIFICATION_REPORT.txt", report)
shutil.copyfile(ledger / "REUSE_LEDGER.txt", reuse)

result = {
    "archive": str(output), "bytes": output.stat().st_size,
    "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
    "files": len(payloads), "root_own_modules": len(modules),
    "report": str(report), "reuse_ledger": str(reuse),
}
(ARTIFACTS / "zeta5_verified_package_manifest.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
