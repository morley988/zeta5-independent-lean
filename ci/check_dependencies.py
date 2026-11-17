#!/usr/bin/env python3
"""Check the resolved Git commits and tracked source state, not moving tags."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
project = root / "zeta5"
manifest = json.loads((project / "lake-manifest.json").read_text())
records = []
for package in manifest["packages"]:
    path = project / manifest["packagesDir"] / package["name"]
    actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    if actual != package["rev"]:
        sys.exit(f"Dependency mismatch: {package['name']}: {actual} != {package['rev']}")
    for args in (["diff", "--quiet", "HEAD", "--"], ["diff", "--cached", "--quiet", "--"]):
        if subprocess.run(["git", "-C", str(path), *args]).returncode:
            sys.exit(f"Modified tracked dependency source: {package['name']}")
    records.append({"name": package["name"], "url": package["url"], "revision": actual})
if len(records) != 14:
    sys.exit(f"Expected 14 dependencies, got {len(records)}")
print(json.dumps({"status": "passed", "dependencies": records}, indent=2))
