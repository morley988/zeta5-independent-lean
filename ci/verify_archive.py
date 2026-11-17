#!/usr/bin/env python3
"""Verify the original archive payload without rewriting its manifest."""
from pathlib import Path
import hashlib
import os
import sys

root = Path(__file__).resolve().parents[1]
manifest = root / "zeta5/MANIFEST.sha256"
expected_manifest = "6b714e280c179bcb9d72ced45cfcaae738a42677a470381b5e8e6c02f3c8edd2"
if hashlib.sha256(manifest.read_bytes()).hexdigest() != expected_manifest:
    sys.exit("Original MANIFEST.sha256 changed")
seen = set()
for line in manifest.read_text().splitlines():
    digest, name = line.split(maxsplit=1)
    path = root / name
    if not name.startswith("zeta5/") or ".." in Path(name).parts or name in seen:
        sys.exit(f"Invalid or duplicated manifest path: {name}")
    seen.add(name)
    if not path.is_file() or path.is_symlink():
        sys.exit(f"Missing or nonregular original file: {name}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        sys.exit(f"Original archive file changed: {name}")
if len(seen) != 233:
    sys.exit(f"Expected 233 original checksums; got {len(seen)}")
actual = set()
for directory, subdirs, files in os.walk(root / "zeta5"):
    subdirs[:] = [name for name in subdirs if name not in {".lake", "__pycache__"}]
    actual.update(str((Path(directory) / name).relative_to(root)) for name in files)
if actual != seen | {"zeta5/MANIFEST.sha256"}:
    sys.exit(f"Original directory file set changed: {actual ^ (seen | {'zeta5/MANIFEST.sha256'})}")
print("PASS: all 234 archive files preserved; 233 content checksums verified")
