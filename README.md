# A new proof of the irrationality of ζ(5), with Lean verification

[![Lean build and audit](https://github.com/morley988/zeta5-independent-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/morley988/zeta5-independent-lean/actions/workflows/lean.yml)

This repository preserves the companion source archive `zeta5_lean_verified.zip`
from the independent factorial-window determinant proof of the irrationality of
ζ(5). The public endpoint is:

```lean
Zeta5.irrational_zeta_five : Irrational (riemannZeta 5).re
```

The required target, with Mathlib names fully qualified, is:

```lean
_root_.Irrational
  (_root_.Complex.re (_root_.riemannZeta (5 : _root_.Complex)))
```

The release audit requires a closed theorem declaration with this type and the
exact transitive axiom set `{propext, Classical.choice, Quot.sound}`. It rejects
additional hypotheses or axioms. The original traversal also requires the
analytic grid, all 24 arithmetic block proofs, the analytic-rate theorem,
restriction-determinant theorem, rational product formula, and prime number
theorem to occur in the dependency closure. It rejects `sorryAx`,
`prelim_decay_2`, and `prelim_decay_3`.

## Journal manuscript

Morley Davidson’s current manuscript is available as a [typeset PDF](manuscript/zeta5_journal_publication.pdf).
Use the [LaTeX source](manuscript/zeta5_journal_publication.tex) for future manuscript edits.

The [archived manuscript](zeta5/inputs/zeta5_journal.tex) preserves the exact
source distributed with the [verified v1.0.0 release](https://github.com/morley988/zeta5-independent-lean/releases/tag/v1.0.0).

## Preservation and provenance

All **234 files** extracted from the original archive remain byte-for-byte
unchanged under [`zeta5/`](zeta5/), including its original README, sources,
certificate data, generators, manuscript, dependency lockfile, and audit logs.
The original manifest covers 233 files; it does not hash itself. New repository
documentation and automation live outside that directory.

Original ZIP SHA-256:

```text
33bd0255937c716bf969a1b5933bfaca05e8c9a9a35522ac2ad7b1a0be31242e
```

Original manifest SHA-256:

```text
6b714e280c179bcb9d72ced45cfcaae738a42677a470381b5e8e6c02f3c8edd2
```

The source archive was packaged on 13 November 2026. Its historical claims and
logs are preserved as provenance, rather than being presented as a fresh CI
result. See the exact commit's [Actions run](https://github.com/morley988/zeta5-independent-lean/actions)
and its `lean-verification-<commit>` artifact for the new build evidence.
The `v1.0.0` release is created only after every required check succeeds.

## Pinned environment

- Lean: **4.33.1**, compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- PrimeNumberTheoremAnd: `650d31264be65f4cd6e70c45d8b25d86d482a761`.
- Four-value provenance reference:
  [`morley988/four-odd-zeta@fd23dd59e5d638c9684eb2d7776fb51e8b427b55`](https://github.com/morley988/four-odd-zeta/tree/fd23dd59e5d638c9684eb2d7776fb51e8b427b55).
  Selected general lemmas were copied into the archive; this is not an extra
  runtime dependency, and its earlier numerical admissions are not imported.

The complete 14-package resolution is in
[`zeta5/lake-manifest.json`](zeta5/lake-manifest.json). Resolved commit hashes,
not moving input tags such as `main`, determine the reproducible checkouts.
CI checks each dependency's actual `HEAD` and rejects tracked source edits.
Do **not** run `lake update` or substitute newer dependency versions when
reproducing this release. The archived Lake package version remains `0.1.0`;
the repository release version is `v1.0.0`.

## Reproduce from a clean checkout

Use Linux with Git, Bash, Python 3, a C/C++ build toolchain, `curl`, and
[Elan](https://github.com/leanprover/elan). The CI runner is `ubuntu-24.04`.
Allow several gigabytes of disk space for Lean, dependencies, and Mathlib's
cache. A fresh run needs network access to GitHub and the upstream cache hosts.

```bash
git clone https://github.com/morley988/zeta5-independent-lean.git
cd zeta5-independent-lean
# For the published release, after it exists:
# git checkout --detach v1.0.0
python3 ci/verify_archive.py
elan toolchain install leanprover/lean4:v4.33.1
cd zeta5
lake exe cache get
cd ..
bash ci/verify.sh
```

`ci/verify.sh` runs the following checks with error propagation enabled:

1. Validate all original archive files and the original manifest.
2. Check the Lean version and full compiler commit.
3. Build the large generated certificate modules sequentially, then run
   `lake build` against the archived project root `Zeta5`.
4. Check all 14 dependency revisions and tracked source trees.
5. Run `lake env lean --trust=0 evidence/FinalAudit.lean`.
6. Run the additional [`ci/ReleaseAudit.lean`](ci/ReleaseAudit.lean), checking
   the declaration kind, exact Mathlib target, and exact axiom set.
7. Run the original `Zeta5/Reuse/FinalTrustAudit.lean`; check its new manifest
   for exactly 81,789 distinct transitive constants and the expected axioms.
8. Recheck source integrity and dependency pins after the audits.

Fresh logs and the newly generated closure go to `verification/latest/`.
The original audit writes into `zeta5/evidence/`; the wrapper saves and restores
the historical file so running it cannot silently replace archived evidence.
Only a completely successful run writes `verification/latest/PASSED`.

The initial publication replay of an unrestricted `lake build` encountered a
process kill (exit 137) while the analytic grid and arithmetic blocks were
compiling concurrently on a machine with approximately 10 GiB RAM. The wrapper
therefore schedules the analytic grid and 24 arithmetic blocks one at a time
before the normal root build. This is a build-resource adjustment only; no
proof source, certificate, compiler option, or dependency pin is changed.

To run the original commands manually:

```bash
cd zeta5
lake build
lake env lean --trust=0 evidence/FinalAudit.lean
lake env lean Zeta5/Reuse/FinalTrustAudit.lean
```

The last manual command overwrites `evidence/final_constant_closure.json`.
Use the wrapper when preserving the archive exactly matters.

## What is built and checked

The default `Zeta5` root includes the closed endpoint and its mathematical
dependencies. The archived report records 178 project modules in that root's
import closure. Extra exploratory and audit files are retained; the default
target does not claim to build every unused experiment as a standalone module.
The final-trust and release audits are run explicitly.

Mathlib's official compiled cache is used for dependencies. Project proof
modules are compiled from the preserved source in a fresh CI checkout.
This is a Lean build and declaration/axiom audit, using Lean's own trusted
implementation. It is **not** a claim of verification by an independent kernel
such as Nanoda, or of a separate source-to-kernel comparator run. The archived
`--trust=0` invocation is reproduced without claiming a separate proof-checker
certificate.

The upstream PNT source contains two unrelated admitted Fourier lemmas. Their
presence in that source does not by itself put them in the theorem's proof;
the transitive audit explicitly checks their absence. The archive states that
no Fauzan result is used. Dependency provenance is available in the source and
the fresh closure manifest for inspection.

## Mathematical organization

| Location | Role |
| --- | --- |
| [`Zeta5/Endpoint/Verified.lean`](zeta5/Zeta5/Endpoint/Verified.lean) | Closed irrationality endpoint |
| [`Zeta5/Construction/`](zeta5/Zeta5/Construction/) | Factorial-window polynomial pencil and determinant |
| [`Zeta5/Analysis/`](zeta5/Zeta5/Analysis/) | Positive measure, Stieltjes identity, determinant decay |
| [`Zeta5/Arithmetic/PrimeAssembly.lean`](zeta5/Zeta5/Arithmetic/PrimeAssembly.lean) | Global arithmetic bound for the actual normalizer |
| [`Zeta5/Certificate/`](zeta5/Zeta5/Certificate/) | Generated exact Lean certificates and their soundness proofs |
| [`Zeta5/Reuse/`](zeta5/Zeta5/Reuse/) | General lemmas reused or generalized from the four-value project |
| [`reuse_ledger/REUSE_LEDGER.txt`](zeta5/reuse_ledger/REUSE_LEDGER.txt) | Detailed reuse and normalization ledger |
| [`VERIFICATION_REPORT.txt`](zeta5/VERIFICATION_REPORT.txt) | Original mathematical and verification report |
| [`inputs/zeta5_journal.tex`](zeta5/inputs/zeta5_journal.tex) | Archived journal-style manuscript source |

The archived report describes 2,048 analytic checks and 3,060 arithmetic cells
in 24 blocks. The sufficient final arithmetic rate is `5.412`; the exact
certificate bound is `202930490737 / 37500000000`, while the analytic rate is
proved greater than `5.4133705070`. The generated Lean certificates are present
in the source. Python regeneration is not required to build the proof.

## CI and release policy

[`lean.yml`](.github/workflows/lean.yml) builds on pushes, pull requests, and
manual dispatch. It installs the pinned compiler, obtains dependency caches,
runs all checks, and uploads new logs even when verification fails. It never
updates the proof sources or dependency pins to make a build pass.

The first successful default-branch run can publish `v1.0.0` at its exact
verified commit. A pull-request run cannot publish. The release step requires
the success marker and checks the logged commit; it refuses to replace an
existing tag or release. Subsequent pushes leave the existing release intact.
The release includes a source archive and the fresh verification evidence.

If fetching, compilation, type checking, dependency validation, or an axiom
audit fails, preserve the failure logs and report the failure. Do not infer a
proof failure from an unavailable download, and do not infer verification
success from historical logs. No tag should be created on a failed check.

## Licensing and citation

The companion archive did not supply a project-wide license. None is assigned
here without the author's choice; existing source notices and dependency
licenses remain in force. Public availability alone does not grant a new
blanket license.

For citation, use the repository's release page and exact commit once
`v1.0.0` is published. The original project attribution is “Zeta Irrationality
Project”; the archived report is dated 13 November 2026. Do not describe a
pending or failed workflow as a completed verification.
