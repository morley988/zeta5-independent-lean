# v1.0.0

Preserved companion sources for the independent factorial-window determinant
proof of the irrationality of ζ(5), with a reproducible Lean build and explicit
theorem/axiom audits.

The release workflow requires all checks to pass before creating this release:

- All 234 original archive files preserved; 233 manifest checksums validated.
- Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- All 14 dependency checkouts match the unchanged lockfile.
- `lake build` succeeds for the `Zeta5` root.
- `Zeta5.irrational_zeta_five` is a closed theorem of the fully qualified
  Mathlib type `Irrational (riemannZeta (5 : Complex)).re`.
- Exact transitive axioms: `propext`, `Classical.choice`, `Quot.sound`.
- 81,789 distinct transitive constants; required certificate and mathematical
  bridges present; `sorryAx`, `prelim_decay_2`, and `prelim_decay_3` absent.

The source ZIP and verification evidence are attached with SHA-256 checksums.
Historical logs under `zeta5/evidence/` retain their original bytes. The attached
verification archive contains the new release run's logs and closure manifest.
No proof sources or dependency versions have been modified for publication.

This is Lean verification and an axiom audit, not a separate independent-kernel
certificate. See the README for reproduction instructions, trust scope,
provenance, and licensing status.
