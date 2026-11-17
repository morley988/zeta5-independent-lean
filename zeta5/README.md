# Zeta(5) Lean verification

The completed theorem is:

```lean
Zeta5.irrational_zeta_five : Irrational (riemannZeta 5).re
```

It has no parameters or remaining hypotheses. `riemannZeta` and `Irrational`
are Mathlib's definitions. The final transitive axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.

## Reproduce

Install the pinned Lean toolchain with Elan, then run from this directory:

```sh
elan toolchain install leanprover/lean4:v4.33.1
lake exe cache get
lake build
lake env lean --trust=0 evidence/FinalAudit.lean
lake env lean Zeta5/Reuse/FinalTrustAudit.lean
```

The lockfile records all dependency commits. The build can fetch the pinned
dependencies and use Mathlib's published cache; caches and toolchains are not
included in the source archive. The final command writes a machine-readable
transitive constant manifest to `evidence/final_constant_closure.json`.

## Main files

- `Zeta5/Endpoint/Verified.lean`: closed irrationality theorem.
- `Zeta5/Arithmetic/PrimeAssembly.lean`: actual global arithmetic bound.
- `Zeta5/Analysis/DeterminantRate.lean`: actual analytic decay rate.
- `Zeta5/Analysis/PhysicalMeasureStieltjes.lean`: actual Stieltjes identity and positivity.
- `Zeta5/Certificate/AllPrimePieces.lean`: all finite arithmetic profile pieces.
- `Zeta5/Certificate/AnalyticGrid.lean`: checked analytic grid.
- `Zeta5/Certificate/ExtendedArithmetic/`: 24 checked blocks, 3,060 cells.
- `evidence/FinalAudit.lean`: explicit Mathlib target and axiom checks.
- `VERIFICATION_REPORT.txt`: scope, numerical rates, checks, and formalization choices.
- `reuse_ledger/REUSE_LEDGER.txt`: direct, generalized, and potential four-value overlap.

## Quantitative comparison

The formal proof uses the eventual arithmetic rate `5.412`. Its finite
certificate and uniform tail give the exact upper constant
`202930490737 / 37500000000 = 5.411479752986666...`.
The actual analytic integral is proved greater than `5.4133705070`.
All numerical certificates required by the final theorem are kernel checked.
There are no deferred numerical obligations.

The formalization uses a fixed cutoff `1/512` for the arithmetic tail and
absorbs the harmless `r!` Gram determinant bound into a proved `o(N^2)` error.
It therefore does not need the manuscript's tighter arithmetic constant or
the infinite-period tail calculation.

## Trust and provenance

Lean: `v4.33.1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
PrimeNumberTheoremAnd: `650d31264be65f4cd6e70c45d8b25d86d482a761`.
Four-value reference: `fd23dd59e5d638c9684eb2d7776fb51e8b427b55` at
<https://github.com/morley988/four-odd-zeta>.

Only checked general lemmas are reused from the four-value project. Its old
numerical admissions are not imported into the final theorem. Two unrelated
admitted Fourier lemmas exist in the pinned PNT source; the final dependency
audit explicitly verifies that both, and `sorryAx`, are absent from the
theorem's dependency closure. The proof does not depend on Fauzan results.
