import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum

/-!
# The target is the ordinary Riemann zeta value

The declarations below directly adapt `realZeta`, `realZeta_cast`, and
`realZeta_eq_re` in `FourValueFinalContradiction.lean` from
morley988/four-odd-zeta at commit
fd23dd59e5d638c9684eb2d7776fb51e8b427b55 (MIT license).
Only the namespace and theorem comments change.  Unlike importing that final
module, these minimal imports bring in no supplied four-value certificates.
-/

noncomputable section
namespace Zeta5.Endpoint

/-- Real zeta at an integer argument, expressed by the ordinary series.
For `k > 1`, the `n=0` summand is zero under Lean's division convention. -/
def realZeta (k : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ k

theorem realZeta_cast (k : ℕ) (hk : 1 < k) :
    (realZeta k : ℂ) = riemannZeta (k : ℂ) := by
  rw [realZeta, Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hk]
  congr 1
  funext n
  simp

theorem realZeta_eq_re (k : ℕ) (hk : 1 < k) :
    realZeta k = (riemannZeta (k : ℂ)).re := by
  have h := congrArg Complex.re (realZeta_cast k hk)
  simpa using h

theorem irrational_realZeta_five_iff :
    Irrational (realZeta 5) ↔ Irrational (riemannZeta 5).re := by
  rw [realZeta_eq_re 5 (by norm_num)]
  norm_num

#print axioms realZeta_cast
#print axioms realZeta_eq_re
#print axioms irrational_realZeta_five_iff

end Zeta5.Endpoint
