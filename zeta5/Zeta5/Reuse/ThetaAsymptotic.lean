import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Finite signed prime-interval asymptotics as an explicit interface

Adapted from `FourValuePrimeAsymptotic.lean` in morley988/four-odd-zeta,
commit fd23dd59e5d638c9684eb2d7776fb51e8b427b55 (MIT license).

The only generalization replaces Chebyshev theta by an arbitrary function
`theta` satisfying the explicitly supplied ratio limit.  No prime number
theorem is assumed as an axiom or silently imported here.  Applying these
lemmas to Chebyshev theta requires its actual proved asymptotic.

These are finite step-weight results. Extension to piecewise affine profiles,
exceptional boundary primes and the cutoff limit Q -> infinity remains a
separate obligation of the zeta(5) application.
-/

noncomputable section
namespace Zeta5.Reuse.ThetaAsymptotic
open Filter
open scoped Topology BigOperators

variable (theta : ℝ → ℝ)
variable (htheta : Tendsto (fun x : ℝ => theta x / x) atTop (𝓝 1))
include htheta

theorem scaled_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => theta (c * x) / x) atTop (𝓝 c) := by
  have ht := htheta.comp ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)
  have ht' := ht.mul_const c
  have heq : (fun x : ℝ => (theta (c * x) / (c * x)) * c) =
      (fun x : ℝ => theta (c * x) / x) := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [ne_of_gt hc]
  simpa only [Function.comp_def, id_eq, one_mul, heq] using ht'

theorem interval_limit (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (theta (b * x) - theta (a * x)) / x)
      atTop (𝓝 (b - a)) := by
  simpa only [sub_div] using
    (scaled_limit theta htheta b hb).sub (scaled_limit theta htheta a ha)

/-- The weights may have either sign. There are finitely many intervals,
and each endpoint is fixed and strictly positive. -/
theorem weighted_intervals {ι : Type*} [Fintype ι] (w a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Tendsto (fun x : ℝ => ∑ i, w i * ((theta (b i * x) - theta (a i * x)) / x))
      atTop (𝓝 (∑ i, w i * (b i - a i))) := by
  apply tendsto_finsetSum
  intro i _
  exact (interval_limit theta htheta (a i) (b i) (ha i) (hb i)).const_mul (w i)

theorem weighted_intervals_nat {ι : Type*} [Fintype ι] (w a b : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Tendsto (fun n : ℕ => ∑ i,
      w i * ((theta (b i * n) - theta (a i * n)) / (n : ℝ)))
      atTop (𝓝 (∑ i, w i * (b i - a i))) :=
  (weighted_intervals theta htheta w a b ha hb).comp tendsto_natCast_atTop_atTop

#print axioms scaled_limit
#print axioms weighted_intervals
#print axioms weighted_intervals_nat

end Zeta5.Reuse.ThetaAsymptotic
