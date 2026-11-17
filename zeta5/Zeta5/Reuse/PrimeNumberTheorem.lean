import PrimeNumberTheoremAnd.Consequences
import Zeta5.Reuse.PrimeAffine

/-!
# The proved prime number theorem and signed affine prime sums

`theta_ratio_limit` is reused directly from the four-value project's
`FourValuePrimeAsymptotic.lean`. The upstream package is pinned to the same
commit. Although its source contains unrelated admitted lemmas, the axiom
audit below verifies that `chebyshev_asymptotic` and every theorem here use
only Lean's standard foundational axioms.
-/

noncomputable section
namespace Zeta5.Reuse.PrimeNumberTheorem
open Filter Asymptotics PrimeAffine
open scoped Topology Chebyshev

theorem theta_ratio_limit : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp chebyshev_asymptotic
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact ne_of_gt hx

theorem primeAffineSum_limit (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (primeAffineSum a b c d) atTop
      (𝓝 (c * (b - a) + d * (b ^ 2 - a ^ 2) / 2)) :=
  primeAffineSum_limit_of_theta theta_ratio_limit a b c d ha hab

theorem primeAffineSum_integral_limit (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (primeAffineSum a b c d) atTop (𝓝 (∫ t in a..b, c + d * t)) :=
  primeAffineSum_integral_limit_of_theta theta_ratio_limit a b c d ha hab

theorem finite_primeAffineSum_limit {ι : Type*} [Fintype ι] (a b c d : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun n : ℕ => ∑ i : ι, primeAffineSum (a i) (b i) (c i) (d i) n) atTop
      (𝓝 (∑ i : ι, (c i * (b i - a i) + d i * (b i ^ 2 - a i ^ 2) / 2))) :=
  finite_primeAffineSum_limit_of_theta theta_ratio_limit a b c d ha hab

#print axioms chebyshev_asymptotic
#print axioms theta_ratio_limit
#print axioms primeAffineSum_limit
#print axioms primeAffineSum_integral_limit
#print axioms finite_primeAffineSum_limit

end Zeta5.Reuse.PrimeNumberTheorem
