import Zeta5.Endpoint.ConcreteCriterion
import Zeta5.Analysis.PhysicalMeasureStieltjes

/-! # The endpoint after the physical positivity hypothesis has been proved -/

noncomputable section
namespace Zeta5.Endpoint
open Filter
open scoped Topology

theorem windowValue_pos (n : ℕ) : 0 < windowValue n :=
  Zeta5.Analysis.PhysicalMeasure.windowDeterminant_realZetaFive_pos n

/-- Only the normalized decay remains to be supplied: positivity follows
from the actual physical measure and the proved Stieltjes identity. -/
theorem irrational_zeta5_of_physical_normalized_decay
    (hdecay : ∀ b : ℕ, 0 < b →
      Tendsto (fun n => (b : ℝ) ^ (24 * n) *
        ((windowNormalizer n : ℝ) * windowValue n)) atTop (𝓝 0)) :
    Irrational (riemannZeta 5).re :=
  irrational_zeta5_of_normalized_decay (Eventually.of_forall windowValue_pos) hdecay

/-- The remaining endpoint obligations are the two quantitative asymptotic
bounds and a strict gap between their rates. -/
theorem irrational_zeta5_of_two_log_rate_bounds (A B : ℝ) (hgap : A < B)
    (errorArithmetic errorAnalytic : ℕ → ℝ)
    (herrorArithmetic : Tendsto (fun n => errorArithmetic n / windowScale n) atTop (𝓝 0))
    (herrorAnalytic : Tendsto (fun n => errorAnalytic n / windowScale n) atTop (𝓝 0))
    (harithmetic : ∀ᶠ n in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ A * windowScale n + errorArithmetic n)
    (hanalytic : ∀ᶠ n in atTop,
      Real.log (windowValue n) ≤ -B * windowScale n + errorAnalytic n) :
    Irrational (riemannZeta 5).re :=
  irrational_zeta5_of_log_rate_bounds A B hgap errorArithmetic errorAnalytic
    herrorArithmetic herrorAnalytic (Eventually.of_forall windowValue_pos) harithmetic hanalytic

end Zeta5.Endpoint
