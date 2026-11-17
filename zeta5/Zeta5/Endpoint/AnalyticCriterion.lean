import Zeta5.Analysis.DeterminantRate

/-! # The remaining arithmetic endpoint after the analytic rate is proved -/

noncomputable section
namespace Zeta5.Endpoint
open Filter
open scoped Topology

/-- The actual analytic determinant estimate and positivity are discharged.
Only the arithmetic normalizer rate and a strict scalar gap remain. -/
theorem irrational_zeta5_of_arithmetic_rate (A : ℝ)
    (hgap : A < Zeta5.Certificate.analyticIntegral)
    (errorArithmetic : ℕ → ℝ)
    (herrorArithmetic : Tendsto (fun n => errorArithmetic n / windowScale n) atTop (𝓝 0))
    (harithmetic : ∀ᶠ n in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ A * windowScale n + errorArithmetic n) :
    Irrational (riemannZeta 5).re := by
  obtain ⟨E, hE, hbound⟩ := Zeta5.Analysis.exists_analytic_rate_error
  exact irrational_zeta5_of_two_log_rate_bounds A Zeta5.Certificate.analyticIntegral hgap
    errorArithmetic E herrorArithmetic hE harithmetic hbound

/-- The exact 2,048-panel certificate supplies a rational target for the
remaining normalizer rate. -/
theorem irrational_zeta5_of_arithmetic_rate_lt_certified (A : ℝ)
    (hgap : A ≤ 54133705070 / 10 ^ 10)
    (errorArithmetic : ℕ → ℝ)
    (herrorArithmetic : Tendsto (fun n => errorArithmetic n / windowScale n) atTop (𝓝 0))
    (harithmetic : ∀ᶠ n in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ A * windowScale n + errorArithmetic n) :
    Irrational (riemannZeta 5).re :=
  irrational_zeta5_of_arithmetic_rate A
    (hgap.trans_lt Zeta5.Certificate.analyticIntegral_gt_displayed)
    errorArithmetic herrorArithmetic harithmetic

end Zeta5.Endpoint
