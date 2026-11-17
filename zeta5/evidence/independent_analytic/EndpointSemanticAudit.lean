import Zeta5.Analysis.ArithmeticRate

/-! This audit fixes fully qualified target constants and restates the exact
application interfaces without adding analytic hypotheses. -/
open Filter
open scoped Topology

example : Zeta5.Endpoint.realZeta 5 = (_root_.riemannZeta (5 : ℂ)).re := by
  simpa using Zeta5.Endpoint.realZeta_eq_re 5 (by norm_num)

example (n : ℕ) : Zeta5.Endpoint.windowScale n = ((20*n : ℕ) : ℝ)^2 := by
  simp only [Zeta5.Endpoint.windowScale, Nat.cast_mul, Nat.cast_ofNat]

example (n : ℕ) : (Zeta5.Endpoint.windowIntegerPolynomial n).natDegree ≤ 24*n :=
  Zeta5.Endpoint.windowIntegerPolynomial_degree n

example (n : ℕ) : 0 < Zeta5.Endpoint.windowValue n :=
  Zeta5.Endpoint.windowValue_pos n

example (n : ℕ) : 0 < Zeta5.Endpoint.windowNormalizer n :=
  Zeta5.Endpoint.windowNormalizer_pos n

example (n : ℕ) :
    (Zeta5.Endpoint.windowIntegerPolynomial n).eval₂ (Int.castRingHom ℝ)
        (Zeta5.Endpoint.realZeta 5) =
      (Zeta5.Endpoint.windowNormalizer n : ℝ)*Zeta5.Endpoint.windowValue n :=
  Zeta5.Endpoint.windowIntegerPolynomial_eval n

example : ∃ E : ℕ → ℝ,
    Tendsto (fun n => E n/Zeta5.Endpoint.windowScale n) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, Real.log (Zeta5.Endpoint.windowValue n) ≤
      -Zeta5.Certificate.analyticIntegral*Zeta5.Endpoint.windowScale n+E n) :=
  Zeta5.Analysis.exists_analytic_rate_error

example : (54133705070/10^10 : ℝ)<Zeta5.Certificate.analyticIntegral :=
  Zeta5.Certificate.analyticIntegral_gt_displayed

example (K L : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      Real.log (Zeta5.Endpoint.windowNormalizer n : ℝ) ≤
        Zeta5.Analysis.arithmeticMajorant Zeta5.Certificate.allPrimePieces K L n) :
    _root_.Irrational ((_root_.riemannZeta (5 : ℂ)).re) :=
  Zeta5.Analysis.irrational_zeta5_of_allPrimePieces_majorant K L h

set_option pp.fullNames true in
#check @Zeta5.Analysis.exists_analytic_rate_error
set_option pp.fullNames true in
#check @Zeta5.Analysis.PhysicalMeasure.windowDeterminant_realZetaFive_pos
set_option pp.fullNames true in
#check @Zeta5.Analysis.irrational_zeta5_of_allPrimePieces_majorant

#print axioms Zeta5.Endpoint.realZeta_eq_re
#print axioms Zeta5.Endpoint.windowIntegerPolynomial_degree
#print axioms Zeta5.Endpoint.windowIntegerPolynomial_eval
#print axioms Zeta5.Endpoint.windowValue_pos
#print axioms Zeta5.Analysis.exists_analytic_rate_error
#print axioms Zeta5.Certificate.analyticIntegral_gt_displayed
#print axioms Zeta5.Analysis.irrational_zeta5_of_allPrimePieces_majorant
