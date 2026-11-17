import Zeta5.Analysis.PhysicalMeasureStieltjesCoth
import Zeta5.Analysis.PhysicalMeasureZetaTail
import Zeta5.Analysis.PhysicalMeasureCauchyFourthIntegrals
import Zeta5.Analysis.PhysicalMeasurePencil

/-!
# The physical Stieltjes identity and the actual positive determinant

The identity is derived from the positive exponential density, four Laplace
integrations by parts, the cotangent partial fractions, and exact rational
Cauchy integrals. Every convergence and interchange is proved in the imported
modules. No Binet formula or additional analytic hypothesis is assumed.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Polynomial Zeta5.Construction
open scoped BigOperators

theorem cothFourthTerm_integral (n : ℕ) {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in Ioi 0, cothFourthTerm n y x) =
      12 * Real.pi / (((n + 1 : ℕ) : ℝ) + y) ^ 5 :=
  Zeta5.Analysis.product_fourthCauchyKernel_integral (by positivity) hy

/-- The physical transform equals the fourth Hurwitz zeta tail, with the two
boundary corrections obtained by integration by parts. -/
theorem stieltjesTransform_hurwitz {y : ℝ} (hy : 0 < y) :
    stieltjesTransform y = y ^ 4 * hurwitzFive y - 1 / (2 * y) - 1 / 4 := by
  rw [stieltjesTransform_coth hy, Zeta5.Analysis.fourthCauchyKernel_integral hy,
    Zeta5.Analysis.linear_fourthCauchyKernel_integral hy]
  have hsum : (∑' n : ℕ, ∫ x : ℝ in Ioi 0, cothFourthTerm n y x) =
      (12 * Real.pi) * (hurwitzFive y - 1 / y ^ 5) := by
    calc
      _ = ∑' n : ℕ, (12 * Real.pi) *
          (1 / (((n + 1 : ℕ) : ℝ) + y) ^ 5) := by
        apply tsum_congr
        intro n
        rw [cothFourthTerm_integral n hy]
        ring
      _ = (12 * Real.pi) * ∑' n : ℕ,
          1 / (((n + 1 : ℕ) : ℝ) + y) ^ 5 := tsum_mul_left
      _ = _ := by rw [hurwitzFive_shift hy]; ring
  rw [hsum]
  field_simp [hy.ne', Real.pi_ne_zero]
  ring

/-- The exact affine formula in ζ(5) at every positive integer. -/
theorem stieltjesTransform_nat {i : ℕ} (hi : 0 < i) :
    stieltjesTransform (i : ℝ) =
      (stieltjes i).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) := by
  rw [stieltjesTransform_hurwitz (by exact_mod_cast hi), hurwitzFive_nat hi]
  simp only [stieltjes, stieltjesConstant, eval₂_add, eval₂_C, eval₂_mul, eval₂_X,
    Rat.coe_castHom, Rat.cast_sub, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  ring

theorem stieltjesAtPositiveIntegers_realZetaFive :
    StieltjesAtPositiveIntegers (Zeta5.Endpoint.realZeta 5) :=
  fun _ hi => stieltjesTransform_nat hi

/-- The intended integral interpretation of the actual polynomial functional. -/
theorem momentFunctional_eq_numeratorFunctional_realZetaFive (N : ℕ) (P : ℚ[X]) :
    momentFunctional N (P.map (Rat.castHom ℝ)) =
      (numeratorFunctional N P).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) :=
  momentFunctional_eq_numeratorFunctional stieltjesAtPositiveIntegers_realZetaFive N P

/-- Strict positivity of the actual ζ(5) determinant, with all measure and
Stieltjes inputs discharged. This also includes the empty determinant at n=0. -/
theorem windowDeterminant_realZetaFive_pos (n : ℕ) :
    0 < (windowDeterminant n).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) :=
  windowDeterminant_pos_of_stieltjes stieltjesAtPositiveIntegers_realZetaFive n

theorem windowDeterminant_ne_zero (n : ℕ) : windowDeterminant n ≠ 0 :=
  windowDeterminant_ne_zero_of_stieltjes stieltjesAtPositiveIntegers_realZetaFive n

end Zeta5.Analysis.PhysicalMeasure
