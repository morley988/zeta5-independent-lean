import Zeta5.Analysis.PhysicalMeasureGram
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual positive measure on the moment variable

`physicalMeasure` is the pushforward of `density(x) dx` on `x > 0` under
`x ↦ x²`.  The integral adapter below makes that definition agree with the
already verified moment and Gram integrals.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators ENNReal

/-- The density measure on the positive `x` half line. -/
def xMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (density x))

/-- The manuscript's measure in the variable `t=x²`. -/
def physicalMeasure : Measure ℝ := Measure.map (fun x : ℝ => x ^ 2) xMeasure

theorem measurable_square : Measurable (fun x : ℝ => x ^ 2) := by fun_prop

/-- Integration against the pushforward is exactly the original density integral. -/
theorem integral_physicalMeasure {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ t, f t ∂physicalMeasure) = ∫ x : ℝ in Ioi 0, f (x ^ 2) * density x := by
  rw [physicalMeasure, integral_map measurable_square.aemeasurable hf.aestronglyMeasurable,
    xMeasure, integral_withDensity_eq_integral_toReal_smul density_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [ENNReal.toReal_ofReal (density_pos hx).le, smul_eq_mul, mul_comm]

/-- Integrability is also preserved by the physical-measure adapter. -/
theorem integrable_physicalMeasure_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f physicalMeasure ↔
      IntegrableOn (fun x : ℝ => f (x ^ 2) * density x) (Ioi 0) := by
  rw [physicalMeasure, integrable_map_measure hf.aestronglyMeasurable
    measurable_square.aemeasurable, xMeasure,
    integrable_withDensity_iff_integrable_smul' density_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (density_pos hx).le, smul_eq_mul, mul_comm]

theorem physicalMeasure_mass : physicalMeasure univ = ENNReal.ofReal (5 / 12 : ℝ) := by
  rw [physicalMeasure, Measure.map_apply measurable_square MeasurableSet.univ]
  simp only [preimage_univ]
  rw [xMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal density_integrable, density_mass]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact (density_pos hx).le

instance physicalMeasure_isFinite : IsFiniteMeasure physicalMeasure where
  measure_univ_lt_top := by rw [physicalMeasure_mass]; exact ENNReal.ofReal_lt_top

/-- Every nonnegative integer moment exists. -/
theorem physicalMeasure_moment_integrable (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) physicalMeasure := by
  apply (integrable_physicalMeasure_iff (show Measurable (fun t : ℝ => t ^ k) from by fun_prop)).mpr
  simpa only [← pow_mul] using density_moment_integrable k

/-- The positive measure has exactly the rational moments used by the matrix. -/
theorem physicalMeasure_moment (k : ℕ) :
    (∫ t : ℝ, t ^ k ∂physicalMeasure) = (Zeta5.Construction.rationalMoment k : ℝ) := by
  rw [integral_physicalMeasure (show Measurable (fun t : ℝ => t ^ k) from by fun_prop)]
  simpa only [← pow_mul] using density_moment k

/-- The polynomial part of the exact rational matrix is physical integration. -/
theorem physicalMeasure_polynomial_integral (p : ℚ[X]) :
    (∫ t : ℝ, (p.map (Rat.castHom ℝ)).eval t ∂physicalMeasure) =
      (Zeta5.Construction.polynomialMoment p : ℝ) := by
  rw [integral_physicalMeasure (p.map (Rat.castHom ℝ)).continuous.measurable]
  simpa only [momentFunctional_apply, weightedDensity_zero] using momentFunctional_zero_rational p

/-- The denominator-weighted polynomial functional is also an integral on the
actual pushforward measure. -/
theorem momentFunctional_eq_measure_integral (N : ℕ) (p : ℝ[X]) :
    momentFunctional N p =
      ∫ t : ℝ, p.eval t / (realDenominator N).eval t ∂physicalMeasure := by
  rw [integral_physicalMeasure (show Measurable (fun t : ℝ => p.eval t / (realDenominator N).eval t) from by fun_prop),
    momentFunctional_apply]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [weightedDensity]
  ring

/-- The pushforward measure is concentrated on the strictly positive half line. -/
theorem physicalMeasure_ae_pos : ∀ᵐ t : ℝ ∂physicalMeasure, 0 < t := by
  rw [physicalMeasure, ae_map_iff measurable_square.aemeasurable measurableSet_Ioi]
  have hx : ∀ᵐ x : ℝ ∂xMeasure, 0 < x :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi (0 : ℝ)))
      (fun x => ENNReal.ofReal (density x))).ae_le
      (self_mem_ae_restrict measurableSet_Ioi)
  exact hx.mono (fun x hx => sq_pos_of_pos hx)

theorem physicalMeasure_polynomial_integrable (p : ℝ[X]) :
    Integrable p.eval physicalMeasure := by
  exact (integrable_physicalMeasure_iff p.continuous.measurable).mpr (polynomial_density_integrable p)

/-- Every Stieltjes kernel at a positive argument is integrable. -/
theorem physicalMeasure_stieltjes_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (fun t : ℝ => 1 / (t + y ^ 2)) physicalMeasure := by
  apply (integrable_const (1 / y ^ 2 : ℝ)).mono'
    (show Measurable (fun t : ℝ => 1 / (t + y ^ 2)) from by fun_prop).aestronglyMeasurable
  filter_upwards [physicalMeasure_ae_pos] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (t + y ^ 2))]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hy) (by linarith)

/-- The physical Stieltjes transform, with convergence already established for `y>0`. -/
def stieltjesTransform (y : ℝ) : ℝ := ∫ t : ℝ, 1 / (t + y ^ 2) ∂physicalMeasure

theorem stieltjesTransform_density (y : ℝ) :
    stieltjesTransform y = ∫ x : ℝ in Ioi 0, density x / (x ^ 2 + y ^ 2) := by
  rw [stieltjesTransform, integral_physicalMeasure (by fun_prop)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  ring

end Zeta5.Analysis.PhysicalMeasure
