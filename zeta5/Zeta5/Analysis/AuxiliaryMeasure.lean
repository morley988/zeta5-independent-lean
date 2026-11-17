import Zeta5.Analysis.Profile
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The positive auxiliary measure as an arcsine mixture

We construct the measure directly as the image of
`u_s'(a) da × dθ/π`, `0<a≤b`, `0<θ≤π`, under `(a,θ) ↦ a cos θ`.
Its positivity is built into the definition, and its total mass is the exact
profile mass.  This is the positive arcsine-mixture description underlying the
manuscript's density calculation.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Zeta5.Analysis

lemma profileMassSlope_continuous {s : ℝ} (hs : 0 < s) :
    Continuous (profileMassSlope s) := by
  have h1 : ∀ a : ℝ, Real.sqrt (1+a^2) ≠ 0 := fun a => by positivity
  have h2 : ∀ a : ℝ, Real.sqrt (s^2+a^2) ≠ 0 := fun a => by positivity
  have c1 : Continuous (fun a : ℝ => a / Real.sqrt (1+a^2)) :=
    continuous_id.div ((continuous_const.add (continuous_id.pow 2)).sqrt) h1
  have c2 : Continuous (fun a : ℝ => 2*a / Real.sqrt (s^2+a^2)) :=
    (continuous_const.mul continuous_id).div
      ((continuous_const.add (continuous_id.pow 2)).sqrt) h2
  exact ((continuous_const.sub c1).add c2).div_const 2

lemma profileMassSlope_nonneg {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    0 ≤ profileMassSlope s a := by
  rcases ha.eq_or_lt with rfl | ha
  · norm_num [profileMassSlope]
  · exact (profileMassSlope_pos hs ha).le

lemma profileMassSlope_le_three_halves {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    profileMassSlope s a ≤ 3/2 := by
  have h1 : 0 ≤ a / Real.sqrt (1+a^2) := by positivity
  have hden : 0 < Real.sqrt (s^2+a^2) := by positivity
  have h2 : a / Real.sqrt (s^2+a^2) ≤ 1 :=
    (div_le_one hden).mpr (sqrt_sum_sq_gt_right hs ha).le
  dsimp [profileMassSlope]
  rw [mul_div_assoc]
  linarith

/-- Uniform angular probability on a half-circle. -/
noncomputable def angleMeasure : Measure ℝ :=
  ENNReal.ofReal (1/Real.pi) • volume.restrict (Ioc 0 Real.pi)

lemma angleMeasure_mass : angleMeasure univ = 1 := by
  simp only [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel Real.pi_ne_zero]
  simp

instance angleMeasure_probability : IsProbabilityMeasure angleMeasure where
  measure_univ := angleMeasure_mass

/-- Radial mass density.  The positivity proof parameter makes the finite-measure
instance available without introducing a separate typeclass assumption. -/
noncomputable def radialMeasure (s : ℝ) (_hs : 0 < s) (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 b)).withDensity (fun a => ENNReal.ofReal (profileMassSlope s a))

lemma radialMeasure_le (s : ℝ) (hs : 0 < s) (b : ℝ) :
    radialMeasure s hs b ≤ ENNReal.ofReal (3/2 : ℝ) • volume.restrict (Ioc 0 b) := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
  exact ENNReal.ofReal_le_ofReal (profileMassSlope_le_three_halves hs ha.1.le)

instance radialMeasure_isFinite (s : ℝ) (hs : 0 < s) (b : ℝ) :
    IsFiniteMeasure (radialMeasure s hs b) where
  measure_univ_lt_top := by
    apply lt_of_le_of_lt (radialMeasure_le s hs b univ)
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma integral_profileMassSlope (s : ℝ) (hs : 0 < s) (b : ℝ) :
    (∫ a in 0..b, profileMassSlope s a) = profileMass s b := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => profileMass_hasDerivAt hs)
    ((profileMassSlope_continuous hs).intervalIntegrable 0 b), profileMass_zero hs.le, sub_zero]

lemma radialMeasure_mass (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    radialMeasure s hs b univ = ENNReal.ofReal (profileMass s b) := by
  rw [radialMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (((profileMassSlope_continuous hs).intervalIntegrable 0 b).1)]
  · rw [← intervalIntegral.integral_of_le hb, integral_profileMassSlope s hs b]
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    exact profileMassSlope_nonneg hs ha.1.le

lemma radialMeasure_ae_mem (s : ℝ) (hs : 0 < s) (b : ℝ) :
    ∀ᵐ a ∂radialMeasure s hs b, a ∈ Ioc (0 : ℝ) b :=
  (withDensity_absolutelyContinuous (volume.restrict (Ioc (0 : ℝ) b)) _).ae_le
    (self_mem_ae_restrict measurableSet_Ioc)

noncomputable def auxiliaryMeasure (s : ℝ) (hs : 0 < s) (b : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 * Real.cos p.2)
    ((radialMeasure s hs b).prod angleMeasure)

noncomputable def squaredAuxiliaryMeasure (s : ℝ) (hs : 0 < s) (b : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => (p.1 * Real.cos p.2)^2)
    ((radialMeasure s hs b).prod angleMeasure)

lemma auxiliaryMap_measurable : Measurable (fun p : ℝ × ℝ => p.1 * Real.cos p.2) := by
  fun_prop

lemma squaredAuxiliaryMap_measurable :
    Measurable (fun p : ℝ × ℝ => (p.1 * Real.cos p.2)^2) := by fun_prop

instance auxiliaryMeasure_isFinite (s : ℝ) (hs : 0 < s) (b : ℝ) :
    IsFiniteMeasure (auxiliaryMeasure s hs b) := by
  unfold auxiliaryMeasure
  infer_instance

instance squaredAuxiliaryMeasure_isFinite (s : ℝ) (hs : 0 < s) (b : ℝ) :
    IsFiniteMeasure (squaredAuxiliaryMeasure s hs b) := by
  unfold squaredAuxiliaryMeasure
  infer_instance

lemma auxiliaryMeasure_mass (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    auxiliaryMeasure s hs b univ = ENNReal.ofReal (profileMass s b) := by
  rw [auxiliaryMeasure, Measure.map_apply auxiliaryMap_measurable MeasurableSet.univ]
  rw [preimage_univ, ← univ_prod_univ, Measure.prod_prod, angleMeasure_mass, mul_one,
    radialMeasure_mass s hs hb]

lemma squaredAuxiliaryMeasure_mass (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    squaredAuxiliaryMeasure s hs b univ = ENNReal.ofReal (profileMass s b) := by
  rw [squaredAuxiliaryMeasure, Measure.map_apply squaredAuxiliaryMap_measurable MeasurableSet.univ]
  rw [preimage_univ, ← univ_prod_univ, Measure.prod_prod, angleMeasure_mass, mul_one,
    radialMeasure_mass s hs hb]

lemma squaredAuxiliaryMeasure_eq_map_square (s : ℝ) (hs : 0 < s) (b : ℝ) :
    squaredAuxiliaryMeasure s hs b =
      Measure.map (fun x : ℝ => x^2) (auxiliaryMeasure s hs b) := by
  rw [auxiliaryMeasure, Measure.map_map (by fun_prop) auxiliaryMap_measurable]
  rfl

lemma squaredAuxiliaryMeasure_ae_mem (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ v ∂squaredAuxiliaryMeasure s hs b, v ∈ Icc (0 : ℝ) (b^2) := by
  change ∀ᵐ v ∂squaredAuxiliaryMeasure s hs b, 0 ≤ v ∧ v ≤ b^2
  rw [squaredAuxiliaryMeasure,
    ae_map_iff squaredAuxiliaryMap_measurable.aemeasurable measurableSet_Icc]
  apply (Measure.ae_prod_iff_ae_ae (squaredAuxiliaryMap_measurable measurableSet_Icc)).mpr
  filter_upwards [radialMeasure_ae_mem s hs b] with a ha
  apply Eventually.of_forall
  intro θ
  constructor
  · exact sq_nonneg _
  · have hc := Real.abs_cos_le_one θ
    have hab : |a*Real.cos θ| ≤ b := by
      rw [abs_mul, abs_of_pos ha.1]
      exact (mul_le_of_le_one_right ha.1.le hc).trans ha.2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr hab

end Zeta5.Analysis
