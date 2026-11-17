import Zeta5.Analysis.AuxiliaryMeasure
import Zeta5.Analysis.TrialPolynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniform small-ball control for the actual auxiliary measure

The arcsine-mixture construction allows a direct estimate, avoiding density
singularities.  Split angles according to `|cos θ| < ρ`.  The first set has
angular mass at most `ρ`; on its complement the radial section has length at
most `2ρ`.  The resulting Hölder bound supplies the verified trial-polynomial
theorem without an unproved quantile regularity assumption.
-/

open MeasureTheory Set Filter Metric Polynomial
open scoped ENNReal

namespace Zeta5.Analysis

lemma angleMeasure_abs_cos_lt_le {ρ : ℝ} (hρ : 0 < ρ) :
    angleMeasure {θ : ℝ | |Real.cos θ| < ρ} ≤ ENNReal.ofReal ρ := by
  have hmeas : MeasurableSet {θ : ℝ | |Real.cos θ| < ρ} := measurableSet_lt (by fun_prop) measurable_const
  have hsub : {θ : ℝ | |Real.cos θ| < ρ} ∩ Ioc 0 Real.pi ⊆
      Ioo (Real.pi/2-Real.pi*ρ/2) (Real.pi/2+Real.pi*ρ/2) := by
    intro θ hθ
    have hdist : |Real.pi/2-θ| ≤ Real.pi/2 := by
      apply abs_le.mpr
      constructor <;> linarith [hθ.2.1, hθ.2.2]
    have hsin := Real.mul_abs_le_abs_sin hdist
    rw [Real.sin_pi_div_two_sub] at hsin
    have hlt : (2/Real.pi)*|Real.pi/2-θ| < ρ := lt_of_le_of_lt hsin hθ.1
    have habs : |Real.pi/2-θ| < Real.pi*ρ/2 := by
      have hh := (lt_div_iff₀ (show 0 < 2/Real.pi by positivity)).mpr
        (show |Real.pi/2-θ| * (2/Real.pi) < ρ by simpa [mul_comm] using hlt)
      convert! hh using 1 <;> field_simp <;> ring
    have hh := abs_lt.mp habs
    constructor <;> linarith [hh.1, hh.2]
  calc
    angleMeasure {θ : ℝ | |Real.cos θ| < ρ} =
        ENNReal.ofReal (1/Real.pi) *
          volume ({θ : ℝ | |Real.cos θ| < ρ} ∩ Ioc 0 Real.pi) := by
      rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply hmeas]
      rfl
    _ ≤ ENNReal.ofReal (1/Real.pi) *
        volume (Ioo (Real.pi/2-Real.pi*ρ/2) (Real.pi/2+Real.pi*ρ/2)) :=
      mul_le_mul_right (measure_mono hsub) _
    _ = ENNReal.ofReal ρ := by
      rw [Real.volume_Ioo]
      rw [show Real.pi/2+Real.pi*ρ/2-(Real.pi/2-Real.pi*ρ/2) = Real.pi*ρ by ring]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

lemma square_window_sub_le {x y c v ρ : ℝ} (hρ : 0 < ρ) (hc : ρ ≤ |c|)
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (hxwin : |v-(x*c)^2| < ρ^4) (hywin : |v-(y*c)^2| < ρ^4) :
    y-x ≤ 2*ρ := by
  have hc2 : ρ^2 ≤ c^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hρ.le (abs_nonneg c)).mpr hc
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hdsq : (y-x)^2 ≤ y^2-x^2 := by nlinarith
  have hwindow : (y^2-x^2)*c^2 < 2*ρ^4 := by
    have h1 := (abs_lt.mp hywin).1
    have h2 := (abs_lt.mp hxwin).2
    nlinarith
  have hcomp : (y-x)^2*ρ^2 ≤ (y^2-x^2)*c^2 :=
    (mul_le_mul_of_nonneg_left hc2 (sq_nonneg (y-x))).trans
      (mul_le_mul_of_nonneg_right hdsq (sq_nonneg c))
  by_contra h
  have hbig : 2*ρ < y-x := lt_of_not_ge h
  have hsq : 4*ρ^2 < (y-x)^2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hsq (sq_pos_of_pos hρ)
  have hρ4 : 0 < ρ^4 := pow_pos hρ 4
  nlinarith

lemma square_window_dist_le {x y c v ρ : ℝ} (hρ : 0 < ρ) (hc : ρ ≤ |c|)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxwin : |v-(x*c)^2| < ρ^4) (hywin : |v-(y*c)^2| < ρ^4) :
    dist x y ≤ 2*ρ := by
  rw [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact square_window_sub_le hρ hc hx hxy hxwin hywin
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact square_window_sub_le hρ hc hy hyx hywin hxwin

lemma volume_square_window_le {c v ρ b : ℝ} (hρ : 0 < ρ) (hc : ρ ≤ |c|) :
    volume ({a : ℝ | |v-(a*c)^2| < ρ^4} ∩ Ioc 0 b) ≤ ENNReal.ofReal (2*ρ) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
  intro x hx y hy
  exact square_window_dist_le hρ hc hx.2.1.le hy.2.1.le hx.1 hy.1

lemma radialMeasure_square_window_le (s : ℝ) (hs : 0 < s) (b : ℝ)
    {c v ρ : ℝ} (hρ : 0 < ρ) (hc : ρ ≤ |c|) :
    radialMeasure s hs b {a : ℝ | |v-(a*c)^2| < ρ^4} ≤ ENNReal.ofReal (3*ρ) := by
  have hmeas : MeasurableSet {a : ℝ | |v-(a*c)^2| < ρ^4} := measurableSet_lt (by fun_prop) measurable_const
  calc
    _ ≤ (ENNReal.ofReal (3/2 : ℝ) • volume.restrict (Ioc 0 b))
          {a : ℝ | |v-(a*c)^2| < ρ^4} := radialMeasure_le s hs b _
    _ = ENNReal.ofReal (3/2 : ℝ) * volume ({a : ℝ | |v-(a*c)^2| < ρ^4} ∩ Ioc 0 b) := by
      rw [Measure.smul_apply, Measure.restrict_apply hmeas]
      rfl
    _ ≤ ENNReal.ofReal (3/2 : ℝ) * ENNReal.ofReal (2*ρ) :=
      mul_le_mul_right (volume_square_window_le hρ hc) _
    _ = ENNReal.ofReal (3*ρ) := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

lemma radialMeasure_mass_le (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    radialMeasure s hs b univ ≤ ENNReal.ofReal ((3/2 : ℝ)*b) := by
  calc
    _ ≤ (ENNReal.ofReal (3/2 : ℝ) • volume.restrict (Ioc 0 b)) univ :=
      radialMeasure_le s hs b univ
    _ = ENNReal.ofReal ((3/2 : ℝ)*b) := by
      simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, smul_eq_mul]
      rw [ENNReal.ofReal_mul (by norm_num)]

/-- The squared auxiliary measure has uniform Hölder exponent `1/4`, with an
explicit constant independent of `s` and of the center of the ball. -/
theorem squaredAuxiliaryMeasure_smallBall (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b)
    (v : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    squaredAuxiliaryMeasure s hs b {w : ℝ | |v-w| < ρ^4} ≤
      ENNReal.ofReal ((3+(3/2 : ℝ)*b)*ρ) := by
  let A : Set ℝ := {θ : ℝ | |Real.cos θ| < ρ}
  let f : ℝ → ℝ≥0∞ := fun θ =>
    radialMeasure s hs b {a : ℝ | |v-(a*Real.cos θ)^2| < ρ^4}
  have hA : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_const
  have hE : MeasurableSet {w : ℝ | |v-w| < ρ^4} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hlow : (∫⁻ θ in A, f θ ∂angleMeasure) ≤
      ENNReal.ofReal ((3/2 : ℝ)*b) * ENNReal.ofReal ρ := by
    calc
      _ ≤ ∫⁻ _θ in A, ENNReal.ofReal ((3/2 : ℝ)*b) ∂angleMeasure := by
        apply lintegral_mono
        intro θ
        exact (measure_mono (subset_univ _)).trans (radialMeasure_mass_le s hs hb)
      _ = ENNReal.ofReal ((3/2 : ℝ)*b) * angleMeasure A := by simp
      _ ≤ ENNReal.ofReal ((3/2 : ℝ)*b) * ENNReal.ofReal ρ :=
        mul_le_mul_right (angleMeasure_abs_cos_lt_le hρ) _
  have hhigh : (∫⁻ θ in Aᶜ, f θ ∂angleMeasure) ≤ ENNReal.ofReal (3*ρ) := by
    calc
      _ ≤ ∫⁻ _θ in Aᶜ, ENNReal.ofReal (3*ρ) ∂angleMeasure := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict hA.compl] with θ hθ
        exact radialMeasure_square_window_le s hs b hρ (le_of_not_gt hθ)
      _ = ENNReal.ofReal (3*ρ) * angleMeasure Aᶜ := by simp
      _ ≤ ENNReal.ofReal (3*ρ) * 1 :=
        mul_le_mul_right ((measure_mono (subset_univ _)).trans_eq angleMeasure_mass) _
      _ = ENNReal.ofReal (3*ρ) := mul_one _
  rw [squaredAuxiliaryMeasure, Measure.map_apply squaredAuxiliaryMap_measurable hE,
    Measure.prod_apply_symm (squaredAuxiliaryMap_measurable hE)]
  change (∫⁻ θ, f θ ∂angleMeasure) ≤ _
  rw [← lintegral_add_compl f hA]
  calc
    _ ≤ ENNReal.ofReal ((3/2 : ℝ)*b) * ENNReal.ofReal ρ + ENNReal.ofReal (3*ρ) :=
      add_le_add hlow hhigh
    _ = ENNReal.ofReal ((3+(3/2 : ℝ)*b)*ρ) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

instance squaredAuxiliaryMeasure_nullSingleton (s : ℝ) (hs : 0 < s) (b : ℝ) :
    NullSingletonClass (squaredAuxiliaryMeasure s hs b) := by
  by_cases hb : 0 ≤ b
  · exact nullSingletonClass_of_fourth_power_smallBall _ (by positivity)
      (fun v ρ hρ => squaredAuxiliaryMeasure_smallBall s hs hb v hρ)
  · have he : Ioc (0 : ℝ) b = ∅ := Ioc_eq_empty_of_le (le_of_not_ge hb)
    simp only [squaredAuxiliaryMeasure, radialMeasure, he, Measure.restrict_empty,
      withDensity_zero_left, Measure.zero_prod, Measure.map_zero]
    exact ⟨fun x => by simp⟩

lemma squaredAuxiliaryMeasure_ae_mem_Ioc (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ v ∂squaredAuxiliaryMeasure s hs b, v ∈ Ioc (0 : ℝ) (b^2) := by
  filter_upwards [squaredAuxiliaryMeasure_ae_mem s hs hb,
    (squaredAuxiliaryMeasure s hs b).ae_ne 0] with v hv hne
  exact ⟨lt_of_le_of_ne hv.1 (Ne.symm hne), hv.2⟩

lemma squaredAuxiliaryMeasure_real_Ioc (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    (squaredAuxiliaryMeasure s hs b).real (Ioc (0 : ℝ) (b^2)) = profileMass s b := by
  have he : squaredAuxiliaryMeasure s hs b (Ioc (0 : ℝ) (b^2)) =
      squaredAuxiliaryMeasure s hs b univ := by
    apply measure_congr
    filter_upwards [squaredAuxiliaryMeasure_ae_mem_Ioc s hs hb] with v hv
    exact propext (iff_of_true hv (mem_univ v))
  rw [measureReal_def, he, squaredAuxiliaryMeasure_mass s hs hb,
    ENNReal.toReal_ofReal (profileMass_nonneg hs hb)]

/-- The concrete positive auxiliary measure now supplies actual trial
polynomials; this is the discretization component of the analytic argument. -/
theorem auxiliaryMeasure_trial_polynomial (s : ℝ) (hs : 0 < s) {b N : ℝ}
    (hb : 0 ≤ b) (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)
    (hmass : profileMass s b = (n : ℝ)/N) :
    ∃ p : ℝ[X], p.Monic ∧ p.natDegree = n ∧ ∀ v : ℝ,
      |p.eval (N^2*v)|^2 ≤
        Real.exp (8*(3+(3/2 : ℝ)*b)) * (1+b^2)^4 * N^(4*n+16) *
          Real.exp (2*N*(∫ w in 0..b^2, Real.log |v-w|
            ∂squaredAuxiliaryMeasure s hs b)) := by
  exact exists_monic_scaled_trial_polynomial (squaredAuxiliaryMeasure s hs b)
    hN (by positivity) (sq_nonneg b) n hn
    ((squaredAuxiliaryMeasure_real_Ioc s hs hb).trans hmass)
    (fun v ρ hρ => squaredAuxiliaryMeasure_smallBall s hs hb v hρ)

end Zeta5.Analysis
