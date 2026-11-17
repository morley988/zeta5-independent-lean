import Zeta5.Analysis.AbelKernel
import Zeta5.Analysis.ArcsinePotential
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# A positive-kernel representation of arcsine potential growth

This representation turns the equilibrium inequality into Tonelli's theorem:
for positive radius `a` and nonnegative `y`, the increase of the arcsine
potential from zero is the integral of the nonnegative Abel kernel in `y`.
-/

open MeasureTheory Set

namespace Zeta5.Analysis

lemma abelKernel_eq_zero_of_le {a t : ℝ} (ht : 0 ≤ t) (hta : t ≤ a) :
    abelKernel t a = 0 := by
  have hrad : t^2-a^2 ≤ 0 := by nlinarith
  simp [abelKernel, Real.sqrt_eq_zero_of_nonpos hrad]

lemma integral_abelKernel_below {a y : ℝ} (hy : 0 ≤ y) (hya : y ≤ a) :
    IntervalIntegrable (fun t => abelKernel t a) volume 0 y ∧
      (∫ t in 0..y, abelKernel t a) = 0 := by
  have heq : EqOn (fun t => abelKernel t a) (fun _ => (0 : ℝ)) (uIcc 0 y) := by
    rw [uIcc_of_le hy]
    intro t ht
    exact abelKernel_eq_zero_of_le ht.1 (ht.2.trans hya)
  refine ⟨(intervalIntegrable_congr (heq.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const, ?_⟩
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

lemma sqrt_div_sq_sub_one {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    Real.sqrt ((t/a)^2-1) = Real.sqrt (t^2-a^2)/a := by
  rw [show (t/a)^2-1 = (t^2-a^2)/a^2 by field_simp <;> ring,
    Real.sqrt_div (by nlinarith), Real.sqrt_sq ha.le]

lemma arcosh_scaled_hasDerivAt {a t : ℝ} (ha : 0 < a) (ht : a < t) :
    HasDerivAt (fun x : ℝ => Real.arcosh (x/a)) (abelKernel t a) t := by
  have harg : 1 < t/a := (lt_div_iff₀ ha).mpr (by simpa using ht)
  have hh := (Real.hasDerivAt_arcosh harg).comp t ((hasDerivAt_id t).div_const a)
  convert! hh using 1
  rw [sqrt_div_sq_sub_one ha ht.le]
  dsimp [abelKernel]
  field_simp

lemma integral_abelKernel_above {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    IntervalIntegrable (fun t => abelKernel t a) volume a y ∧
      (∫ t in a..y, abelKernel t a) = Real.arcosh (y/a) := by
  have hcont : ContinuousOn (fun t : ℝ => Real.arcosh (t/a)) (Icc a y) :=
    Real.continuousOn_arcosh.comp (continuous_id.div_const a).continuousOn
      (fun t ht => (le_div_iff₀ ha).mpr (by simpa using ht.1))
  obtain ⟨hi, hv⟩ := integral_of_nonnegative_derivative hay hcont
    (fun t ht => arcosh_scaled_hasDerivAt ha ht.1) (fun t _ => abelKernel_nonneg t a)
  exact ⟨hi, by simpa [ha.ne'] using hv⟩

lemma arcsinePotential_sub_zero_eq_arcosh {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    arcsinePotential a y-Real.log (a/2) = Real.arcosh (y/a) := by
  rw [(arcsinePotential_of_le ha hay).2, Real.arcosh, sqrt_div_sq_sub_one ha hay]
  have hy : 0 < y := lt_of_lt_of_le ha hay
  rw [← Real.log_div (by positivity : (y+Real.sqrt (y^2-a^2))/2 ≠ 0)
    (by positivity : a/2 ≠ 0)]
  congr 1
  field_simp

/-- The exact positive-kernel formula for the arcsine potential. -/
theorem arcsinePotential_eq_log_add_abel {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    IntervalIntegrable (fun t => abelKernel t a) volume 0 y ∧
      arcsinePotential a y = Real.log (a/2)+(∫ t in 0..y, abelKernel t a) := by
  by_cases hya : y ≤ a
  · obtain ⟨hi, hv⟩ := integral_abelKernel_below hy hya
    refine ⟨hi, ?_⟩
    rw [hv, add_zero]
    exact (arcsinePotential_of_abs_le ha (by simpa [abs_of_nonneg hy] using hya)).2
  · have hay : a ≤ y := le_of_not_ge hya
    obtain ⟨h0, h0v⟩ := integral_abelKernel_below ha.le (le_refl a)
    obtain ⟨h1, h1v⟩ := integral_abelKernel_above ha hay
    refine ⟨h0.trans h1, ?_⟩
    have hsum := intervalIntegral.integral_add_adjacent_intervals h0 h1
    rw [h0v, h1v, zero_add] at hsum
    have hW := arcsinePotential_sub_zero_eq_arcosh ha hay
    linarith

end Zeta5.Analysis
