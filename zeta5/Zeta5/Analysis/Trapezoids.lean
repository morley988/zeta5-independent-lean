import Zeta5.Analysis.ProfileContinuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Certified lower trapezoids for the analytic saving

The grid need not be uniform.  Endpoint and function-value enclosures are
explicit inputs, so exact finite data can be connected to the actual
Lebesgue integral without a numerical-integration axiom.
-/

namespace Zeta5.Analysis

open MeasureTheory Set
open scoped BigOperators

noncomputable section

theorem concave_trapezoid_le_integral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hconc : ConcaveOn ℝ (Icc a b) f) (hcont : ContinuousOn f (Icc a b)) :
    (b - a) / 2 * (f a + f b) ≤ ∫ x in a..b, f x := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  let L : ℝ → ℝ := fun x => (f b - f a) / (b - a) * x +
    (b * f a - a * f b) / (b - a)
  have hden : 0 < b - a := sub_pos.mpr hlt
  have hLcont : Continuous L :=
    (continuous_const.mul continuous_id).add continuous_const
  have hLle : ∀ x ∈ Icc a b, L x ≤ f x := by
    intro x hx
    have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
    have hxrepr : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
      field_simp
      ring
    have h := hconc.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      (div_nonneg (sub_nonneg.mpr hx.2) hden.le)
      (div_nonneg (sub_nonneg.mpr hx.1) hden.le) hsum
    simp only [smul_eq_mul] at h
    rw [hxrepr] at h
    convert! h using 1
    dsimp [L]
    ring
  have hLint : ∫ x in a..b, L x = (b - a) / 2 * (f a + f b) := by
    have hlin : Continuous (fun x : ℝ => (f b - f a) / (b - a) * x) :=
      continuous_id.const_mul _
    have hconst : Continuous (fun _ : ℝ => (b * f a - a * f b) / (b - a)) :=
      continuous_const
    dsimp [L]
    rw [intervalIntegral.integral_add (hlin.intervalIntegrable a b)
      (hconst.intervalIntegrable a b)]
    rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [← hLint]
  exact intervalIntegral.integral_mono_on hab (hLcont.intervalIntegrable a b)
    (hcont.intervalIntegrable_of_Icc hab) hLle

theorem analyticSaving_intervalIntegrable (s : ℝ) (hs : 0 < s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (analyticSaving s hs) volume a b :=
  ((analyticSaving_continuousOn s hs).mono
    (fun _ hx => ha.trans hx.1)).intervalIntegrable_of_Icc hab

theorem analyticSaving_trapezoid_le (s : ℝ) (hs : 0 < s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) / 2 * (analyticSaving s hs a + analyticSaving s hs b) ≤
      ∫ x in a..b, analyticSaving s hs x := by
  apply concave_trapezoid_le_integral hab
  · exact (analyticSaving_strictConcaveOn_nonneg s hs).concaveOn.subset
      (fun _ hx => ha.trans hx.1) (convex_Icc a b)
  · exact (analyticSaving_continuousOn s hs).mono (fun _ hx => ha.trans hx.1)

theorem lower_trapezoid_le (s : ℝ) (hs : 0 < s)
    {a b aUpper bLower faLower fbLower : ℝ}
    (ha : 0 ≤ a) (haUpper : a ≤ aUpper) (hbLower : bLower ≤ b)
    (hwidth : aUpper ≤ bLower)
    (hfa : faLower ≤ analyticSaving s hs a) (hfb : fbLower ≤ analyticSaving s hs b)
    (hfa0 : 0 ≤ faLower) (hfb0 : 0 ≤ fbLower) :
    (bLower - aUpper) / 2 * (faLower + fbLower) ≤
      ∫ x in a..b, analyticSaving s hs x := by
  have hab : a ≤ b := haUpper.trans (hwidth.trans hbLower)
  apply le_trans _ (analyticSaving_trapezoid_le s hs ha hab)
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  · exact add_le_add hfa hfb
  · exact add_nonneg hfa0 hfb0
  · positivity

/-- Sum any finite sequence of lower trapezoids and retain the nonnegative
tail from its last endpoint to `δ`. -/
theorem sum_lower_trapezoids_le (s : ℝ) (hs : 0 < s) (n : ℕ)
    (u lower upper values : ℕ → ℝ) (δ : ℝ)
    (hstart : u 0 = 0)
    (hu : ∀ j ≤ n, 0 ≤ u j)
    (hlower : ∀ j ≤ n, lower j ≤ u j)
    (hupper : ∀ j ≤ n, u j ≤ upper j)
    (hwidth : ∀ j < n, upper j ≤ lower (j + 1))
    (hval : ∀ j ≤ n, values j ≤ analyticSaving s hs (u j))
    (hval0 : ∀ j ≤ n, 0 ≤ values j)
    (hend : u n ≤ δ) :
    ∑ j ∈ Finset.range n, (lower (j + 1) - upper j) / 2 * (values j + values (j + 1)) ≤
      ∫ x in 0..δ, analyticSaving s hs x := by
  have hstep : ∀ j < n, u j ≤ u (j + 1) := fun j hj =>
    (hupper j hj.le).trans ((hwidth j hj).trans (hlower (j + 1) hj))
  have hint : ∀ j < n, IntervalIntegrable (analyticSaving s hs) volume (u j) (u (j + 1)) :=
    fun j hj => analyticSaving_intervalIntegrable s hs (hu j hj.le) (hstep j hj)
  have hsum :
      (∑ j ∈ Finset.range n, (lower (j + 1) - upper j) / 2 * (values j + values (j + 1))) ≤
      ∑ j ∈ Finset.range n, ∫ x in u j..u (j + 1), analyticSaving s hs x := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn := Finset.mem_range.mp hj
    exact lower_trapezoid_le s hs (hu j hjn.le) (hupper j hjn.le)
      (hlower (j + 1) hjn) (hwidth j hjn) (hval j hjn.le) (hval (j + 1) hjn)
      (hval0 j hjn.le) (hval0 (j + 1) hjn)
  rw [intervalIntegral.sum_integral_adjacent_intervals hint, hstart] at hsum
  have htail : 0 ≤ ∫ x in u n..δ, analyticSaving s hs x :=
    intervalIntegral.integral_nonneg hend fun x hx => analyticSaving_nonneg s hs ((hu n le_rfl).trans hx.1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (analyticSaving_intervalIntegrable s hs (a := 0) (b := u n) le_rfl (hu n le_rfl))
    (analyticSaving_intervalIntegrable s hs (hu n le_rfl) hend)
  linarith

end

end Zeta5.Analysis
