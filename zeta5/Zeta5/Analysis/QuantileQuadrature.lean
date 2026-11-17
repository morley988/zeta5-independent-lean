import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Equal-mass quadrature for truncated logarithms

A monotone function's quadrature error is bounded by its variation, independently
of the sizes of the cells.  Splitting a truncated logarithm into an increasing
and a decreasing function makes this estimate apply uniformly across its center.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Zeta5.Analysis

lemma scaled_integral_const_of_cell_mass (μ : Measure ℝ) {N a b c : ℝ}
    (hN : N ≠ 0) (hab : a ≤ b) (hmass : μ.real (Ioc a b) = 1 / N) :
    N * (∫ _ in a..b, c ∂μ) = c := by
  rw [intervalIntegral.integral_const']
  have hempty : Ioc b a = ∅ := Ioc_eq_empty_of_le hab
  rw [hempty, measureReal_empty, hmass]
  simp only [sub_zero, smul_eq_mul]
  field_simp

/-- A sample from each equal-mass interval gives an upper quadrature error at
most the variation of an increasing function. -/
theorem monotone_equalMass_quadrature (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N : ℝ} (hN : 0 < N) (n : ℕ) (a sample : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : Monotone f) (hfi : ∀ j < n, IntervalIntegrable f μ (a j) (a (j+1)))
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1 / N) :
    (∑ j ∈ Finset.range n, f (sample j)) ≤
      N * (∫ w in a 0..a n, f w ∂μ) + f (a n) - f (a 0) := by
  have hcell (j : ℕ) (hj : j < n) :
      f (sample j) - N * (∫ w in a j..a (j+1), f w ∂μ) ≤
        f (a (j+1)) - f (a j) := by
    have hl := intervalIntegral.integral_mono_on (ha j hj) intervalIntegrable_const
      (hfi j hj) (fun w hw => hf hw.1)
    have hl' := mul_le_mul_of_nonneg_left hl hN.le
    rw [scaled_integral_const_of_cell_mass μ hN.ne' (ha j hj) (hmass j hj)] at hl'
    have hu := hf (hsample j hj).2
    linarith
  have hsum : (∑ j ∈ Finset.range n, f (sample j)) -
      N * (∫ w in a 0..a n, f w ∂μ) ≤ f (a n) - f (a 0) := calc
    _ = ∑ j ∈ Finset.range n,
        (f (sample j) - N * (∫ w in a j..a (j+1), f w ∂μ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        intervalIntegral.sum_integral_adjacent_intervals hfi]
    _ ≤ ∑ j ∈ Finset.range n, (f (a (j+1)) - f (a j)) :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = f (a n) - f (a 0) := Finset.sum_range_sub (fun j => f (a j)) n
  linarith

/-- The same estimate for a decreasing function. -/
theorem antitone_equalMass_quadrature (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N : ℝ} (hN : 0 < N) (n : ℕ) (a sample : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : Antitone f) (hfi : ∀ j < n, IntervalIntegrable f μ (a j) (a (j+1)))
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1 / N) :
    (∑ j ∈ Finset.range n, f (sample j)) ≤
      N * (∫ w in a 0..a n, f w ∂μ) + f (a 0) - f (a n) := by
  have hcell (j : ℕ) (hj : j < n) :
      f (sample j) - N * (∫ w in a j..a (j+1), f w ∂μ) ≤
        f (a j) - f (a (j+1)) := by
    have hl := intervalIntegral.integral_mono_on (ha j hj) intervalIntegrable_const
      (hfi j hj) (fun w hw => hf hw.2)
    have hl' := mul_le_mul_of_nonneg_left hl hN.le
    rw [scaled_integral_const_of_cell_mass μ hN.ne' (ha j hj) (hmass j hj)] at hl'
    have hu := hf (hsample j hj).1
    linarith
  have hsum : (∑ j ∈ Finset.range n, f (sample j)) -
      N * (∫ w in a 0..a n, f w ∂μ) ≤ f (a 0) - f (a n) := calc
    _ = ∑ j ∈ Finset.range n,
        (f (sample j) - N * (∫ w in a j..a (j+1), f w ∂μ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        intervalIntegral.sum_integral_adjacent_intervals hfi]
    _ ≤ ∑ j ∈ Finset.range n, (f (a j) - f (a (j+1))) :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _ = f (a 0) - f (a n) := Finset.sum_range_sub' (fun j => f (a j)) n
  linarith

noncomputable def truncatedLog (δ v w : ℝ) : ℝ := Real.log (max δ |v-w|)

lemma truncatedLog_continuous {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    Continuous (truncatedLog δ v) := by
  unfold truncatedLog
  exact (continuous_const.max ((continuous_const.sub continuous_id).abs)).log
    (fun w => ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _)))

lemma truncatedLog_split {δ : ℝ} (hδ : 0 < δ) (v w : ℝ) :
    truncatedLog δ v w = Real.log (max δ (v-w)) +
      Real.log (max δ (w-v)) - Real.log δ := by
  rcases le_total w v with h | h
  · rw [truncatedLog, abs_of_nonneg (sub_nonneg.mpr h)]
    rw [max_eq_left (show w-v ≤ δ by linarith)]
    ring
  · rw [truncatedLog, abs_of_nonpos (sub_nonpos.mpr h)]
    rw [max_eq_left (show v-w ≤ δ by linarith)]
    rw [neg_sub]
    ring

lemma truncatedLog_left_antitone {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    Antitone (fun w : ℝ => Real.log (max δ (v-w))) := by
  intro x y hxy
  exact Real.log_le_log (lt_of_lt_of_le hδ (le_max_left _ _))
    (max_le_max le_rfl (sub_le_sub_left hxy v))

lemma truncatedLog_right_monotone {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    Monotone (fun w : ℝ => Real.log (max δ (w-v))) := by
  intro x y hxy
  exact Real.log_le_log (lt_of_lt_of_le hδ (le_max_left _ _))
    (max_le_max le_rfl (sub_le_sub_right hxy v))

lemma scaled_integral_const_equalMass (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N : ℝ} (hN : N ≠ 0) (n : ℕ) (a : ℕ → ℝ) (c : ℝ)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1 / N) :
    N * (∫ _ in a 0..a n, c ∂μ) = (n : ℝ) * c := by
  calc
    _ = ∑ j ∈ Finset.range n, N * (∫ _ in a j..a (j+1), c ∂μ) := by
      rw [← Finset.mul_sum,
        intervalIntegral.sum_integral_adjacent_intervals (fun _ _ => intervalIntegrable_const)]
    _ = ∑ _j ∈ Finset.range n, c := Finset.sum_congr rfl (fun j hj =>
      scaled_integral_const_of_cell_mass μ hN (ha j (Finset.mem_range.mp hj))
        (hmass j (Finset.mem_range.mp hj)))
    _ = (n : ℝ) * c := by simp

lemma log_max_shift_le {δ B x : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    Real.log (max δ (x+B)) - Real.log (max δ x) ≤ Real.log (1+B/δ) := by
  have hd : 0 < max δ x := lt_of_lt_of_le hδ (le_max_left _ _)
  have hc : 0 < 1+B/δ := by positivity
  have hmul : B ≤ (B/δ) * max δ x := by
    have hh := mul_le_mul_of_nonneg_left (le_max_left δ x) (div_nonneg hB hδ.le)
    rwa [div_mul_cancel₀ _ hδ.ne'] at hh
  have hmax : max δ (x+B) ≤ (1+B/δ) * max δ x := by
    refine max_le ?_ ?_
    · have hh := le_max_left δ x
      nlinarith
    · have hh := le_max_right δ x
      nlinarith
  have hl := Real.log_le_log (lt_of_lt_of_le hδ (le_max_left δ (x+B))) hmax
  rw [Real.log_mul hc.ne' hd.ne'] at hl
  linarith

/-- Uniform bounded-variation quadrature for the truncated logarithm.  This
holds for every center `v : ℝ`, including centers on cell boundaries, and puts
no lower or upper bound on cell lengths. -/
theorem truncatedLog_equalMass_quadrature (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N δ B : ℝ} (hN : 0 < N) (hδ : 0 < δ) (hB : 0 ≤ B)
    (n : ℕ) (a sample : ℕ → ℝ) (v : ℝ)
    (ha0 : a 0 = 0) (han : a n = B)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1 / N) :
    (∑ j ∈ Finset.range n, truncatedLog δ v (sample j)) ≤
      N * (∫ w in 0..B, truncatedLog δ v w ∂μ) + 2 * Real.log (1+B/δ) := by
  let f : ℝ → ℝ := fun w => Real.log (max δ (v-w))
  let g : ℝ → ℝ := fun w => Real.log (max δ (w-v))
  have hfcont : Continuous f :=
    (continuous_const.max (continuous_const.sub continuous_id)).log
      (fun w => ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _)))
  have hgcont : Continuous g :=
    (continuous_const.max (continuous_id.sub continuous_const)).log
      (fun w => ne_of_gt (lt_of_lt_of_le hδ (le_max_left _ _)))
  have hf := antitone_equalMass_quadrature μ hN n a sample f
    (truncatedLog_left_antitone hδ v) (fun _ _ => hfcont.intervalIntegrable _ _)
    ha hsample hmass
  have hg := monotone_equalMass_quadrature μ hN n a sample g
    (truncatedLog_right_monotone hδ v) (fun _ _ => hgcont.intervalIntegrable _ _)
    ha hsample hmass
  have hc := scaled_integral_const_equalMass μ hN.ne' n a (Real.log δ) ha hmass
  have hsplit : (∫ w in a 0..a n, truncatedLog δ v w ∂μ) =
      (∫ w in a 0..a n, f w ∂μ) + (∫ w in a 0..a n, g w ∂μ) -
        (∫ _ in a 0..a n, Real.log δ ∂μ) := by
    simp_rw [truncatedLog_split hδ]
    rw [intervalIntegral.integral_sub
      ((hfcont.intervalIntegrable _ _).add (hgcont.intervalIntegrable _ _))
      intervalIntegrable_const,
      intervalIntegral.integral_add (hfcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)]
  have hsum : (∑ j ∈ Finset.range n, truncatedLog δ v (sample j)) =
      (∑ j ∈ Finset.range n, f (sample j)) +
      (∑ j ∈ Finset.range n, g (sample j)) - (n : ℝ) * Real.log δ := by
    simp_rw [truncatedLog_split hδ]
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, f, g]
  have hfv : f (a 0) - f (a n) ≤ Real.log (1+B/δ) := by
    simpa [f, ha0, han] using (log_max_shift_le (x := v-B) hδ hB)
  have hgv : g (a n) - g (a 0) ≤ Real.log (1+B/δ) := by
    simpa [g, ha0, han, sub_eq_add_neg, add_comm] using
      (log_max_shift_le (x := -v) hδ hB)
  rw [hsum]
  rw [ha0, han] at hsplit hf hg hc hfv hgv
  have hscaled := congrArg (fun z : ℝ => N * z) hsplit
  nlinarith

end Zeta5.Analysis
