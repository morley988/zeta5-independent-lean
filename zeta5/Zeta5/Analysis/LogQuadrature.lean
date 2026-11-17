import Zeta5.Analysis.LogTruncation
import Zeta5.Analysis.QuantileQuadrature

/-!
# Uniform logarithmic quadrature

Combining the small-ball estimate with truncated-log quadrature gives a uniform
`O(log N)` error.  Unlike a direct treatment of singular cells, this argument
needs no lower bound on the cell lengths.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace Zeta5.Analysis

lemma truncatedLog_le_log_add_loss (δ v w : ℝ) :
    truncatedLog δ v w ≤ Real.log |v-w| + logTruncationLoss δ v w := by
  by_cases h : δ ≤ |v-w|
  · rw [truncatedLog, max_eq_right h]
    exact le_add_of_nonneg_right (logTruncationLoss_nonneg _ _ _)
  · rw [truncatedLog, max_eq_left (le_of_not_ge h)]
    have hh := le_max_right 0 (Real.log δ - Real.log |v-w|)
    dsimp [logTruncationLoss]
    linarith

lemma abs_log_le_truncatedLog_add_loss {δ : ℝ} (hδ : 0 < δ) (v w : ℝ) :
    |Real.log (|v-w|)| ≤ |truncatedLog δ v w| + logTruncationLoss δ v w := by
  by_cases hd : |v-w| = 0
  · simp only [hd, Real.log_zero, abs_zero]
    exact add_nonneg (abs_nonneg _) (logTruncationLoss_nonneg _ _ _)
  have hdpos : 0 < |v-w| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
  by_cases h : δ ≤ |v-w|
  · rw [truncatedLog, max_eq_right h]
    exact le_add_of_nonneg_right (logTruncationLoss_nonneg _ _ _)
  · have hlog : Real.log |v-w| ≤ Real.log δ :=
      Real.log_le_log hdpos (le_of_not_ge h)
    rw [truncatedLog, max_eq_left (le_of_not_ge h)]
    rw [logTruncationLoss, max_eq_right (sub_nonneg.mpr hlog)]
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le (Real.log δ)
      linarith
    · have hh := le_abs_self (Real.log δ)
      linarith

/-- Integrability of the actual logarithmic kernel, together with a bound on
the integral change when it is truncated. -/
theorem log_integrableOn_and_truncated_integral_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] {C ε B v : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hB : 0 ≤ B)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    IntegrableOn (fun w => Real.log |v-w|) (Ioc 0 B) μ ∧
      (∫ w in 0..B, truncatedLog (ε^4) v w ∂μ) ≤
        (∫ w in 0..B, Real.log |v-w| ∂μ) + 4*C*ε := by
  have hsmall' : ∀ ρ : ℝ, 0 < ρ →
      (μ.restrict (Ioc 0 B)) {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ) := by
    intro ρ hρ
    exact (Measure.restrict_apply_le _ _).trans (hsmall ρ hρ)
  obtain ⟨hloss, hbound⟩ := logTruncationLoss_integrable_and_integral_le
    (μ.restrict (Ioc 0 B)) hC hε hsmall'
  have ht : IntegrableOn (truncatedLog (ε^4) v) (Ioc 0 B) μ :=
    ((truncatedLog_continuous (pow_pos hε _) v).intervalIntegrable 0 B).1
  have hmeas : Measurable (fun w : ℝ => Real.log |v-w|) := by fun_prop
  have hlog : IntegrableOn (fun w => Real.log |v-w|) (Ioc 0 B) μ := by
    exact (ht.abs.add hloss).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall (fun w => by
        simpa only [Real.norm_eq_abs, Pi.add_apply] using
          abs_log_le_truncatedLog_add_loss (pow_pos hε _) v w))
  refine ⟨hlog, ?_⟩
  rw [intervalIntegral.integral_of_le hB, intervalIntegral.integral_of_le hB]
  have hm := integral_mono ht (hlog.add hloss)
    (truncatedLog_le_log_add_loss (ε^4) v)
  dsimp only [Pi.add_apply] at hm
  rw [integral_add hlog hloss] at hm
  linarith

/-- Uniform logarithmic quadrature with an explicit truncation parameter.
The noncollision hypothesis is necessary because `Real.log 0 = 0`; the final
polynomial estimate handles collisions separately by the vanishing product. -/
theorem log_equalMass_quadrature (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N C ε B v : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (hε : 0 < ε) (hB : 0 ≤ B)
    (n : ℕ) (a sample : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = B)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1/N)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ))
    (hne : ∀ j < n, v ≠ sample j) :
    (∑ j ∈ Finset.range n, Real.log |v-sample j|) ≤
      N * (∫ w in 0..B, Real.log |v-w| ∂μ) +
        N*(4*C*ε) + 2*Real.log (1+B/(ε^4)) := by
  have hpoint : (∑ j ∈ Finset.range n, Real.log |v-sample j|) ≤
      ∑ j ∈ Finset.range n, truncatedLog (ε^4) v (sample j) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Real.log_le_log
    · exact abs_pos.mpr (sub_ne_zero.mpr (hne j (Finset.mem_range.mp hj)))
    · exact le_max_right _ _
  have hquad := truncatedLog_equalMass_quadrature μ hN (pow_pos hε 4) hB n a sample v
    ha0 han ha hsample hmass
  have hint := (log_integrableOn_and_truncated_integral_le μ hC hε hB hsmall).2
  have hmul := mul_le_mul_of_nonneg_left hint hN.le
  linarith

lemma log_quadrature_error_le {N B : ℝ} (hN : 1 ≤ N) (hB : 0 ≤ B) :
    2*Real.log (1+B/(N⁻¹)^4) ≤ 8*Real.log N + 2*Real.log (1+B) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hN4 : 1 ≤ N^4 := one_le_pow₀ hN
  have harg : 1+B/(N⁻¹)^4 ≤ (1+B)*N^4 := by
    rw [inv_pow, div_inv_eq_mul]
    nlinarith
  have hl := Real.log_le_log (show 0 < 1+B/(N⁻¹)^4 by positivity) harg
  rw [Real.log_mul (show 1+B ≠ 0 by positivity) (pow_ne_zero _ hNpos.ne'),
    Real.log_pow] at hl
  norm_num at hl
  simp only [inv_pow, div_inv_eq_mul]
  linarith

/-- The explicit `O(log N)` estimate used for the trial polynomial.  Its
constant is uniform in the logarithm's center. -/
theorem log_equalMass_quadrature_log_error (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N C B v : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (n : ℕ) (a sample : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = B)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1/N)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ))
    (hne : ∀ j < n, v ≠ sample j) :
    (∑ j ∈ Finset.range n, Real.log |v-sample j|) ≤
      N * (∫ w in 0..B, Real.log |v-w| ∂μ) +
        8*Real.log N + 2*Real.log (1+B) + 4*C := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hq := log_equalMass_quadrature μ hNpos hC (inv_pos.mpr hNpos) hB n a sample
    ha0 han ha hsample hmass hsmall hne
  have he := log_quadrature_error_le hN hB
  have hc : N*(4*C*N⁻¹) = 4*C := by field_simp
  rw [hc] at hq
  linarith

end Zeta5.Analysis
