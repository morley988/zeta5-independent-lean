import Zeta5.Arithmetic.SmallPrimeSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The full small-prime contribution is negligible at quadratic scale

The natural cutoff is bounded by a fixed multiple of the real square root.
The remaining estimate reduces to the proved limit `log x / sqrt x → 0`.
-/

open Filter
open scoped Topology

namespace Zeta5.Analysis

lemma smallPrimeCutoff_le_real_sqrt {n : ℕ} (hn : 0 < n) :
    (Zeta5.Arithmetic.smallPrimeCutoff n : ℝ) ≤ 200*Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hsq : (Nat.sqrt n : ℝ)^2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hroot := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hkn : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  unfold Zeta5.Arithmetic.smallPrimeCutoff
  push_cast
  nlinarith

lemma tendsto_log_nat_div_sqrt :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  convert! h.comp hcast using 1
  ext n
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

lemma tendsto_inv_sqrt_nat :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma smallPrimeError_nonneg (n : ℕ) : 0 ≤ Zeta5.Arithmetic.smallPrimeError n := by
  unfold Zeta5.Arithmetic.smallPrimeError
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (Real.log_nonneg
      (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  · exact Real.log_nonneg (by norm_num)

lemma smallPrimeError_over_scale_le {n : ℕ} (hn : 0 < n) :
    Zeta5.Arithmetic.smallPrimeError n/Zeta5.Endpoint.windowScale n ≤
      12*(9*(Real.log 104+Real.log (n : ℝ))+Real.log 96)/Real.sqrt (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hlog : Real.log (100*(n : ℝ)+4) ≤ Real.log 104+Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < 100*(n : ℝ)+4)
      (show 100*(n : ℝ)+4 ≤ 104*(n : ℝ) by linarith)
    rwa [Real.log_mul (by norm_num : (104 : ℝ) ≠ 0) hnpos.ne'] at h
  have hB : 0 ≤ 9*Real.log (100*(n : ℝ)+4)+Real.log 96 := by
    exact add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
      (Real.log_nonneg (by norm_num))
  have hB' : 0 ≤ 9*(Real.log 104+Real.log (n : ℝ))+Real.log 96 := by
    linarith
  have h := mul_le_mul
    (mul_le_mul_of_nonneg_left (smallPrimeCutoff_le_real_sqrt hn)
      (show 0 ≤ 24*(n : ℝ) by positivity))
    (show 9*Real.log (100*(n : ℝ)+4)+Real.log 96 ≤
      9*(Real.log 104+Real.log (n : ℝ))+Real.log 96 by linarith) hB (by positivity)
  have hd := div_le_div_of_nonneg_right h (sq_nonneg (20*(n : ℝ)))
  change Zeta5.Arithmetic.smallPrimeError n/Zeta5.Endpoint.windowScale n ≤ _ at hd
  apply hd.trans_eq
  have hs := Real.sq_sqrt hnpos.le
  field_simp
  nlinarith [hs]

theorem smallPrimeError_over_windowScale_limit :
    Tendsto (fun n : ℕ => Zeta5.Arithmetic.smallPrimeError n/Zeta5.Endpoint.windowScale n)
      atTop (𝓝 0) := by
  have hlog := tendsto_log_nat_div_sqrt.const_mul (108 : ℝ)
  have hc := tendsto_inv_sqrt_nat.const_mul (12*(9*Real.log 104+Real.log 96))
  have hupper := hlog.add hc
  simp only [mul_zero, add_zero] at hupper
  have hupper' : Tendsto (fun n : ℕ =>
      12*(9*(Real.log 104+Real.log (n : ℝ))+Real.log 96)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    convert! hupper using 1
    ext n
    ring
  apply squeeze_zero' _ _ hupper'
  · filter_upwards [] with n
    exact div_nonneg (smallPrimeError_nonneg n) (sq_nonneg _)
  · exact (eventually_gt_atTop (0 : ℕ)).mono (fun _ hn => smallPrimeError_over_scale_le hn)

end Zeta5.Analysis
