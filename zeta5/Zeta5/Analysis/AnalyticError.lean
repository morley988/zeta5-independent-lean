import Zeta5.Endpoint.ConcreteCriterion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The explicit analytic remainder is negligible at quadratic scale

The determinant's extra `r!` from Leibniz, the polynomial trial prefactors,
and the endpoint error in the exact profile grid bound are all `o(N²)`.
Only the elementary inequality `r! ≤ r^r` is needed for this remainder.
-/

open Filter
open scoped Topology

namespace Zeta5.Analysis

noncomputable def analyticError (C d : ℝ) (n : ℕ) : ℝ :=
  Real.log (Nat.factorial (24*n) : ℝ)+(24*(n : ℝ))*
    (C+22*Real.log (20*(n : ℝ))+Real.log (20*(n : ℝ)+1)+2)+(20*(n : ℝ))*d

lemma log_factorial_nonneg (n : ℕ) : 0 ≤ Real.log (Nat.factorial n : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.factorial_pos n

lemma log_factorial_le_mul_log (n : ℕ) :
    Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ)*Real.log (n : ℝ) := by
  have hpow : (Nat.factorial n : ℝ) ≤ (n : ℝ)^n := by
    exact_mod_cast Nat.factorial_le_pow n
  have h := Real.log_le_log (by positivity : (0 : ℝ) < Nat.factorial n) hpow
  simpa only [Real.log_pow] using h

lemma tendsto_log_mul_nat_div_nat (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (a*(n : ℝ))/(n : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => a*(n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp ht
  have hm := hlog.const_mul a
  simp only [pow_one, one_mul, add_zero, mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  field_simp

lemma tendsto_log_mul_nat_add_one_div_nat (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log (a*(n : ℝ)+1)/(n : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => a*(n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)).comp ht
  have hm := hlog.const_mul a
  simp only [pow_one, one_mul, mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Function.comp_apply]
  field_simp
  ring

lemma factorial_over_windowScale_limit :
    Tendsto (fun n : ℕ => Real.log (Nat.factorial (24*n) : ℝ)/Zeta5.Endpoint.windowScale n)
      atTop (𝓝 0) := by
  have hu := (tendsto_log_mul_nat_div_nat 24 (by norm_num)).const_mul (24/400 : ℝ)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    exact div_nonneg (log_factorial_nonneg _) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have h := div_le_div_of_nonneg_right (log_factorial_le_mul_log (24*n))
      (sq_nonneg (20*(n : ℝ)))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    convert! h using 1
    field_simp
    ring

/-- The explicit remainder used by the actual determinant estimate is
negligible on the manuscript's quadratic scale. -/
theorem analyticError_over_windowScale_limit (C d : ℝ) :
    Tendsto (fun n : ℕ => analyticError C d n/Zeta5.Endpoint.windowScale n)
      atTop (𝓝 0) := by
  have hc := Zeta5.Endpoint.linear_over_windowScale_limit (24*(C+2)+20*d)
  have hl := (tendsto_log_mul_nat_div_nat 20 (by norm_num)).const_mul (528/400 : ℝ)
  have hl1 := (tendsto_log_mul_nat_add_one_div_nat 20 (by norm_num)).const_mul (24/400 : ℝ)
  have h := ((factorial_over_windowScale_limit.add hc).add hl).add hl1
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold analyticError Zeta5.Endpoint.windowScale
  field_simp
  ring

end Zeta5.Analysis
