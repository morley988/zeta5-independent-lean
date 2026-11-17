import Zeta5.Endpoint.ZetaBridge
import Zeta5.Construction.Determinant
import Mathlib.Analysis.PSeries

/-! # The ordinary zeta tail at positive integers -/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Polynomial Real
open scoped BigOperators

def hurwitzFive (y : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + y) ^ 5

theorem hurwitzFive_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + y) ^ 5) := by
  have h := (Real.summable_one_div_nat_add_rpow y 5).mpr (by norm_num)
  apply h.congr
  intro n
  rw [abs_of_pos (by positivity : 0 < (n : ℝ) + y)]
  norm_cast

theorem hurwitzFive_shift {y : ℝ} (hy : 0 < y) :
    hurwitzFive y = 1 / y ^ 5 + ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + y) ^ 5 := by
  simpa only [hurwitzFive, Nat.cast_zero, zero_add] using (hurwitzFive_summable hy).tsum_eq_zero_add

theorem harmonicFive_real_range (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), 1 / (k : ℝ) ^ 5) =
      (Zeta5.Construction.harmonicFive m : ℝ) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by decide : 5 ≠ 0), div_zero, add_zero,
    Zeta5.Construction.harmonicFive, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast]

theorem hurwitzFive_nat {i : ℕ} (hi : 0 < i) :
    hurwitzFive (i : ℝ) = Zeta5.Endpoint.realZeta 5 -
      (Zeta5.Construction.harmonicFive (i - 1) : ℝ) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have ht := hs.sum_add_tsum_nat_add i
  have hm : (∑ k ∈ Finset.range i, 1 / (k : ℝ) ^ 5) =
      (Zeta5.Construction.harmonicFive (i - 1) : ℝ) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using harmonicFive_real_range (i - 1)
  rw [hm] at ht
  simp only [Nat.cast_add] at ht
  change _ + hurwitzFive (i : ℝ) = Zeta5.Endpoint.realZeta 5 at ht
  linarith

end Zeta5.Analysis.PhysicalMeasure
