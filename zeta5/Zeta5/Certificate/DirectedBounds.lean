import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sound directed enclosures used by the exact comparison

These results justify individual square-root enclosures and finite logarithm
lower bounds. The finite grid and its relation to the potential integral are
separate obligations.
-/

namespace Zeta5.Certificate

open Finset

theorem sqrt_interval_of_squared_bounds {x lower upper : ℝ}
    (hl : 0 ≤ lower) (hu : 0 ≤ upper)
    (hlo : lower ^ 2 ≤ x) (hhi : x ≤ upper ^ 2) :
    lower ≤ Real.sqrt x ∧ Real.sqrt x ≤ upper := by
  have hx : 0 ≤ x := (sq_nonneg lower).trans hlo
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith

noncomputable def logSeriesLower (terms : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ j ∈ range terms, ((x - 1) / (x + 1)) ^ (2 * j + 1) / (2 * j + 1)

theorem logSeriesLower_le_log {x : ℝ} (hx : 1 ≤ x) (terms : ℕ) :
    logSeriesLower terms x ≤ Real.log x := by
  have hd : 0 < x + 1 := by linarith
  have hz0 : 0 ≤ (x - 1) / (x + 1) := div_nonneg (by linarith) hd.le
  have hz1 : (x - 1) / (x + 1) < 1 := (div_lt_one hd).2 (by linarith)
  have hid : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    have hden : 1 - (x - 1) / (x + 1) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    <;> ring
  have h := Real.sum_range_le_log_div hz0 hz1 terms
  rw [hid] at h
  dsimp [logSeriesLower]
  linarith

/-- Multiplication rounded downward on a nonnegative fixed-point grid. -/
def roundedMul (scale a b : ℕ) : ℕ := a * b / scale

theorem roundedMul_le (scale a b : ℕ) (hscale : 0 < scale) :
    (roundedMul scale a b : ℝ) / scale ≤ (a : ℝ) / scale * ((b : ℝ) / scale) := by
  have h : ((a * b / scale : ℕ) : ℝ) ≤ (a : ℝ) * b / scale := by
    simpa only [Nat.cast_mul] using (Nat.cast_div_le (m := a * b) (n := scale) :
      ((a * b / scale : ℕ) : ℝ) ≤ (a * b : ℕ) / (scale : ℝ))
  have hm : (0 : ℝ) < scale := by exact_mod_cast hscale
  dsimp [roundedMul]
  calc
    ((a * b / scale : ℕ) : ℝ) / scale ≤ ((a : ℝ) * b / scale) / scale :=
      div_le_div_of_nonneg_right h hm.le
    _ = (a : ℝ) / scale * ((b : ℝ) / scale) := by ring

/-- The rounded odd-power recurrence used in the manuscript program. -/
def roundedOddPower (scale z : ℕ) : ℕ → ℕ
  | 0 => z
  | j + 1 => roundedMul scale (roundedOddPower scale z j) (roundedMul scale z z)

theorem roundedOddPower_le (scale z : ℕ) (hscale : 0 < scale)
    {x : ℝ} (hx : 0 ≤ x) (hz : (z : ℝ) / scale ≤ x) (j : ℕ) :
    (roundedOddPower scale z j : ℝ) / scale ≤ x ^ (2 * j + 1) := by
  have hz0 : (0 : ℝ) ≤ (z : ℝ) / scale := by positivity
  have hzz : (roundedMul scale z z : ℝ) / scale ≤ x ^ 2 := by
    calc
      (roundedMul scale z z : ℝ) / scale ≤ (z : ℝ) / scale * ((z : ℝ) / scale) :=
        roundedMul_le scale z z hscale
      _ ≤ x * x := mul_le_mul hz hz hz0 hx
      _ = x ^ 2 := by ring
  induction j with
  | zero => simpa [roundedOddPower] using hz
  | succ j ih =>
    calc
      (roundedOddPower scale z (j + 1) : ℝ) / scale
          ≤ ((roundedOddPower scale z j : ℝ) / scale) *
              ((roundedMul scale z z : ℝ) / scale) :=
        roundedMul_le scale _ _ hscale
      _ ≤ x ^ (2 * j + 1) * x ^ 2 :=
        mul_le_mul ih hzz (by positivity) (pow_nonneg hx _)
      _ = x ^ (2 * (j + 1) + 1) := by
        rw [← pow_add]
        congr 1

def roundedLogNumerator (scale z terms : ℕ) : ℕ :=
  ∑ j ∈ range terms, 2 * roundedOddPower scale z j / (2 * j + 1)

theorem roundedLogNumerator_le_series (scale z terms : ℕ) (hscale : 0 < scale)
    {x : ℝ} (hx : 0 ≤ x) (hz : (z : ℝ) / scale ≤ x) :
    (roundedLogNumerator scale z terms : ℝ) / scale ≤
      2 * ∑ j ∈ range terms, x ^ (2 * j + 1) / (2 * j + 1) := by
  have hm : (0 : ℝ) < scale := by exact_mod_cast hscale
  dsimp [roundedLogNumerator]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hd : (0 : ℝ) < 2 * j + 1 := by positivity
  calc
    ((2 * roundedOddPower scale z j / (2 * j + 1) : ℕ) : ℝ) / scale
        ≤ ((2 : ℝ) * roundedOddPower scale z j / (2 * j + 1)) / scale := by
      apply div_le_div_of_nonneg_right _ hm.le
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
        (Nat.cast_div_le (m := 2 * roundedOddPower scale z j) (n := 2 * j + 1) :
        ((2 * roundedOddPower scale z j / (2 * j + 1) : ℕ) : ℝ) ≤
          (2 * roundedOddPower scale z j : ℕ) / ((2 * j + 1 : ℕ) : ℝ))
    _ = 2 * ((roundedOddPower scale z j : ℝ) / scale) / (2 * j + 1) := by ring
    _ ≤ 2 * x ^ (2 * j + 1) / (2 * j + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (roundedOddPower_le scale z hscale hx hz j) (by norm_num)) hd.le
    _ = 2 * (x ^ (2 * j + 1) / (2 * j + 1)) := by ring

/-- Any certified downward rounding of `(x-1)/(x+1)` produces a sound
logarithm lower bound after the rounded recurrence. -/
theorem roundedLogNumerator_le_log (scale z terms : ℕ) (hscale : 0 < scale)
    {x : ℝ} (hx : 1 ≤ x) (hz : (z : ℝ) / scale ≤ (x - 1) / (x + 1)) :
    (roundedLogNumerator scale z terms : ℝ) / scale ≤ Real.log x := by
  apply le_trans (roundedLogNumerator_le_series scale z terms hscale
    (div_nonneg (by linarith) (by linarith)) hz)
  exact logSeriesLower_le_log hx terms

end Zeta5.Certificate
