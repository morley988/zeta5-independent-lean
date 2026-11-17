import Zeta5.Certificate.ArithmeticCells
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exact real affine profile on every certified arithmetic cell

The cell tests imply identities throughout each open interval, not only at
its midpoint. Endpoint exceptions are harmless for subsequent integration.
This file concerns the explicitly defined rank profile; bounding the actual
determinant valuation by that profile is a separate mathematical step.
-/

namespace Zeta5.Certificate

noncomputable def profileEpsilon (β : ℝ) : ℝ :=
  if β ≤ 2 * (1 - (⌊1 / β⌋ : ℤ) * β) then 1 else 0

noncomputable def middleRankProfile (β : ℝ) : ℝ :=
  (4 + profileEpsilon β) * (6 / 5) +
    min (6 / 5) (((⌊(5 / 2) / β⌋ : ℤ) + 1) *
      (1 - ((⌊1 / β⌋ : ℤ) + profileEpsilon β / 2) * β))

namespace ArithmeticCell

theorem lo_real_pos {c : ArithmeticCell} (h : c.Valid) : 0 < (c.lo : ℝ) := by
  exact_mod_cast h.1

theorem floor_inverse {c : ArithmeticCell} (h : c.Valid) {β : ℝ}
    (hβl : (c.lo : ℝ) < β) (hβr : β < (c.hi : ℝ)) :
    ⌊1 / β⌋ = (c.q : ℤ) := by
  have hβ : 0 < β := (lo_real_pos h).trans hβl
  have hqhi : (c.q : ℝ) * (c.hi : ℝ) ≤ 1 := by exact_mod_cast h.2.2.1
  have hqlo : 1 ≤ ((c.q : ℝ) + 1) * (c.lo : ℝ) := by exact_mod_cast h.2.2.2.1
  apply Int.floor_eq_iff.mpr
  constructor
  · simp only [Int.cast_natCast]
    apply (le_div_iff₀ hβ).2
    exact (mul_le_mul_of_nonneg_left hβr.le (Nat.cast_nonneg _)).trans hqhi
  · simp only [Int.cast_natCast]
    apply (div_lt_iff₀ hβ).2
    exact hqlo.trans_lt (mul_lt_mul_of_pos_left hβl (by positivity))

theorem floor_degree {c : ArithmeticCell} (h : c.Valid) {β : ℝ}
    (hβl : (c.lo : ℝ) < β) (hβr : β < (c.hi : ℝ)) :
    ⌊(5 / 2) / β⌋ = (c.degree : ℤ) := by
  have hβ : 0 < β := (lo_real_pos h).trans hβl
  have hdhi : (c.degree : ℝ) * (c.hi : ℝ) ≤ 5 / 2 := by
    have hr : (c.degree : ℝ) * (c.hi : ℝ) ≤ 2 * (rho : ℝ) := by exact_mod_cast h.2.2.2.2.2.1
    norm_num [rho] at hr ⊢
    exact hr
  have hdlo : 5 / 2 ≤ ((c.degree : ℝ) + 1) * (c.lo : ℝ) := by
    have hr : 2 * (rho : ℝ) ≤ ((c.degree : ℝ) + 1) * (c.lo : ℝ) := by
      exact_mod_cast h.2.2.2.2.2.2.1
    norm_num [rho] at hr ⊢
    exact hr
  apply Int.floor_eq_iff.mpr
  constructor
  · simp only [Int.cast_natCast]
    apply (le_div_iff₀ hβ).2
    exact (mul_le_mul_of_nonneg_left hβr.le (Nat.cast_nonneg _)).trans hdhi
  · simp only [Int.cast_natCast]
    apply (div_lt_iff₀ hβ).2
    exact hdlo.trans_lt (mul_lt_mul_of_pos_left hβl (by positivity))

theorem epsilon_eq {c : ArithmeticCell} (h : c.Valid) {β : ℝ}
    (hβl : (c.lo : ℝ) < β) (hβr : β < (c.hi : ℝ)) :
    profileEpsilon β = (c.eps : ℝ) := by
  unfold profileEpsilon
  rw [floor_inverse h hβl hβr]
  simp only [Int.cast_natCast]
  cases he : c.epsilon with
  | false =>
    have hε : (2 : ℝ) ≤ (2 * (c.q : ℝ) + 1) * (c.lo : ℝ) := by
      have hr : (2 : ℚ) ≤ (2 * (c.q : ℚ) + 1) * c.lo := by
        simpa [he] using h.2.2.2.2.1
      exact_mod_cast hr
    have hs : (2 : ℝ) < (2 * (c.q : ℝ) + 1) * β :=
      hε.trans_lt (mul_lt_mul_of_pos_left hβl (by positivity))
    have hnot : ¬ β ≤ 2 * (1 - (c.q : ℝ) * β) := by nlinarith
    simp [hnot, eps, he]
  | true =>
    have hε : (2 * (c.q : ℝ) + 1) * (c.hi : ℝ) ≤ 2 := by
      have hr : (2 * (c.q : ℚ) + 1) * c.hi ≤ 2 := by
        simpa [he] using h.2.2.2.2.1
      exact_mod_cast hr
    have hs : (2 * (c.q : ℝ) + 1) * β < 2 :=
      (mul_lt_mul_of_pos_left hβr (by positivity)).trans_le hε
    have hyes : β ≤ 2 * (1 - (c.q : ℝ) * β) := by nlinarith
    simp [hyes, eps, he]

theorem widthSlope_real_nonneg (c : ArithmeticCell) : 0 ≤ (c.widthSlope : ℝ) := by
  cases he : c.epsilon <;> simp [widthSlope, eps, he] <;> positivity

theorem profile_affine {c : ArithmeticCell} (h : c.Valid) {β : ℝ}
    (hβl : (c.lo : ℝ) < β) (hβr : β < (c.hi : ℝ)) :
    middleRankProfile β = (c.intercept : ℝ) + (c.slope : ℝ) * β := by
  have hd : (delta : ℝ) = 6 / 5 := by norm_num [delta, rho, s]
  have hw : (c.widthSlope : ℝ) = (c.q : ℝ) + (c.eps : ℝ) / 2 := by
    simp [widthSlope]
  have hw0 := widthSlope_real_nonneg c
  have hc0 : (0 : ℝ) ≤ c.degree + 1 := by positivity
  unfold middleRankProfile
  rw [epsilon_eq h hβl hβr, floor_degree h hβl hβr, floor_inverse h hβl hβr]
  simp only [Int.cast_natCast]
  rw [← hw]
  cases hs : c.saturated with
  | false =>
    have hclip : ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * (c.lo : ℝ)) ≤ 6 / 5 := by
      have hr : ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * (c.lo : ℝ)) ≤ (delta : ℝ) := by
        have hq : (c.degree + 1 : ℚ) * (1 - c.widthSlope * c.lo) ≤ delta := by
          simpa [hs] using h.2.2.2.2.2.2.2
        exact_mod_cast hq
      simpa only [hd] using hr
    have hβ : ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * β) ≤ 6 / 5 := by
      apply le_trans _ hclip
      apply mul_le_mul_of_nonneg_left _ hc0
      have hh := mul_le_mul_of_nonneg_left hβl.le hw0
      linarith
    rw [min_eq_right hβ]
    simp [intercept, slope, hs, hd, widthSlope]
    ring
  | true =>
    have hclip : 6 / 5 ≤ ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * (c.hi : ℝ)) := by
      have hr : (delta : ℝ) ≤ ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * (c.hi : ℝ)) := by
        have hq : delta ≤ (c.degree + 1 : ℚ) * (1 - c.widthSlope * c.hi) := by
          simpa [hs] using h.2.2.2.2.2.2.2
        exact_mod_cast hq
      simpa only [hd] using hr
    have hβ : 6 / 5 ≤ ((c.degree : ℝ) + 1) * (1 - (c.widthSlope : ℝ) * β) := by
      apply le_trans hclip
      apply mul_le_mul_of_nonneg_left _ hc0
      have hh := mul_le_mul_of_nonneg_left hβr.le hw0
      linarith
    rw [min_eq_left hβ]
    simp [intercept, slope, hs, hd]
    ring

end ArithmeticCell

end Zeta5.Certificate
