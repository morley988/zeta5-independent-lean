import Zeta5.Arithmetic.FactorialFloorSum
import Zeta5.Arithmetic.LargePrimes
import Zeta5.Certificate.UpperArithmetic

/-! Exact finite-size comparison with the seven upper-band affine rows. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Zeta5.Certificate

def upperCharge (n p : ℕ) : ℤ :=
  factorialCharge (20 * n) n (24 * n) p + 7 * (upperHighCount (20 * n) p : ℤ) -
    2 * (upperAffectedCount (20 * n) n p : ℤ) +
    ((min (terminalSize (20 * n) n (25 * n) p)
      (24 * n - upperHighCount (20 * n) p) : ℕ) : ℤ)

theorem upperCharge_le_of_bounds (n p : ℕ) (hpN : p ≤ 20 * n) (f a t : ℝ)
    (hf : (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤ f)
    (ha : a ≤ (upperAffectedCount (20 * n) n p : ℝ))
    (ht : (terminalSize (20 * n) n (25 * n) p : ℝ) ≤ t) :
    (upperCharge n p : ℝ) ≤ f + 7 * (20 * (n : ℝ) - p) - 2 * a + t := by
  have hH : (upperHighCount (20 * n) p : ℝ) ≤ 20 * (n : ℝ) - p := by
    have h : upperHighCount (20 * n) p ≤ 20 * n - p := Nat.sub_le _ _
    have hc : ((20 * n - p : ℕ) : ℝ) = 20 * (n : ℝ) - p := by
      rw [Nat.cast_sub hpN]; norm_num
    rw [← hc]
    exact_mod_cast h
  have hm : ((min (terminalSize (20 * n) n (25 * n) p)
      (24 * n - upperHighCount (20 * n) p) : ℕ) : ℝ) ≤ t :=
    (Nat.cast_le.mpr (Nat.min_le_left (terminalSize (20 * n) n (25 * n) p)
      (24 * n - upperHighCount (20 * n) p))).trans ht
  simp only [upperCharge, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat]
  linarith

theorem terminalSize_low_bound (n p : ℕ) (hp : p ≤ 15 * n) :
    (terminalSize (20 * n) n (25 * n) p : ℝ) ≤ 30 * (n : ℝ) + 2 - 2 * p := by
  have h : terminalSize (20 * n) n (25 * n) p + 2 * p ≤ 30 * n + 2 := by
    unfold terminalSize
    omega
  have hr : (terminalSize (20 * n) n (25 * n) p : ℝ) + 2 * p ≤ 30 * (n : ℝ) + 2 := by
    exact_mod_cast h
  linarith

theorem terminalSize_high_bound (n p : ℕ) (hp : 15 * n ≤ p) :
    (terminalSize (20 * n) n (25 * n) p : ℝ) ≤ 2 := by
  have h : terminalSize (20 * n) n (25 * n) p ≤ 2 := by unfold terminalSize; omega
  exact_mod_cast h

theorem upperAffected_low_bound (n p : ℕ) (hn : 0 < n)
    (hq : 20 * n / p = 1) (hp : p ≤ 19 * n) :
    (n : ℝ) - 1 ≤ (upperAffectedCount (20 * n) n p : ℝ) := by
  have hmod := Nat.mod_add_div (20 * n) p
  rw [hq] at hmod
  have h : n ≤ upperAffectedCount (20 * n) n p + 1 := by
    unfold upperAffectedCount
    rw [hq]
    simp only [Nat.sub_self, mul_zero, zero_mul, zero_add]
    omega
  have hr : (n : ℝ) ≤ (upperAffectedCount (20 * n) n p : ℝ) + 1 := by exact_mod_cast h
  linarith

theorem upperAffected_early_bound (n p : ℕ) (hn : 0 < n)
    (hq : 20 * n / p = 1) (hp : 2 * p ≤ 21 * n) :
    22 * (n : ℝ) - 2 * p - 1 ≤ (upperAffectedCount (20 * n) n p : ℝ) := by
  have hmod := Nat.mod_add_div (20 * n) p
  rw [hq] at hmod
  have h : 22 * n ≤ upperAffectedCount (20 * n) n p + 2 * p + 1 := by
    unfold upperAffectedCount
    rw [hq]
    simp only [Nat.sub_self, mul_zero, zero_mul, zero_add]
    omega
  have hr : 22 * (n : ℝ) ≤ (upperAffectedCount (20 * n) n p : ℝ) + 2 * p + 1 := by
    exact_mod_cast h
  linarith

theorem upperAffected_late_bound (n p : ℕ) (hn : 0 < n)
    (hq : 20 * n / p = 1) (hp : 19 * n ≤ p) :
    20 * (n : ℝ) - p - 1 ≤ (upperAffectedCount (20 * n) n p : ℝ) := by
  have hmod := Nat.mod_add_div (20 * n) p
  rw [hq] at hmod
  have h : 20 * n ≤ upperAffectedCount (20 * n) n p + p + 1 := by
    unfold upperAffectedCount
    rw [hq]
    simp only [Nat.sub_self, mul_zero, zero_mul, zero_add]
    omega
  have hr : 20 * (n : ℝ) ≤ (upperAffectedCount (20 * n) n p : ℝ) + p + 1 := by
    exact_mod_cast h
  linarith

theorem stage_factorialCharge_bound (n p D q : ℕ) (hp : 0 < p)
    (hD : 50 * n / p = D) (hq : 20 * n / p = q) :
    (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤
      50 * D * (n : ℝ) - (p : ℝ) * D * (D + 1) / 2 - 48 * n * q := by
  have h := factorialCharge_real_bound (20 * n) n (24 * n) p hp
  have he : 2 * (n + 24 * n) = 50 * n := by omega
  rw [he, hD, hq] at h
  push_cast at h
  nlinarith

theorem upperCharge_row1 (n p : ℕ) (hn : 0 < n) (hl : 9 * n < p) (hr : p < 10 * n) :
    (upperCharge n p : ℝ) ≤ 324 * (n : ℝ) - 24 * p + 8 := by
  have hD : 50 * n / p = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 5 2 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ 0 _ hf (by positivity)
    (terminalSize_low_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row2 (n p : ℕ) (hn : 0 < n) (hl : 10 * n < p) (hr : 2 * p < 21 * n) :
    (upperCharge n p : ℝ) ≤ 278 * (n : ℝ) - 15 * p + 8 := by
  have hD : 50 * n / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 4 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_early_bound n p hn hq (by omega)) (terminalSize_low_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row3 (n p : ℕ) (hn : 0 < n) (hl : 21 * n < 2 * p) (hr : 2 * p < 25 * n) :
    (upperCharge n p : ℝ) ≤ 320 * (n : ℝ) - 19 * p + 8 := by
  have hD : 50 * n / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 4 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_low_bound n p hn hq (by omega)) (terminalSize_low_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row4 (n p : ℕ) (hn : 0 < n) (hl : 25 * n < 2 * p) (hr : p < 15 * n) :
    (upperCharge n p : ℝ) ≤ 270 * (n : ℝ) - 15 * p + 8 := by
  have hD : 50 * n / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 3 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_low_bound n p hn hq (by omega)) (terminalSize_low_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row5 (n p : ℕ) (hn : 0 < n) (hl : 15 * n < p) (hr : 3 * p < 50 * n) :
    (upperCharge n p : ℝ) ≤ 240 * (n : ℝ) - 13 * p + 8 := by
  have hD : 50 * n / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 3 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_low_bound n p hn hq (by omega)) (terminalSize_high_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row6 (n p : ℕ) (hn : 0 < n) (hl : 50 * n < 3 * p) (hr : p < 19 * n) :
    (upperCharge n p : ℝ) ≤ 190 * (n : ℝ) - 10 * p + 8 := by
  have hD : 50 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 2 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_low_bound n p hn hq (by omega)) (terminalSize_high_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_row7 (n p : ℕ) (hn : 0 < n) (hl : 19 * n < p) (hr : p < 20 * n) :
    (upperCharge n p : ℝ) ≤ 152 * (n : ℝ) - 8 * p + 8 := by
  have hD : 50 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hf := stage_factorialCharge_bound n p 2 1 (by omega) hD hq
  have h := upperCharge_le_of_bounds n p (by omega) _ _ _ hf
    (upperAffected_late_bound n p hn hq (by omega)) (terminalSize_high_bound n p (by omega))
  norm_num at h
  linarith

theorem upperCharge_affine (n p : ℕ) (row : AffineRow) (hn : 0 < n)
    (hrow : row ∈ upperRows)
    (hl : (row.lo : ℝ) < (p : ℝ) / (20 * n))
    (hr : (p : ℝ) / (20 * n) < (row.hi : ℝ)) :
    (upperCharge n p : ℝ) ≤
      20 * n * ((row.intercept : ℝ) + (row.slope : ℝ) * ((p : ℝ) / (20 * n))) + 8 := by
  have hN : (0 : ℝ) < 20 * n := by positivity
  have hl' := (lt_div_iff₀ hN).mp hl
  have hr' := (div_lt_iff₀ hN).mp hr
  have hbound : (upperCharge n p : ℝ) ≤
      20 * n * (row.intercept : ℝ) + (row.slope : ℝ) * p + 8 := by
    simp only [upperRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num at hl' hr' ⊢
    · have hb := upperCharge_row1 n p hn
        (by exact_mod_cast (by nlinarith : 9 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 10 * n))
      linarith
    · have hb := upperCharge_row2 n p hn
        (by exact_mod_cast (by nlinarith : 10 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : 2 * (p : ℝ) < 21 * n))
      linarith
    · have hb := upperCharge_row3 n p hn
        (by exact_mod_cast (by nlinarith : 21 * (n : ℝ) < 2 * p))
        (by exact_mod_cast (by nlinarith : 2 * (p : ℝ) < 25 * n))
      linarith
    · have hb := upperCharge_row4 n p hn
        (by exact_mod_cast (by nlinarith : 25 * (n : ℝ) < 2 * p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 15 * n))
      linarith
    · have hb := upperCharge_row5 n p hn
        (by exact_mod_cast (by nlinarith : 15 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : 3 * (p : ℝ) < 50 * n))
      linarith
    · have hb := upperCharge_row6 n p hn
        (by exact_mod_cast (by nlinarith : 50 * (n : ℝ) < 3 * p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 19 * n))
      linarith
    · have hb := upperCharge_row7 n p hn
        (by exact_mod_cast (by nlinarith : 19 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 20 * n))
      linarith
  convert hbound using 1 <;> field_simp <;> ring

def largeRows : List AffineRow :=
  [⟨1, 5 / 4, 5, -3⟩, ⟨5 / 4, 5 / 2, 5 / 2, -1⟩]

theorem largeRows_area : (largeRows.map AffineRow.area).sum = 19 / 16 := by
  norm_num [largeRows, AffineRow.area]

theorem largeCharge_row1 (n p : ℕ) (hn : 0 < n) (hl : 20 * n < p) (hr : p < 25 * n) :
    (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤ 100 * (n : ℝ) - 3 * p := by
  have hD : 50 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h := stage_factorialCharge_bound n p 2 0 (by omega) hD hq
  norm_num at h
  linarith

theorem largeCharge_row2 (n p : ℕ) (hn : 0 < n) (hl : 25 * n < p) (hr : p < 50 * n) :
    (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤ 50 * (n : ℝ) - p := by
  have hD : 50 * n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hq : 20 * n / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h := stage_factorialCharge_bound n p 1 0 (by omega) hD hq
  norm_num at h
  linarith

theorem largeCharge_affine (n p : ℕ) (row : AffineRow) (hn : 0 < n)
    (hrow : row ∈ largeRows)
    (hl : (row.lo : ℝ) < (p : ℝ) / (20 * n))
    (hr : (p : ℝ) / (20 * n) < (row.hi : ℝ)) :
    (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤
      20 * n * ((row.intercept : ℝ) + (row.slope : ℝ) * ((p : ℝ) / (20 * n))) := by
  have hN : (0 : ℝ) < 20 * n := by positivity
  have hl' := (lt_div_iff₀ hN).mp hl
  have hr' := (div_lt_iff₀ hN).mp hr
  have hbound : (factorialCharge (20 * n) n (24 * n) p : ℝ) ≤
      20 * n * (row.intercept : ℝ) + (row.slope : ℝ) * p := by
    simp only [largeRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl
    all_goals norm_num at hl' hr' ⊢
    · have hb := largeCharge_row1 n p hn
        (by exact_mod_cast (by nlinarith : 20 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 25 * n))
      linarith
    · have hb := largeCharge_row2 n p hn
        (by exact_mod_cast (by nlinarith : 25 * (n : ℝ) < p))
        (by exact_mod_cast (by nlinarith : (p : ℝ) < 50 * n))
      linarith
  convert hbound using 1 <;> field_simp <;> ring

#print axioms upperCharge_affine
#print axioms largeCharge_affine

end Zeta5.Arithmetic
