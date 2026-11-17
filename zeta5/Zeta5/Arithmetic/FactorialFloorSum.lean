import Zeta5.Arithmetic.FactorialPrefactor
import Mathlib.Algebra.BigOperators.Intervals

/-! A finite double-counting bound for the factorial charge.
No asymptotic floor-sum or numerical approximation is assumed. -/

noncomputable section
namespace Zeta5.Arithmetic
open Finset

theorem twice_sum_Icc_id (D : ℕ) : 2 * (∑ k ∈ Icc 1 D, k) = D * (D + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [sum_Icc_succ_top (by omega)]
    nlinarith

theorem floor_sum_double_count (R p D : ℕ) (hp : 0 < p) (hD : 2 * R / p ≤ D) :
    (∑ j ∈ range R, 2 * j / p) =
      ∑ k ∈ Icc 1 D, ((range R).filter (fun j => k * p ≤ 2 * j)).card := by
  have hj (j : ℕ) (hj : j ∈ range R) :
      2 * j / p = ∑ k ∈ Icc 1 D, if k * p ≤ 2 * j then (1 : ℕ) else 0 := by
    have hjR : j < R := mem_range.mp hj
    have hbound : 2 * j / p ≤ D := (Nat.div_le_div_right (by omega : 2 * j ≤ 2 * R)).trans hD
    have he : (Icc 1 D).filter (fun k => k * p ≤ 2 * j) = Icc 1 (2 * j / p) := by
      ext k
      simp only [mem_filter, mem_Icc, ← Nat.le_div_iff_mul_le hp]
      omega
    rw [← sum_filter, he]
    simp
  rw [sum_congr rfl hj, sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter]
  simp

theorem floor_level_card_bound (R p k : ℕ) (hkp : k * p ≤ 2 * R) :
    2 * ((range R).filter (fun j => k * p ≤ 2 * j)).card + k * p ≤ 2 * R := by
  have he : (range R).filter (fun j => k * p ≤ 2 * j) = Ico ((k * p + 1) / 2) R := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [he, Nat.card_Ico]
  omega

theorem factorial_floor_sum_bound (R p : ℕ) (hp : 0 < p) :
    4 * (∑ j ∈ range R, 2 * j / p) + p * (2 * R / p) * (2 * R / p + 1) ≤
      4 * (2 * R / p) * R := by
  let D := 2 * R / p
  have hsum := sum_le_sum (s := Icc 1 D) (fun k hk =>
    floor_level_card_bound R p k (by
      have hkD := (mem_Icc.mp hk).2
      exact (Nat.mul_le_mul_right p hkD).trans (Nat.div_mul_le_self (2 * R) p)))
  rw [sum_add_distrib, ← mul_sum, ← sum_mul, sum_const, Nat.card_Icc] at hsum
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hsum
  rw [← floor_sum_double_count R p D hp le_rfl] at hsum
  have hid := twice_sum_Icc_id D
  change 4 * (∑ j ∈ range R, 2 * j / p) + p * D * (D + 1) ≤ 4 * D * R
  nlinarith

theorem factorial_window_floor_sum_le (m r p : ℕ) :
    (∑ k : Fin r, 2 * (m + k.val) / p) ≤ ∑ j ∈ range (m + r), 2 * j / p := by
  rw [Fin.sum_univ_eq_sum_range (fun k => 2 * (m + k) / p), sum_range_add]
  omega

theorem factorialCharge_real_bound (N m r p : ℕ) (hp : 0 < p) :
    (factorialCharge N m r p : ℝ) ≤
      2 * ((2 * (m + r) / p : ℕ) : ℝ) * (m + r) -
        (p : ℝ) * ((2 * (m + r) / p : ℕ) : ℝ) * (((2 * (m + r) / p : ℕ) : ℝ) + 1) / 2 -
        2 * r * ((N / p : ℕ) : ℝ) := by
  have hf := factorial_floor_sum_bound (m + r) p hp
  have hw := factorial_window_floor_sum_le m r p
  have hfR : 4 * (∑ j ∈ range (m + r), (((2 * j) / p : ℕ) : ℝ)) +
      (p : ℝ) * ((2 * (m + r) / p : ℕ) : ℝ) * (((2 * (m + r) / p : ℕ) : ℝ) + 1) ≤
      4 * ((2 * (m + r) / p : ℕ) : ℝ) * (m + r) := by exact_mod_cast hf
  have hwR : (∑ k : Fin r, (((2 * (m + k.val)) / p : ℕ) : ℝ)) ≤
      ∑ j ∈ range (m + r), (((2 * j) / p : ℕ) : ℝ) := by exact_mod_cast hw
  simp only [factorialCharge, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, Int.cast_sum]
  linarith

#print axioms factorial_floor_sum_bound
#print axioms factorialCharge_real_bound

end Zeta5.Arithmetic
