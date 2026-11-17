import Zeta5.Reuse.PrimeIntervals

/-! Signed affine prime sums with one endpoint exception per row. -/

noncomputable section
namespace Zeta5.Arithmetic
open Finset Zeta5.Reuse.PrimePiecewise
open scoped Chebyshev

def rightEndpointPenalty (c : AffinePiece) (U : ℝ) : ℝ :=
  U + |c.intercept + c.slope * c.hi|

theorem prime_row_charge_le (c : AffinePiece) (hc : c.Valid) (N : ℕ) (hN : 0 < N)
    (C U K : ℝ) (hC : c.hi ≤ C) (hCN : 1 ≤ C * N) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (f : ℕ → ℝ)
    (hregular : ∀ p : ℕ, p.Prime → c.lo < (p : ℝ) / N → (p : ℝ) / N < c.hi →
      f p ≤ N * (c.intercept + c.slope * ((p : ℝ) / N)) + K)
    (huniform : ∀ p : ℕ, p.Prime → c.lo < (p : ℝ) / N → (p : ℝ) / N ≤ c.hi →
      f p ≤ U * N) :
    (∑ p ∈ (Ioc ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊).filter Nat.Prime, f p * Real.log p) ≤
      c.primeMass N + K * θ (C * N) +
        rightEndpointPenalty c U * N * Real.log (C * N) := by
  let S := (Ioc ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊).filter Nat.Prime
  let B := S.filter (fun p : ℕ => (p : ℝ) / N = c.hi)
  let L := rightEndpointPenalty c U
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ L := add_nonneg hU (abs_nonneg _)
  have hlog : 0 ≤ Real.log (C * N) := Real.log_nonneg hCN
  have hmem (p : ℕ) (hp : p ∈ S) :
      p.Prime ∧ c.lo < (p : ℝ) / N ∧ (p : ℝ) / N ≤ c.hi := by
    obtain ⟨hpr, hl, hr⟩ :=
      (Zeta5.Reuse.PrimeAffine.prime_interval_membership c.lo c.hi hc.1.le hc.2 N p).mp hp
    exact ⟨hpr, (lt_div_iff₀ hNR).mpr hl, (div_le_iff₀ hNR).mpr hr⟩
  have hpCN (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ C * N := by
    have h := (div_le_iff₀ hNR).mp (hmem p hp).2.2
    exact h.trans (mul_le_mul_of_nonneg_right hC hNR.le)
  have htheta : (∑ p ∈ S, Real.log p) ≤ θ (C * N) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, (hmem p hp).1⟩
      exact (Nat.le_floor_iff (by linarith : 0 ≤ C * N)).mpr (hpCN p hp)
    · intro p hp hn
      exact Real.log_natCast_nonneg p
  have hBsub : B ⊆ {⌊c.hi * N⌋₊} := by
    intro p hp
    obtain ⟨hpS, he⟩ := mem_filter.mp hp
    have heq : (p : ℝ) = c.hi * N := (div_eq_iff hNR.ne').mp he
    simp only [mem_singleton]
    rw [← heq, Nat.floor_natCast]
  have hBsum : (∑ p ∈ B, Real.log p) ≤ Real.log (C * N) := by
    calc
      _ ≤ ∑ _p ∈ B, Real.log (C * N) := by
        apply sum_le_sum
        intro p hp
        have hpS := (mem_filter.mp hp).1
        apply Real.log_le_log
        · exact_mod_cast (hmem p hpS).1.pos
        · exact hpCN p hpS
      _ ≤ ∑ _p ∈ ({⌊c.hi * N⌋₊} : Finset ℕ), Real.log (C * N) :=
        sum_le_sum_of_subset_of_nonneg hBsub (fun _ _ _ => hlog)
      _ = _ := by simp
  have hpoint (p : ℕ) (hp : p ∈ S) :
      f p * Real.log p ≤
        (N * (c.intercept + c.slope * ((p : ℝ) / N)) + K) * Real.log p +
          if (p : ℝ) / N = c.hi then L * N * Real.log p else 0 := by
    obtain ⟨hpr, hl, hr⟩ := hmem p hp
    have hplog := Real.log_natCast_nonneg p
    by_cases he : (p : ℝ) / N = c.hi
    · rw [if_pos he, he]
      have hf := huniform p hpr hl hr
      have hab := neg_abs_le (c.intercept + c.slope * c.hi)
      have hh : f p ≤ N * (c.intercept + c.slope * c.hi) + K + L * N := by
        dsimp [L, rightEndpointPenalty]
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hh hplog
      nlinarith
    · rw [if_neg he, add_zero]
      exact mul_le_mul_of_nonneg_right (hregular p hpr hl (lt_of_le_of_ne hr he)) hplog
  have hsum := sum_le_sum hpoint
  have hrewrite :
      (∑ p ∈ S, (((N : ℝ) * (c.intercept + c.slope * ((p : ℝ) / N)) + K) * Real.log p +
        if (p : ℝ) / N = c.hi then L * N * Real.log p else 0)) =
        c.primeMass N + K * (∑ p ∈ S, Real.log p) + L * N * (∑ p ∈ B, Real.log p) := by
    rw [sum_add_distrib, ← sum_filter]
    simp only [AffinePiece.primeMass, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    rfl
  rw [hrewrite] at hsum
  exact hsum.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left htheta hK))
    (mul_le_mul_of_nonneg_left hBsum (mul_nonneg hL hNR.le)))

#print axioms prime_row_charge_le

theorem sum_prime_row_bounds (cells : List AffinePiece) (N : ℕ) (C U K : ℝ)
    (f : ℕ → ℝ)
    (hrow : ∀ c ∈ cells,
      primeWeightedSum f ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊ ≤
        c.primeMass N + K * θ (C * N) +
          rightEndpointPenalty c U * N * Real.log (C * N)) :
    (cells.map (fun c : AffinePiece => primeWeightedSum f ⌊c.lo * (N : ℝ)⌋₊ ⌊c.hi * (N : ℝ)⌋₊)).sum ≤
      finitePrimeMass cells N + (K * cells.length) * θ (C * N) +
        (cells.map (fun c => rightEndpointPenalty c U)).sum * N * Real.log (C * N) := by
  induction cells with
  | nil => simp [finitePrimeMass]
  | cons c cs ih =>
    have hh := hrow c (by simp)
    have ht := ih (fun d hd => hrow d (by simp [hd]))
    have h := add_le_add hh ht
    convert h using 1 <;> first | rfl |
      (simp only [List.map_cons, List.sum_cons, finitePrimeMass, List.length_cons,
        Nat.cast_add, Nat.cast_one]; ring)

end Zeta5.Arithmetic
