import Zeta5.Reuse.PrimePiecewise
import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact signed prime charges and adjacent interval telescoping -/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise
open Finset
open scoped BigOperators

/-- The actual signed valuation charge; no positivity of f is assumed. -/
def primeWeightedSum (f : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, f p * Real.log p

@[simp] theorem primeWeightedSum_self (f : ℕ → ℝ) (a : ℕ) :
    primeWeightedSum f a a = 0 := by simp [primeWeightedSum]

theorem primeWeightedSum_add (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    primeWeightedSum f a b + primeWeightedSum f b c = primeWeightedSum f a c := by
  simp only [primeWeightedSum, Finset.sum_filter]
  exact Finset.sum_Ioc_consecutive _ hab hbc

theorem primeWeightedSum_floor_add (f : ℕ → ℝ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (N : ℕ) :
    primeWeightedSum f ⌊a * N⌋₊ ⌊b * N⌋₊ +
      primeWeightedSum f ⌊b * N⌋₊ ⌊c * N⌋₊ =
        primeWeightedSum f ⌊a * N⌋₊ ⌊c * N⌋₊ := by
  apply primeWeightedSum_add
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N))
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_right hbc (Nat.cast_nonneg N))

theorem primeWeightedSum_mono {f g : ℕ → ℝ} (a b : ℕ)
    (hfg : ∀ p, p.Prime → a < p → p ≤ b → f p ≤ g p) :
    primeWeightedSum f a b ≤ primeWeightedSum g a b := by
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpab, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpa, hpb⟩ := Finset.mem_Ioc.mp hpab
  exact mul_le_mul_of_nonneg_right (hfg p hprime hpa hpb) (Real.log_natCast_nonneg p)

theorem AffinePiece.primeMass_eq_weightedSum (c : AffinePiece) (N : ℕ) :
    c.primeMass N = primeWeightedSum
      (fun p => (N : ℝ) * (c.intercept + c.slope * ((p : ℝ) / N)))
      ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊ := by
  simp only [AffinePiece.primeMass, primeWeightedSum, Finset.mul_sum, mul_assoc]

end Zeta5.Reuse.PrimePiecewise
