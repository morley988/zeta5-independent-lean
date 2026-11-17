import Zeta5.Reuse.PrimePiecewise

/-! # Exact recombination of finite prime pieces into a single profile sum -/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise
open Finset
open scoped BigOperators

def AffinePiece.valueAt (c : AffinePiece) (β : ℝ) : ℝ :=
  if c.lo < β ∧ β ≤ c.hi then c.intercept + c.slope * β else 0

def finiteProfile (cells : List AffinePiece) (β : ℝ) : ℝ :=
  (cells.map (fun c => c.valueAt β)).sum

@[simp] theorem finiteProfile_nil (β : ℝ) : finiteProfile [] β = 0 := rfl

@[simp] theorem finiteProfile_cons (c : AffinePiece) (cs : List AffinePiece) (β : ℝ) :
    finiteProfile (c :: cs) β = c.valueAt β + finiteProfile cs β := rfl

theorem finiteProfile_append (xs ys : List AffinePiece) (β : ℝ) :
    finiteProfile (xs ++ ys) β = finiteProfile xs β + finiteProfile ys β := by
  simp [finiteProfile]

theorem finiteProfile_zero {cells : List AffinePiece} {β : ℝ}
    (h : ∀ c ∈ cells, ¬ (c.lo < β ∧ β ≤ c.hi)) : finiteProfile cells β = 0 := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
      simp only [finiteProfile_cons, AffinePiece.valueAt, if_neg (h c (by simp)), zero_add]
      exact ih (fun d hd => h d (by simp [hd]))

def primeRange (C : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 0 ⌊C * N⌋₊).filter Nat.Prime

theorem AffinePiece.primeMass_eq_sum_valueAt (c : AffinePiece) (hc : c.Valid)
    {C : ℝ} (hcC : c.hi ≤ C) {N : ℕ} (hN : 0 < N) :
    c.primeMass N = (N : ℝ) * ∑ p ∈ primeRange C N,
      c.valueAt ((p : ℝ) / N) * Real.log p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hCN : 0 ≤ C * N := mul_nonneg (hc.1.le.trans (hc.2.trans hcC)) hNr.le
  let S := (Finset.Ioc ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊).filter Nat.Prime
  have hsub : S ⊆ primeRange C N := by
    intro p hp
    have hs := (PrimeAffine.prime_interval_membership _ _ hc.1.le hc.2 N p).mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, hs.1⟩
    apply (Nat.le_floor_iff hCN).mpr
    exact hs.2.2.trans (mul_le_mul_of_nonneg_right hcC hNr.le)
  have hcond (p : ℕ) : (c.lo < (p : ℝ) / N ∧ (p : ℝ) / N ≤ c.hi) ↔
      (c.lo * N < p ∧ (p : ℝ) ≤ c.hi * N) := by
    rw [lt_div_iff₀ hNr, div_le_iff₀ hNr]
  unfold primeMass
  congr 1
  calc
    (∑ p ∈ S, (c.intercept + c.slope * ((p : ℝ) / N)) * Real.log p) =
        ∑ p ∈ S, c.valueAt ((p : ℝ) / N) * Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hs := (PrimeAffine.prime_interval_membership _ _ hc.1.le hc.2 N p).mp hp
      simp [AffinePiece.valueAt, (hcond p).mpr hs.2]
    _ = ∑ p ∈ primeRange C N, c.valueAt ((p : ℝ) / N) * Real.log p := by
      apply Finset.sum_subset hsub
      intro p hp hpS
      have hpprime := (Finset.mem_filter.mp hp).2
      have hnot : ¬ (c.lo < (p : ℝ) / N ∧ (p : ℝ) / N ≤ c.hi) := by
        intro hh
        exact hpS ((PrimeAffine.prime_interval_membership _ _ hc.1.le hc.2 N p).mpr
          ⟨hpprime, (hcond p).mp hh⟩)
      simp [AffinePiece.valueAt, hnot]

theorem finitePrimeMass_eq_sum_profile (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) {C : ℝ} (hC : ∀ c ∈ cells, c.hi ≤ C)
    {N : ℕ} (hN : 0 < N) :
    finitePrimeMass cells N = (N : ℝ) * ∑ p ∈ primeRange C N,
      finiteProfile cells ((p : ℝ) / N) * Real.log p := by
  induction cells with
  | nil => simp [finitePrimeMass, finiteProfile]
  | cons c cs ih =>
      have ht := ih (fun d hd => hcells d (by simp [hd])) (fun d hd => hC d (by simp [hd]))
      change c.primeMass N + finitePrimeMass cs N = _
      rw [c.primeMass_eq_sum_valueAt (hcells c (by simp)) (hC c (by simp)) hN, ht]
      simp only [finiteProfile_cons, add_mul, Finset.sum_add_distrib, mul_add]

end Zeta5.Reuse.PrimePiecewise
