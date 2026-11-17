import Zeta5.Reuse.PrimeNumberTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite affine prime profiles and negligible boundary costs

Signed affine pieces are summed without a sign restriction. The main term is
of quadratic scale, while a uniform per-prime error and finitely many endpoint
strips contribute only theta(CN) and N log(CN), respectively.
-/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise
open Filter Finset
open scoped Topology Chebyshev BigOperators

structure AffinePiece where
  lo : ℝ
  hi : ℝ
  intercept : ℝ
  slope : ℝ

namespace AffinePiece

def Valid (c : AffinePiece) : Prop := 0 < c.lo ∧ c.lo ≤ c.hi

def area (c : AffinePiece) : ℝ :=
  c.intercept * (c.hi - c.lo) + c.slope * (c.hi ^ 2 - c.lo ^ 2) / 2

/-- Unnormalized logarithmic prime sum with the valuation-scale factor N. -/
def primeMass (c : AffinePiece) (N : ℕ) : ℝ :=
  (N : ℝ) * ∑ p ∈ (Finset.Ioc ⌊c.lo * N⌋₊ ⌊c.hi * N⌋₊).filter Nat.Prime,
    (c.intercept + c.slope * ((p : ℝ) / (N : ℝ))) * Real.log p

theorem primeMass_div_sq (c : AffinePiece) (N : ℕ) :
    c.primeMass N / (N : ℝ) ^ 2 =
      PrimeAffine.primeAffineSum c.lo c.hi c.intercept c.slope N := by
  unfold primeMass PrimeAffine.primeAffineSum
  by_cases hN : N = 0
  · simp [hN]
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

theorem primeMass_limit (c : AffinePiece) (hc : c.Valid) :
    Tendsto (fun N => c.primeMass N / (N : ℝ) ^ 2) atTop (𝓝 c.area) := by
  simp_rw [primeMass_div_sq]
  exact PrimeNumberTheorem.primeAffineSum_limit _ _ _ _ hc.1 hc.2

end AffinePiece

def finitePrimeMass (cells : List AffinePiece) (N : ℕ) : ℝ :=
  (cells.map (fun c => c.primeMass N)).sum

def finiteArea (cells : List AffinePiece) : ℝ := (cells.map AffinePiece.area).sum

theorem finitePrimeMass_limit (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) :
    Tendsto (fun N => finitePrimeMass cells N / (N : ℝ) ^ 2) atTop (𝓝 (finiteArea cells)) := by
  induction cells with
  | nil => simpa [finitePrimeMass, finiteArea] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | cons c cs ih =>
      have hc := c.primeMass_limit (hcells c (by simp))
      have ht := ih (fun d hd => hcells d (by simp [hd]))
      simpa [finitePrimeMass, finiteArea, add_div] using hc.add ht

/-- A uniform O(1) error at each prime costs only O(N), by theta. -/
theorem theta_over_sq_limit (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ => θ (C * N) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := (ThetaAsymptotic.scaled_limit θ PrimeNumberTheorem.theta_ratio_limit C hC).comp
    tendsto_natCast_atTop_atTop
  have ht := h.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [mul_zero, Function.comp_apply, div_mul_div_comm, mul_one, pow_two] using ht

theorem log_linear_over_nat_limit (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ => Real.log (C * N) / (N : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => C * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hC
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp ht
  have hm := hl.const_mul C
  simp only [pow_one, one_mul, add_zero, mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [Function.comp_apply]
  field_simp

theorem nat_log_linear_over_sq_limit (C : ℝ) (hC : 0 < C) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.log (C * N) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  apply (log_linear_over_nat_limit C hC).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- All finite affine pieces, a uniform prime error, and finite boundary costs. -/
def primeProfileMajorant (cells : List AffinePiece) (K L C : ℝ) (N : ℕ) : ℝ :=
  finitePrimeMass cells N + K * θ (C * N) + L * (N : ℝ) * Real.log (C * N)

theorem primeProfileMajorant_limit (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L C : ℝ) (hC : 0 < C) :
    Tendsto (fun N => primeProfileMajorant cells K L C N / (N : ℝ) ^ 2)
      atTop (𝓝 (finiteArea cells)) := by
  have h := ((finitePrimeMass_limit cells hcells).add
    ((theta_over_sq_limit C hC).const_mul K)).add
    ((nat_log_linear_over_sq_limit C hC).const_mul L)
  simpa [primeProfileMajorant, add_div, mul_div_assoc, mul_assoc] using h

/-- A convergent quadratic majorant supplies the exact o(N²) error interface.
The upper rate A may exceed the finite sum of piece areas. -/
theorem exists_rate_error_of_majorant {f g : ℕ → ℝ} {a A : ℝ}
    (hlim : Tendsto (fun N => g N / (N : ℝ) ^ 2) atTop (𝓝 a))
    (hbound : ∀ᶠ N in atTop, f N ≤ g N) (ha : a ≤ A) :
    ∃ E : ℕ → ℝ,
      Tendsto (fun N => E N / (N : ℝ) ^ 2) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, f N ≤ A * (N : ℝ) ^ 2 + E N) := by
  refine ⟨fun N => g N - a * (N : ℝ) ^ 2, ?_, ?_⟩
  · have h := hlim.sub_const a
    simp only [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · filter_upwards [hbound] with N hN
    have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (N : ℝ))
    linarith

end Zeta5.Reuse.PrimePiecewise
