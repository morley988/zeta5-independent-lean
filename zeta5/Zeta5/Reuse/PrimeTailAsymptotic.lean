import Zeta5.Reuse.PrimePiecewise

/-! # A fixed small-prime tail and finite affine profile asymptotics -/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise
open Filter
open scoped Topology Chebyshev

theorem nat_theta_over_sq_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (N : ℝ) * θ (c * N) / (N : ℝ) ^ 2) atTop (𝓝 c) := by
  have h := (ThetaAsymptotic.scaled_limit θ PrimeNumberTheorem.theta_ratio_limit c hc).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [Function.comp_apply]
  field_simp

def primeProfileWithTail (cells : List AffinePiece) (tailRate cutoff K L C : ℝ) (N : ℕ) : ℝ :=
  primeProfileMajorant cells K L C N + tailRate * (N : ℝ) * θ (cutoff * N)

theorem primeProfileWithTail_limit (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (tailRate cutoff K L C : ℝ)
    (hcutoff : 0 < cutoff) (hC : 0 < C) :
    Tendsto (fun N => primeProfileWithTail cells tailRate cutoff K L C N / (N : ℝ) ^ 2)
      atTop (𝓝 (finiteArea cells + tailRate * cutoff)) := by
  have h := (primeProfileMajorant_limit cells hcells K L C hC).add
    ((nat_theta_over_sq_limit cutoff hcutoff).const_mul tailRate)
  simpa [primeProfileWithTail, add_div, mul_div_assoc, mul_assoc] using h

end Zeta5.Reuse.PrimePiecewise
