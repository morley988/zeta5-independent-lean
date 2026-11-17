import Zeta5.Certificate.ExtendedArithmetic.Chain
import Zeta5.Reuse.PrimeIntervals

/-! # The exact prime-charge telescope through the certified middle chain -/

noncomputable section
namespace Zeta5.Certificate.ExtendedArithmetic
open Zeta5.Reuse.PrimePiecewise

def chainWeightedSum (xs : List (ArithmeticCell × ℚ)) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (xs.map (fun x => primeWeightedSum f ⌊(x.1.lo : ℝ) * N⌋₊ ⌊(x.1.hi : ℝ) * N⌋₊)).sum

theorem chainWeightedSum_telescope {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) (f : ℕ → ℝ) (N : ℕ) :
    chainWeightedSum xs f N =
      primeWeightedSum f ⌊(a : ℝ) * N⌋₊ ⌊(cappedChainEnd a xs : ℝ) * N⌋₊ := by
  induction xs generalizing a with
  | nil => simp [chainWeightedSum, cappedChainEnd]
  | cons x xs ih =>
      change primeWeightedSum f ⌊(x.1.lo : ℝ) * N⌋₊ ⌊(x.1.hi : ℝ) * N⌋₊ +
        chainWeightedSum xs f N = _
      rw [ih h.2.2.2]
      change _ = primeWeightedSum f ⌊(a : ℝ) * N⌋₊ ⌊(cappedChainEnd x.1.hi xs : ℝ) * N⌋₊
      rw [h.1]
      apply primeWeightedSum_floor_add
      · exact_mod_cast (h.1 ▸ h.2.1.2.1.le)
      · exact_mod_cast cappedChain_end_ge h.2.2.2

/-- Summing per-cell signed upper bounds and then telescoping requires no
positivity assumption on the valuation charge or affine coefficients. -/
theorem chainWeightedSum_le {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) (f : ℕ → ℝ) (N : ℕ) (error : ArithmeticCell × ℚ → ℝ)
    (hcell : ∀ x ∈ xs,
      primeWeightedSum f ⌊(x.1.lo : ℝ) * N⌋₊ ⌊(x.1.hi : ℝ) * N⌋₊ ≤
        (cellPrimePiece x.1).primeMass N + error x) :
    primeWeightedSum f ⌊(a : ℝ) * N⌋₊ ⌊(cappedChainEnd a xs : ℝ) * N⌋₊ ≤
      finitePrimeMass (chainPrimePieces xs) N + (xs.map error).sum := by
  rw [← chainWeightedSum_telescope h]
  induction xs generalizing a with
  | nil => simp [chainWeightedSum, chainPrimePieces, finitePrimeMass]
  | cons x xs ih =>
      have hc := hcell x (by simp)
      have ht := ih h.2.2.2 (fun y hy => hcell y (by simp [hy]))
      simpa [chainWeightedSum, chainPrimePieces, finitePrimeMass, add_assoc, add_left_comm, add_comm]
        using add_le_add hc ht

end Zeta5.Certificate.ExtendedArithmetic
