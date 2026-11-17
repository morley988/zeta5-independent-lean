import Zeta5.Analysis.PhysicalNormTrial
import Zeta5.Analysis.WindowGramBound
import Zeta5.Reuse.FactorialRow

/-! # Exact cancellation of the factorial and scaling terms in each row -/

noncomputable section
namespace Zeta5.Analysis
open Real Polynomial OddZeta.FourValue
open scoped BigOperators

def rowNormUpper (K s : ℝ) (hs : 0 < s) (N m k : ℕ) : ℝ :=
  gramNormFactor N m k * (K * physicalWeightScale N m * (N : ℝ) ^ (4 * k + 22) *
    Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)))

theorem rowNormUpper_pos {K s : ℝ} (hK : 0 < K) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (m k : ℕ) : 0 < rowNormUpper K s hs N m k := by
  unfold rowNormUpper
  exact mul_pos (gramNormFactor_pos _ _ _)
    (mul_pos (mul_pos (mul_pos hK (physicalWeightScale_pos hN _)) (by positivity))
      (Real.exp_pos _))

theorem rowNormUpper_cancel {K s : ℝ} (hs : 0 < s) (N m k : ℕ) :
    rowNormUpper K s hs N m k =
      K * ((Nat.factorial N : ℝ) ^ 2 / (Nat.factorial (2 * (m + k)) : ℝ) ^ 2) *
        ((N : ℝ) ^ (4 * (m + k) + 22) / (N : ℝ) ^ (2 * N)) *
          Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)) := by
  unfold rowNormUpper gramNormFactor physicalWeightScale
  rw [show 4 * (m + k) + 22 = 4 * m + (4 * k + 22) by omega, pow_add]
  have hf : (Nat.factorial (2 * m) : ℝ) ≠ 0 := by positivity
  field_simp [hf]
  ring

theorem log_rowNormUpper {K s : ℝ} (hK : 0 < K) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (m k : ℕ) :
    Real.log (rowNormUpper K s hs N m k) =
      Real.log K + 2 * Real.log (Nat.factorial N : ℝ) -
        2 * Real.log (Nat.factorial (2 * (m + k)) : ℝ) +
        (4 * ((m + k : ℕ) : ℝ) + 22 - 2 * (N : ℝ)) * Real.log (N : ℝ) +
        (N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N) := by
  rw [rowNormUpper_cancel hs]
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hK.ne' (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

/-- The factorial lower bounds suffice for the upper row estimate; the only
Stirling error comes from N!, and is uniform in the row index. -/
theorem log_rowNormUpper_le_profile {K s : ℝ} (hK : 0 < K) (hs : 0 < s)
    {N m : ℕ} (hN : 0 < N) (hms : (m : ℝ) / N = s) (k : ℕ) :
    Real.log (rowNormUpper K s hs N m k) ≤
      (N : ℝ) * analyticProfile s hs ((k : ℝ) / N) +
        (Real.log K + 22 * Real.log (N : ℝ) + Real.log ((N : ℝ) + 1) + 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfac := (abs_le.mp (log_factorial_main_error N)).2
  have hrow := factorial_row_main_upper (m + k) (N : ℝ) hNr
  have hnorm : (N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N) - 2 * (N : ℝ) +
      (N : ℝ) * factorialRowRate (((m + k : ℕ) : ℝ) / N) =
        (N : ℝ) * analyticProfile s hs ((k : ℝ) / N) := by
    simp only [Nat.cast_add, add_div, hms, profileEquilibrium, factorialRowRate]
    ring
  rw [log_rowNormUpper hK hs hN]
  linarith

end Zeta5.Analysis
