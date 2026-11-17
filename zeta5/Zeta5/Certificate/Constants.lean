import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Exact constants in the Stage 60 comparison certificate

These theorems check rational arithmetic only. They do not identify the
constant `arithmeticTotal` with an asymptotic arithmetic rate, nor do they
assert an analytic estimate for the determinant.
-/

namespace Zeta5.Certificate

def arithmeticTotal : ℚ :=
  191258319415140413215011151671222972968539453509572803845881093658106414835114844023 /
  35352223433977492021442108242640841605890021236208954246644376534746108587827200000

def s : ℚ := 1 / 20
def rho : ℚ := 5 / 4
def delta : ℚ := rho - s
def leftEndpoint : ℚ := 1 / 40

theorem delta_eq : delta = 6 / 5 := by norm_num [delta, rho, s]

theorem small_tail_exact :
    (4 * delta + rho) * leftEndpoint + leftEndpoint ^ 2 / 4 = 969 / 6400 := by
  norm_num [delta, rho, s, leftEndpoint]

theorem large_primes_exact : 3 * rho ^ 2 - 4 * rho + 3 / 2 = 19 / 16 := by
  norm_num [rho]

theorem arithmeticTotal_pos : 0 < arithmeticTotal := by norm_num [arithmeticTotal]

theorem arithmeticTotal_lt_threshold : arithmeticTotal < 54101 / 10000 := by
  norm_num [arithmeticTotal]

theorem rounded_analytic_lower_gt_threshold :
    (54133705070 : ℚ) / 10 ^ 10 > 54133 / 10000 := by norm_num

theorem exact_rational_margin :
    (54133705070 : ℚ) / 10 ^ 10 - arithmeticTotal > 32 / 10000 := by
  norm_num [arithmeticTotal]

/-- Transferring the two stated strict bounds gives the claimed positive gap.
The hypotheses are explicit because proving the rate bounds is separate work. -/
theorem strict_gap_of_rate_bounds (arithmetic analytic : ℝ)
    (ha : arithmetic < 54101 / 10000)
    (hb : 54133 / 10000 < analytic) :
    32 / 10000 < analytic - arithmetic := by
  linarith

end Zeta5.Certificate
