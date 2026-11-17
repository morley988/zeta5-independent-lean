import Zeta5.Certificate.DirectedBounds
import Mathlib.Tactic.NormNum

namespace Zeta5.Certificate

def fixedScale : ℕ := 10 ^ 30
def logTwoNumerator : ℕ := 693147180559945309417231930490

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem logTwoNumerator_exact :
    roundedLogNumerator fixedScale 333333333333333333333333333333 24 =
      logTwoNumerator := by decide

theorem logTwoNumerator_lower :
    (logTwoNumerator : ℝ) / fixedScale ≤ Real.log 2 := by
  rw [← logTwoNumerator_exact]
  apply roundedLogNumerator_le_log
  · norm_num [fixedScale]
  · norm_num
  · norm_num [fixedScale]

end Zeta5.Certificate
