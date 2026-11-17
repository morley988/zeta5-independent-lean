import Zeta5.Certificate.ExtendedArithmetic.Block00
import Zeta5.Certificate.ExtendedArithmetic.Block01
import Zeta5.Certificate.ExtendedArithmetic.Block02
import Zeta5.Certificate.ExtendedArithmetic.Block03
import Zeta5.Certificate.ExtendedArithmetic.Block04
import Zeta5.Certificate.ExtendedArithmetic.Block05
import Zeta5.Certificate.ExtendedArithmetic.Block06
import Zeta5.Certificate.ExtendedArithmetic.Block07
import Zeta5.Certificate.ExtendedArithmetic.Block08
import Zeta5.Certificate.ExtendedArithmetic.Block09
import Zeta5.Certificate.ExtendedArithmetic.Block10
import Zeta5.Certificate.ExtendedArithmetic.Block11
import Zeta5.Certificate.ExtendedArithmetic.Block12
import Zeta5.Certificate.ExtendedArithmetic.Block13
import Zeta5.Certificate.ExtendedArithmetic.Block14
import Zeta5.Certificate.ExtendedArithmetic.Block15
import Zeta5.Certificate.ExtendedArithmetic.Block16
import Zeta5.Certificate.ExtendedArithmetic.Block17
import Zeta5.Certificate.ExtendedArithmetic.Block18
import Zeta5.Certificate.ExtendedArithmetic.Block19
import Zeta5.Certificate.ExtendedArithmetic.Block20
import Zeta5.Certificate.ExtendedArithmetic.Block21
import Zeta5.Certificate.ExtendedArithmetic.Block22
import Zeta5.Certificate.ExtendedArithmetic.Block23

set_option maxHeartbeats 0

namespace Zeta5.Certificate.ExtendedArithmetic

theorem append_real_profile_bounds {a b c A B : ℝ}
    (h1 : IntervalIntegrable middleRankProfile MeasureTheory.volume a b ∧
      (∫ β in a..b, middleRankProfile β) ≤ A)
    (h2 : IntervalIntegrable middleRankProfile MeasureTheory.volume b c ∧
      (∫ β in b..c, middleRankProfile β) ≤ B) :
    IntervalIntegrable middleRankProfile MeasureTheory.volume a c ∧
      (∫ β in a..c, middleRankProfile β) ≤ A + B := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1]
  exact add_le_add h1.2 h2.2

def areaUpper : ℚ := (33853132329 / 12500000000)

def totalUpper : ℚ := (202930490737 / 37500000000)

theorem extended_profile_bound :
    IntervalIntegrable middleRankProfile MeasureTheory.volume (1 / 512 : ℝ) (9 / 20 : ℝ) ∧
    (∫ β in (1 / 512 : ℝ)..(9 / 20 : ℝ), middleRankProfile β) ≤ (areaUpper : ℝ) := by
  have h0 := Block00.bound
  have h1 := append_real_profile_bounds h0 Block01.bound
  have h2 := append_real_profile_bounds h1 Block02.bound
  have h3 := append_real_profile_bounds h2 Block03.bound
  have h4 := append_real_profile_bounds h3 Block04.bound
  have h5 := append_real_profile_bounds h4 Block05.bound
  have h6 := append_real_profile_bounds h5 Block06.bound
  have h7 := append_real_profile_bounds h6 Block07.bound
  have h8 := append_real_profile_bounds h7 Block08.bound
  have h9 := append_real_profile_bounds h8 Block09.bound
  have h10 := append_real_profile_bounds h9 Block10.bound
  have h11 := append_real_profile_bounds h10 Block11.bound
  have h12 := append_real_profile_bounds h11 Block12.bound
  have h13 := append_real_profile_bounds h12 Block13.bound
  have h14 := append_real_profile_bounds h13 Block14.bound
  have h15 := append_real_profile_bounds h14 Block15.bound
  have h16 := append_real_profile_bounds h15 Block16.bound
  have h17 := append_real_profile_bounds h16 Block17.bound
  have h18 := append_real_profile_bounds h17 Block18.bound
  have h19 := append_real_profile_bounds h18 Block19.bound
  have h20 := append_real_profile_bounds h19 Block20.bound
  have h21 := append_real_profile_bounds h20 Block21.bound
  have h22 := append_real_profile_bounds h21 Block22.bound
  have h23 := append_real_profile_bounds h22 Block23.bound
  norm_num [areaUpper] at h23 ⊢
  exact h23

theorem totalUpper_decomposition :
    areaUpper + (36 : ℚ) / (5 * 512) + 901 / 600 + 19 / 16 = totalUpper := by
  norm_num [areaUpper, totalUpper]

theorem totalUpper_lt : totalUpper < (5412 : ℚ) / 1000 := by
  norm_num [totalUpper]

#print axioms extended_profile_bound
#print axioms totalUpper_lt

end Zeta5.Certificate.ExtendedArithmetic
