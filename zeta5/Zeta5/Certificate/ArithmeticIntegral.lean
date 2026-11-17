import Zeta5.Certificate.ArithmeticProfile
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrating the certified affine rank profile, with endpoint jumps ignored. -/

namespace Zeta5.Certificate

open MeasureTheory Set

namespace ArithmeticCell

theorem profile_intervalIntegrable {c : ArithmeticCell} (h : c.Valid) :
    IntervalIntegrable middleRankProfile volume (c.lo : ℝ) (c.hi : ℝ) := by
  have hle : (c.lo : ℝ) ≤ (c.hi : ℝ) := by exact_mod_cast h.2.1.le
  have hcont : Continuous (fun β : ℝ => (c.intercept : ℝ) + (c.slope : ℝ) * β) := by
    fun_prop
  apply (hcont.intervalIntegrable _ _).congr_uIoo
  intro β hβ
  rw [uIoo_of_le hle] at hβ
  exact (profile_affine h hβ.1 hβ.2).symm

theorem integral_profile {c : ArithmeticCell} (h : c.Valid) :
    (∫ β in (c.lo : ℝ)..(c.hi : ℝ), middleRankProfile β) = (c.area : ℝ) := by
  have hle : (c.lo : ℝ) ≤ (c.hi : ℝ) := by exact_mod_cast h.2.1.le
  calc
    (∫ β in (c.lo : ℝ)..(c.hi : ℝ), middleRankProfile β) =
        ∫ β in (c.lo : ℝ)..(c.hi : ℝ), (c.intercept : ℝ) + (c.slope : ℝ) * β := by
      apply intervalIntegral.integral_congr_Ioo_of_le hle
      intro β hβ
      exact profile_affine h hβ.1 hβ.2
    _ = (c.area : ℝ) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_id.const_mul _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul, integral_id]
      simp only [smul_eq_mul, area, Rat.cast_mul, Rat.cast_sub, Rat.cast_add,
        Rat.cast_div, Rat.cast_ofNat]
      ring

end ArithmeticCell

def arithmeticChainFits (start : ℚ) : List ArithmeticCell → Prop
  | [] => True
  | c :: cs => c.lo = start ∧ c.Valid ∧ arithmeticChainFits c.hi cs

def arithmeticChainEnd (start : ℚ) : List ArithmeticCell → ℚ
  | [] => start
  | c :: cs => arithmeticChainEnd c.hi cs

theorem integrate_arithmeticChain {cells : List ArithmeticCell} {start : ℚ}
    (h : arithmeticChainFits start cells) :
    IntervalIntegrable middleRankProfile volume (start : ℝ) (arithmeticChainEnd start cells : ℝ) ∧
    (∫ β in (start : ℝ)..(arithmeticChainEnd start cells : ℝ), middleRankProfile β) =
      ((cells.map ArithmeticCell.area).sum : ℝ) := by
  induction cells generalizing start with
  | nil => simp [arithmeticChainEnd]
  | cons c cs ih =>
    rcases h with ⟨hstart, hc, hrest⟩
    subst start
    have hcell := ArithmeticCell.profile_intervalIntegrable hc
    have htail := ih hrest
    constructor
    · exact hcell.trans htail.1
    · change (∫ β in (c.lo : ℝ)..(arithmeticChainEnd c.hi cs : ℝ), middleRankProfile β) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals hcell htail.1,
        ArithmeticCell.integral_profile hc, htail.2]
      simp

end Zeta5.Certificate
