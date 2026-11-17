import Zeta5.Certificate.ArithmeticIntegral

/-! A fixed finite cutoff replaces the infinite-period arithmetic tail.
Every cell uses the existing exact floor/branch certificate. Its area is
bounded above by a rational with a common denominator, keeping the kernel
calculation small while retaining a strict final gap. -/

namespace Zeta5.Certificate.ExtendedArithmetic
open MeasureTheory

def cappedChainFits (start : ℚ) : List (ArithmeticCell × ℚ) → Prop
  | [] => True
  | (c, u) :: cs => c.lo = start ∧ c.Valid ∧ c.area ≤ u ∧ cappedChainFits c.hi cs

def cappedChainEnd (start : ℚ) : List (ArithmeticCell × ℚ) → ℚ
  | [] => start
  | (c, _) :: cs => cappedChainEnd c.hi cs

def cappedChainUpper : List (ArithmeticCell × ℚ) → ℚ
  | [] => 0
  | (_, u) :: cs => u + cappedChainUpper cs

theorem integrate_cappedChain {cells : List (ArithmeticCell × ℚ)} {start : ℚ}
    (h : cappedChainFits start cells) :
    IntervalIntegrable middleRankProfile volume (start : ℝ) (cappedChainEnd start cells : ℝ) ∧
    (∫ β in (start : ℝ)..(cappedChainEnd start cells : ℝ), middleRankProfile β) ≤
      (cappedChainUpper cells : ℝ) := by
  induction cells generalizing start with
  | nil => simp [cappedChainEnd, cappedChainUpper]
  | cons cu cs ih =>
    rcases cu with ⟨c, u⟩
    rcases h with ⟨hstart, hc, hu, hrest⟩
    subst start
    have hcell := ArithmeticCell.profile_intervalIntegrable hc
    have htail := ih hrest
    constructor
    · exact hcell.trans htail.1
    · change (∫ β in (c.lo : ℝ)..(cappedChainEnd c.hi cs : ℝ), middleRankProfile β) ≤ _
      rw [← intervalIntegral.integral_add_adjacent_intervals hcell htail.1,
        ArithmeticCell.integral_profile hc]
      change (c.area : ℝ) + _ ≤ ((u + cappedChainUpper cs : ℚ) : ℝ)
      rw [Rat.cast_add]
      exact add_le_add (by exact_mod_cast hu) htail.2

theorem append_profile_bounds {a b c A B : ℚ}
    (h1 : IntervalIntegrable middleRankProfile volume (a : ℝ) (b : ℝ) ∧
      (∫ β in (a : ℝ)..(b : ℝ), middleRankProfile β) ≤ (A : ℝ))
    (h2 : IntervalIntegrable middleRankProfile volume (b : ℝ) (c : ℝ) ∧
      (∫ β in (b : ℝ)..(c : ℝ), middleRankProfile β) ≤ (B : ℝ)) :
    IntervalIntegrable middleRankProfile volume (a : ℝ) (c : ℝ) ∧
      (∫ β in (a : ℝ)..(c : ℝ), middleRankProfile β) ≤ ((A + B : ℚ) : ℝ) := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1, Rat.cast_add]
  exact add_le_add h1.2 h2.2

end Zeta5.Certificate.ExtendedArithmetic
