import Zeta5.Certificate.AnalyticGrid
import Zeta5.Certificate.ArithmeticCells
import Zeta5.Certificate.UpperArithmetic

/-! Exact real-valued comparison of the two finite certificates. -/

namespace Zeta5.Certificate

noncomputable def analyticLowerValue : ℝ :=
  (analyticTotalNumerator : ℝ) / (4 * (fixedScale : ℝ) ^ 3)

theorem analyticLowerValue_gt_displayed :
    54133705070 / (10 : ℝ) ^ 10 < analyticLowerValue := by
  norm_num [analyticLowerValue, analyticTotalNumerator, fixedScale]

theorem analyticLowerValue_gt_threshold : (54133 : ℝ) / 10000 < analyticLowerValue := by
  norm_num [analyticLowerValue, analyticTotalNumerator, fixedScale]

theorem arithmeticTotal_real_lt : (arithmeticTotal : ℝ) < 54101 / 10000 := by
  norm_num [arithmeticTotal]

theorem finite_certificate_gap : (32 : ℝ) / 10000 < analyticLowerValue - arithmeticTotal := by
  norm_num [analyticLowerValue, analyticTotalNumerator, fixedScale, arithmeticTotal]

/-- Once a separate analytic argument bounds its target below by the
verified trapezoid certificate, the certified strict gap transfers to it. -/
theorem gap_of_analyticLowerValue_le (analytic : ℝ) (h : analyticLowerValue ≤ analytic) :
    (32 : ℝ) / 10000 < analytic - arithmeticTotal :=
  lt_of_lt_of_le finite_certificate_gap (sub_le_sub_right h _)

end Zeta5.Certificate
