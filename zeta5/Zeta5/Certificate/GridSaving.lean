import Zeta5.Certificate.GridSoundness
import Zeta5.Analysis.ProfileShape

/-! The validated finite node savings lie below the actual analytic profile. -/

namespace Zeta5.Certificate

namespace AnalyticNode

theorem first_argument {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    ((2 * c.vNumerator j : ℕ) : ℝ) / (gridB j : ℝ) =
      4 * ((1 / 20 : ℝ) + c.massLower j) / gridPoint j := by
  have hB : 0 < gridB j := h.2.2.2.2.2.2.2.1.1
  have hBr : (0 : ℝ) < gridB j := by exact_mod_cast hB
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h10 : ((fixedScale / 10 : ℕ) : ℝ) = (fixedScale : ℝ) / 10 := by norm_num [fixedScale]
  dsimp [vNumerator, massLower, gridPoint]
  push_cast
  rw [h10]
  field_simp
  ring

theorem second_argument {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    ((2 * c.vNumerator j : ℕ) : ℝ) / ((fixedScale / 20 + c.sqrtC + 1 : ℕ) : ℝ) =
      4 * ((1 / 20 : ℝ) + c.massLower j) /
        ((1 / 20 : ℝ) + (c.sqrtC + 1 : ℝ) / fixedScale) := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h10 : ((fixedScale / 10 : ℕ) : ℝ) = (fixedScale : ℝ) / 10 := by norm_num [fixedScale]
  have h20 : ((fixedScale / 20 : ℕ) : ℝ) = (fixedScale : ℝ) / 20 := by norm_num [fixedScale]
  dsimp [vNumerator, massLower]
  push_cast
  rw [h10, h20]
  field_simp
  ring

theorem third_argument {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    ((fixedScale + c.sqrtA : ℕ) : ℝ) / ((2 * fixedScale : ℕ) : ℝ) =
      (1 + (c.sqrtA : ℝ) / fixedScale) / 2 := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  push_cast
  field_simp

theorem savingLower_formula (j : ℕ) (c : AnalyticNode) :
    c.savingLower j =
      4 * c.massLower j * ((c.logOne.numerator : ℝ) / fixedScale) +
      4 * (1 / 20 : ℝ) * ((c.logTwo.numerator : ℝ) / fixedScale) +
      2 * ((c.logThree.numerator : ℝ) / fixedScale) := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h5 : ((fixedScale / 5 : ℕ) : ℝ) = (fixedScale : ℝ) / 5 := by norm_num [fixedScale]
  dsimp [savingLower, gNumerator, massLower]
  push_cast
  rw [h5]
  field_simp
  ring

theorem savingLower_le {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    c.savingLower j ≤ Zeta5.Analysis.analyticSaving (1 / 20) (by norm_num)
      (Zeta5.Analysis.profileMass (1 / 20) (gridPoint j)) := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hlog1 : c.logOne.Valid (2 * c.vNumerator j) (gridB j) := h.2.2.2.2.2.2.2.1
  have hlog2 : c.logTwo.Valid (2 * c.vNumerator j) (fixedScale / 20 + c.sqrtC + 1) :=
    h.2.2.2.2.2.2.2.2.1
  have hlog3 : c.logThree.Valid (fixedScale + c.sqrtA) (2 * fixedScale) :=
    h.2.2.2.2.2.2.2.2.2.1
  have hB : (0 : ℝ) < gridB j := by exact_mod_cast hlog1.1
  have hb : 0 < gridPoint j := by dsimp [gridPoint]; positivity
  have hL := c.massLower_pos h
  have hU := Zeta5.Analysis.profileMass_pos (by norm_num : (0 : ℝ) < 1 / 20) hb
  have hLU := (mass_interval h).1
  have hAI := sqrtA_interval h
  have hCI := sqrtC_interval h
  have h1 := LogBound.sound hlog1
  have h2 := LogBound.sound hlog2
  have h3 := LogBound.sound hlog3
  rw [first_argument h] at h1
  rw [second_argument h] at h2
  rw [third_argument h] at h3
  have h1' : (c.logOne.numerator : ℝ) / fixedScale ≤
      Real.log (4 * ((1 / 20 : ℝ) + Zeta5.Analysis.profileMass (1 / 20) (gridPoint j)) /
        gridPoint j) := by
    apply h1.trans
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  have h2' : (c.logTwo.numerator : ℝ) / fixedScale ≤
      Real.log (4 * ((1 / 20 : ℝ) + Zeta5.Analysis.profileMass (1 / 20) (gridPoint j)) /
        ((1 / 20 : ℝ) + Real.sqrt ((1 / 20 : ℝ) ^ 2 + gridPoint j ^ 2))) := by
    apply h2.trans
    apply Real.log_le_log (by positivity)
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith [hCI.2])
  have h3' : (c.logThree.numerator : ℝ) / fixedScale ≤
      Real.log ((1 + Real.sqrt (1 + gridPoint j ^ 2)) / 2) := by
    apply h3.trans
    apply Real.log_le_log (by positivity)
    linarith [hAI.1]
  rw [savingLower_formula, Zeta5.Analysis.analyticSaving_at_mass (1 / 20) (by norm_num) hb]
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul (by linarith) h1' (by positivity) (by positivity)
    · exact mul_le_mul_of_nonneg_left h2' (by norm_num)
  · exact mul_le_mul_of_nonneg_left h3' (by norm_num)

end AnalyticNode

theorem initialSaving_le :
    (initialGNumerator : ℝ) / (fixedScale : ℝ) ^ 2 ≤
      Zeta5.Analysis.analyticSaving (1 / 20) (by norm_num) 0 := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h5 : ((fixedScale / 5 : ℕ) : ℝ) = (fixedScale : ℝ) / 5 := by norm_num [fixedScale]
  rw [Zeta5.Analysis.analyticSaving_zero]
  have h := mul_le_mul_of_nonneg_left logTwoNumerator_lower (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have heq : (initialGNumerator : ℝ) / (fixedScale : ℝ) ^ 2 =
      (1 / 5 : ℝ) * ((logTwoNumerator : ℝ) / fixedScale) := by
    dsimp [initialGNumerator]
    push_cast
    rw [h5]
    field_simp
  rw [heq]
  nlinarith [h]

end Zeta5.Certificate
