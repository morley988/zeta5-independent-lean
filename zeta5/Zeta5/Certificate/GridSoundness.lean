import Zeta5.Certificate.GridDefinitions
import Zeta5.Analysis.Profile
import Mathlib.Tactic.NormNum

/-!
# Real meaning of the finite grid's integer checks

The finite witnesses are not trusted: their validated integer inequalities
are converted here into one-sided real logarithm bounds. These theorems do
not yet identify the trapezoid sum with the determinant's analytic rate.
-/

namespace Zeta5.Certificate

theorem fixedScale_pos : 0 < fixedScale := by norm_num [fixedScale]

theorem LogBound.sound {c : LogBound} {num den : ℕ} (h : c.Valid num den) :
    (c.numerator : ℝ) / fixedScale ≤ Real.log ((num : ℝ) / den) := by
  rcases h with ⟨hden, hlo, _hhi, hz, heq⟩
  have hD : (0 : ℝ) < den := by exact_mod_cast hden
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hP : (0 : ℝ) < 2 ^ c.exponent := by positivity
  have hDP : (0 : ℝ) < den * 2 ^ c.exponent := mul_pos hD hP
  have hloR : (den : ℝ) * 2 ^ c.exponent ≤ num := by exact_mod_cast hlo
  have hx : (1 : ℝ) ≤ (num : ℝ) / (den * 2 ^ c.exponent) :=
    (one_le_div hDP).2 hloR
  have hsum : (0 : ℝ) < num + den * 2 ^ c.exponent := by linarith
  have hzR : (c.z : ℝ) * (num + den * 2 ^ c.exponent) ≤
      fixedScale * ((num : ℝ) - den * 2 ^ c.exponent) := by
    exact_mod_cast hz
  have hzdiv : (c.z : ℝ) / fixedScale ≤
      ((num : ℝ) - den * 2 ^ c.exponent) / (num + den * 2 ^ c.exponent) := by
    apply (div_le_div_iff₀ hM hsum).2
    nlinarith only [hzR]
  have hratio :
      (((num : ℝ) / (den * 2 ^ c.exponent)) - 1) /
        (((num : ℝ) / (den * 2 ^ c.exponent)) + 1) =
      ((num : ℝ) - den * 2 ^ c.exponent) / (num + den * 2 ^ c.exponent) := by
    field_simp
  have hzarg : (c.z : ℝ) / fixedScale ≤
      (((num : ℝ) / (den * 2 ^ c.exponent)) - 1) /
        (((num : ℝ) / (den * 2 ^ c.exponent)) + 1) := by
    rw [hratio]
    exact hzdiv
  have hlog := roundedLogNumerator_le_log fixedScale c.z 24 fixedScale_pos hx hzarg
  have hlog2 := mul_le_mul_of_nonneg_left logTwoNumerator_lower
    (show (0 : ℝ) ≤ c.exponent by positivity)
  have hprod : (num : ℝ) / den =
      ((num : ℝ) / (den * 2 ^ c.exponent)) * 2 ^ c.exponent := by
    field_simp
  have hred : Real.log ((num : ℝ) / den) =
      Real.log ((num : ℝ) / (den * 2 ^ c.exponent)) + c.exponent * Real.log 2 := by
    rw [hprod, Real.log_mul (by linarith : (num : ℝ) / (den * 2 ^ c.exponent) ≠ 0)
      (ne_of_gt hP), Real.log_pow]
  rw [heq]
  push_cast
  rw [hred]
  calc
    ((roundedLogNumerator fixedScale c.z 24 : ℝ) + c.exponent * logTwoNumerator) / fixedScale
        = (roundedLogNumerator fixedScale c.z 24 : ℝ) / fixedScale +
          c.exponent * ((logTwoNumerator : ℝ) / fixedScale) := by ring
    _ ≤ _ := add_le_add hlog hlog2

noncomputable def gridPoint (j : ℕ) : ℝ := (gridB j : ℝ) / fixedScale

namespace AnalyticNode

noncomputable def massLower (j : ℕ) (c : AnalyticNode) : ℝ :=
  (c.uLower j : ℝ) / (2 * fixedScale)

noncomputable def massUpper (j : ℕ) (c : AnalyticNode) : ℝ :=
  (c.uUpper j : ℝ) / (2 * fixedScale)

noncomputable def savingLower (j : ℕ) (c : AnalyticNode) : ℝ :=
  (c.gNumerator j : ℝ) / (fixedScale : ℝ) ^ 2

theorem sqrtA_interval {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    (c.sqrtA : ℝ) / fixedScale ≤ Real.sqrt (1 + gridPoint j ^ 2) ∧
      Real.sqrt (1 + gridPoint j ^ 2) ≤ (c.sqrtA + 1 : ℝ) / fixedScale := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hlo : (c.sqrtA : ℝ) ^ 2 ≤ (fixedScale : ℝ) ^ 2 + (gridB j : ℝ) ^ 2 := by
    exact_mod_cast h.1
  have hhi : (fixedScale : ℝ) ^ 2 + (gridB j : ℝ) ^ 2 ≤ (c.sqrtA + 1 : ℝ) ^ 2 := by
    exact_mod_cast h.2.1
  apply sqrt_interval_of_squared_bounds (by positivity) (by positivity)
  · calc
      ((c.sqrtA : ℝ) / fixedScale) ^ 2 = (c.sqrtA : ℝ) ^ 2 / (fixedScale : ℝ) ^ 2 := div_pow _ _ _
      _ ≤ ((fixedScale : ℝ) ^ 2 + (gridB j : ℝ) ^ 2) / (fixedScale : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlo (sq_nonneg _)
      _ = 1 + gridPoint j ^ 2 := by dsimp [gridPoint]; field_simp
  · calc
      1 + gridPoint j ^ 2 = ((fixedScale : ℝ) ^ 2 + (gridB j : ℝ) ^ 2) / (fixedScale : ℝ) ^ 2 := by
        dsimp [gridPoint]; field_simp
      _ ≤ (c.sqrtA + 1 : ℝ) ^ 2 / (fixedScale : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hhi (sq_nonneg _)
      _ = ((c.sqrtA + 1 : ℝ) / fixedScale) ^ 2 := (div_pow _ _ _).symm

theorem sqrtC_interval {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    (c.sqrtC : ℝ) / fixedScale ≤ Real.sqrt ((1 / 20 : ℝ) ^ 2 + gridPoint j ^ 2) ∧
      Real.sqrt ((1 / 20 : ℝ) ^ 2 + gridPoint j ^ 2) ≤
        (c.sqrtC + 1 : ℝ) / fixedScale := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have heq : ((fixedScale ^ 2 / 400 : ℕ) : ℝ) = (fixedScale : ℝ) ^ 2 / 400 := by
    norm_num [fixedScale]
  have hlo : (c.sqrtC : ℝ) ^ 2 ≤ (fixedScale : ℝ) ^ 2 / 400 + (gridB j : ℝ) ^ 2 := by
    have hh : (c.sqrtC : ℝ) ^ 2 ≤ ((fixedScale ^ 2 / 400 : ℕ) : ℝ) + (gridB j : ℝ) ^ 2 := by
      exact_mod_cast h.2.2.1
    simpa only [heq] using hh
  have hhi : (fixedScale : ℝ) ^ 2 / 400 + (gridB j : ℝ) ^ 2 ≤ (c.sqrtC + 1 : ℝ) ^ 2 := by
    have hh : ((fixedScale ^ 2 / 400 : ℕ) : ℝ) + (gridB j : ℝ) ^ 2 ≤ (c.sqrtC + 1 : ℝ) ^ 2 := by
      exact_mod_cast h.2.2.2.1
    simpa only [heq] using hh
  apply sqrt_interval_of_squared_bounds (by positivity) (by positivity)
  · calc
      ((c.sqrtC : ℝ) / fixedScale) ^ 2 = (c.sqrtC : ℝ) ^ 2 / (fixedScale : ℝ) ^ 2 := div_pow _ _ _
      _ ≤ ((fixedScale : ℝ) ^ 2 / 400 + (gridB j : ℝ) ^ 2) / (fixedScale : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hlo (sq_nonneg _)
      _ = (1 / 20 : ℝ) ^ 2 + gridPoint j ^ 2 := by dsimp [gridPoint]; field_simp; ring
  · calc
      (1 / 20 : ℝ) ^ 2 + gridPoint j ^ 2 =
          ((fixedScale : ℝ) ^ 2 / 400 + (gridB j : ℝ) ^ 2) / (fixedScale : ℝ) ^ 2 := by
        dsimp [gridPoint]; field_simp; ring
      _ ≤ (c.sqrtC + 1 : ℝ) ^ 2 / (fixedScale : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hhi (sq_nonneg _)
      _ = ((c.sqrtC + 1 : ℝ) / fixedScale) ^ 2 := (div_pow _ _ _).symm

theorem massLower_formula {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    c.massLower j =
      (gridPoint j + 1 - 2 * (1 / 20 : ℝ) - (c.sqrtA + 1 : ℝ) / fixedScale +
        2 * ((c.sqrtC : ℝ) / fixedScale)) / 2 := by
  have hnat := h.2.2.2.2.1
  have hscale : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h9 : ((9 * fixedScale / 10 : ℕ) : ℝ) = 9 * (fixedScale : ℝ) / 10 := by
    norm_num [fixedScale]
  dsimp [massLower, uLower, gridPoint]
  rw [Nat.cast_sub hnat]
  push_cast
  rw [h9]
  field_simp
  ring

theorem massUpper_formula {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    c.massUpper j =
      (gridPoint j + 1 - 2 * (1 / 20 : ℝ) - (c.sqrtA : ℝ) / fixedScale +
        2 * ((c.sqrtC + 1 : ℝ) / fixedScale)) / 2 := by
  have hnat : c.sqrtA ≤ gridB j + 9 * fixedScale / 10 + 2 * (c.sqrtC + 1) := by
    have hh := h.2.2.2.2.1
    omega
  have hscale : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have h9 : ((9 * fixedScale / 10 : ℕ) : ℝ) = 9 * (fixedScale : ℝ) / 10 := by
    norm_num [fixedScale]
  dsimp [massUpper, uUpper, gridPoint]
  rw [Nat.cast_sub hnat]
  push_cast
  rw [h9]
  field_simp
  ring

theorem mass_interval {j : ℕ} {c : AnalyticNode} (h : c.Valid j) :
    c.massLower j ≤ Zeta5.Analysis.profileMass (1 / 20) (gridPoint j) ∧
      Zeta5.Analysis.profileMass (1 / 20) (gridPoint j) ≤ c.massUpper j := by
  have ha := sqrtA_interval h
  have hc := sqrtC_interval h
  rw [massLower_formula h, massUpper_formula h]
  dsimp [Zeta5.Analysis.profileMass]
  constructor <;> linarith

theorem massLower_pos {j : ℕ} {c : AnalyticNode} (h : c.Valid j) : 0 < c.massLower j := by
  have hu : 0 < c.uLower j := h.2.2.2.2.2.1
  have hscale : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  dsimp [massLower]
  positivity

theorem savingLower_pos {j : ℕ} {c : AnalyticNode} (h : c.Valid j) : 0 < c.savingLower j := by
  have hg : 0 < c.gNumerator j := h.2.2.2.2.2.2.2.2.2.2
  have hscale : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  dsimp [savingLower]
  positivity

end AnalyticNode

theorem checkAnalyticNodes_cons_iff (start previousUpper : ℕ) (node : AnalyticNode)
    (rest : List AnalyticNode) :
    checkAnalyticNodes start previousUpper (node :: rest) = true ↔
      node.Valid start ∧ previousUpper < node.uLower start ∧
        checkAnalyticNodes (start + 1) (node.uUpper start) rest = true := by
  simp [checkAnalyticNodes, and_assoc]

end Zeta5.Certificate
