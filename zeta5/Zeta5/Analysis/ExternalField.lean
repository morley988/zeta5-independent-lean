import Zeta5.Analysis.EquilibriumKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The actual logarithmic external field and its slope -/

noncomputable section
namespace Zeta5.Analysis
open Real Set MeasureTheory Filter
open scoped Topology

def externalIntegral (a y : ℝ) : ℝ := ∫ t in 0..a, Real.log (y ^ 2 + t ^ 2)

def externalIntegralFormula (a y : ℝ) : ℝ :=
  a * Real.log (y ^ 2 + a ^ 2) - 2 * a + Real.pi * y - 2 * y * Real.arctan (y / a)

def externalField (s y : ℝ) : ℝ :=
  2 * Real.pi * y + externalIntegral 1 y - 2 * externalIntegral s y

private theorem hasDerivAt_logQuadraticPrimitive {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.log (y ^ 2 + t ^ 2) - 2 * t +
      2 * y * Real.arctan (t / y)) (Real.log (y ^ 2 + t ^ 2)) t := by
  have hd : y ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < y ^ 2 + t ^ 2)
  have h := ((((hasDerivAt_id t).mul
    ((((hasDerivAt_id t).pow 2).const_add (y ^ 2)).log hd)).sub
      ((hasDerivAt_id t).const_mul 2)).add
        ((((hasDerivAt_id t).div_const y).arctan).const_mul (2 * y)))
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp [hy.ne', hd]
  ring

theorem externalIntegral_integrable (a : ℝ) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun t : ℝ => Real.log (y ^ 2 + t ^ 2)) volume 0 a := by
  apply Continuous.intervalIntegrable
  exact (continuous_const.add (continuous_id.pow 2)).log
    (fun t => ne_of_gt (by positivity : 0 < y ^ 2 + t ^ 2))

theorem externalIntegral_formula {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    externalIntegral a y = externalIntegralFormula a y := by
  rcases eq_or_lt_of_le hy with rfl | hy
  · unfold externalIntegral externalIntegralFormula
    simp only [zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero, zero_div,
      arctan_zero, sub_zero, add_zero, Real.log_pow]
    rw [intervalIntegral.integral_const_mul, integral_log_from_zero]
    ring
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_logQuadraticPrimitive hy t) (externalIntegral_integrable a hy)
    change externalIntegral a y = _ at h
    have hinv : a / y = (y / a)⁻¹ := by rw [inv_div]
    rw [h]
    simp only [zero_mul, zero_div, arctan_zero, mul_zero, sub_zero, add_zero]
    rw [hinv, Real.arctan_inv_of_pos (div_pos hy ha)]
    unfold externalIntegralFormula
    ring

theorem externalIntegralFormula_hasDerivAt {a : ℝ} (ha : 0 < a) (y : ℝ) :
    HasDerivAt (externalIntegralFormula a) (Real.pi - 2 * Real.arctan (y / a)) y := by
  have hd : y ^ 2 + a ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < y ^ 2 + a ^ 2)
  have h := (((((((hasDerivAt_id y).pow 2).add_const (a ^ 2)).log hd).const_mul a).sub_const
    (2 * a)).add ((hasDerivAt_id y).const_mul Real.pi)).sub
      (((hasDerivAt_id y).const_mul 2).mul (((hasDerivAt_id y).div_const a).arctan))
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp [ha.ne', hd]
  ring

theorem externalIntegralFormula_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (externalIntegralFormula a) :=
  continuous_iff_continuousAt.mpr (fun y => (externalIntegralFormula_hasDerivAt ha y).continuousAt)

theorem externalField_zero {s : ℝ} (hs : 0 < s) :
    externalField s 0 = -2 - 4 * s * Real.log s + 4 * s := by
  rw [externalField, externalIntegral_formula (by norm_num) le_rfl,
    externalIntegral_formula hs le_rfl]
  simp only [externalIntegralFormula, zero_pow (by decide : 2 ≠ 0), zero_add,
    one_pow, Real.log_one, one_mul, mul_zero, sub_zero, add_zero, Real.log_pow]
  ring

/-- The exact identity connecting the real integral field with the auxiliary
potential's slope. The endpoint y=0 is included. -/
theorem externalField_sub_zero {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    externalField s y - externalField s 0 = 4 * ∫ t in 0..y, equilibriumSlope s t := by
  let F : ℝ → ℝ := fun t => 2 * Real.pi * t + externalIntegralFormula 1 t -
    2 * externalIntegralFormula s t
  have hF (t : ℝ) : HasDerivAt F (4 * equilibriumSlope s t) t := by
    have h := (((hasDerivAt_id t).const_mul (2 * Real.pi)).add
      (externalIntegralFormula_hasDerivAt (by norm_num : (0 : ℝ) < 1) t)).sub
        ((externalIntegralFormula_hasDerivAt hs t).const_mul 2)
    apply h.congr_deriv
    dsimp [equilibriumSlope]
    rw [div_one]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    (((equilibriumSlope_continuous s).const_mul 4).intervalIntegrable 0 y)
  rw [intervalIntegral.integral_const_mul] at hint
  have hyF : F y = externalField s y := by
    simp only [F, externalField, externalIntegral_formula (by norm_num : (0 : ℝ) < 1) hy,
      externalIntegral_formula hs hy]
  have h0F : F 0 = externalField s 0 := by
    simp only [F, externalField, externalIntegral_formula (by norm_num : (0 : ℝ) < 1) le_rfl,
      externalIntegral_formula hs le_rfl]
  rw [hyF, h0F] at hint
  exact hint.symm

end Zeta5.Analysis
