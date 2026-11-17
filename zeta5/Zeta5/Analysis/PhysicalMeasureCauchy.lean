import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Cauchy integrals on the positive half-line

These equalities use explicit real antiderivatives, including the repeated
pole case.  They require no exchange of a parameter derivative and an
improper integral.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Zeta5.Analysis

open MeasureTheory Filter Set Real
open scoped Topology

theorem cauchy_den_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < x ^ 2 + a ^ 2 := by
  positivity

theorem hasDerivAt_arctan_div {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun x : ℝ => arctan (x / a)) (a / (x ^ 2 + a ^ 2)) x := by
  apply ((hasDerivAt_id x).div_const a).arctan.congr_deriv
  simp only [id_eq]
  have hd := ne_of_gt (cauchy_den_pos ha x)
  have he : 1 + (x / a) ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hd, he]
  ring

theorem tendsto_arctan_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => arctan (x / a)) atTop (𝓝 (π / 2)) := by
  exact (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)

theorem tendsto_linear_div_cauchy {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x / (x ^ 2 + a ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    calc
      x / (x ^ 2 + a ^ 2) ≤ x / x ^ 2 :=
        div_le_div_of_nonneg_left hx.le (by positivity) (le_add_of_nonneg_right (sq_nonneg a))
      _ = x⁻¹ := by field_simp

def cauchyProduct (a b x : ℝ) : ℝ := x ^ 2 / ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2))

def cauchyPrimitiveDistinct (a b x : ℝ) : ℝ :=
  (b * arctan (x / b) - a * arctan (x / a)) / (b ^ 2 - a ^ 2)

theorem cauchy_square_sub_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    b ^ 2 - a ^ 2 ≠ 0 := by
  intro h
  have hm : (b - a) * (b + a) = 0 := by nlinarith
  rcases mul_eq_zero.mp hm with h | h
  · exact hab (sub_eq_zero.mp h).symm
  · linarith

theorem hasDerivAt_cauchyPrimitiveDistinct {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (x : ℝ) :
    HasDerivAt (cauchyPrimitiveDistinct a b) (cauchyProduct a b x) x := by
  have h := (((hasDerivAt_arctan_div hb x).const_mul b).sub
    ((hasDerivAt_arctan_div ha x).const_mul a)).div_const (b ^ 2 - a ^ 2)
  apply h.congr_deriv
  unfold cauchyProduct
  field_simp [ne_of_gt (cauchy_den_pos ha x), ne_of_gt (cauchy_den_pos hb x),
    cauchy_square_sub_ne_zero ha hb hab]
  ring

theorem tendsto_cauchyPrimitiveDistinct {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Tendsto (cauchyPrimitiveDistinct a b) atTop (𝓝 (π / (2 * (a + b)))) := by
  have h := (((tendsto_arctan_div hb).const_mul b).sub
    ((tendsto_arctan_div ha).const_mul a)).div_const (b ^ 2 - a ^ 2)
  have hs : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have he : (b * (π / 2) - a * (π / 2)) / (b ^ 2 - a ^ 2) = π / (2 * (a + b)) := by
    field_simp [hs, cauchy_square_sub_ne_zero ha hb hab]
    ring
  unfold cauchyPrimitiveDistinct
  rw [he] at h
  exact h

def cauchyPrimitiveRepeated (a x : ℝ) : ℝ :=
  (arctan (x / a) - a * (x / (x ^ 2 + a ^ 2))) / (2 * a)

theorem hasDerivAt_cauchyPrimitiveRepeated {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (cauchyPrimitiveRepeated a) (cauchyProduct a a x) x := by
  have hd : HasDerivAt (fun x : ℝ => x / (x ^ 2 + a ^ 2))
      ((x ^ 2 + a ^ 2 - x * (2 * x)) / (x ^ 2 + a ^ 2) ^ 2) x := by
    apply ((hasDerivAt_id x).div (((hasDerivAt_id x).pow 2).add_const (a ^ 2))
      (ne_of_gt (cauchy_den_pos ha x))).congr_deriv
    simp only [id_eq, Pi.pow_apply]
    ring
  have h := ((hasDerivAt_arctan_div ha x).sub (hd.const_mul a)).div_const (2 * a)
  apply h.congr_deriv
  unfold cauchyProduct
  field_simp [ne_of_gt (cauchy_den_pos ha x), ha.ne']
  ring

theorem tendsto_cauchyPrimitiveRepeated {a : ℝ} (ha : 0 < a) :
    Tendsto (cauchyPrimitiveRepeated a) atTop (𝓝 (π / (2 * (a + a)))) := by
  have h := ((tendsto_arctan_div ha).sub
    ((tendsto_linear_div_cauchy ha).const_mul a)).div_const (2 * a)
  have he : (π / 2 - a * 0) / (2 * a) = π / (2 * (a + a)) := by ring
  unfold cauchyPrimitiveRepeated
  rw [he] at h
  exact h

theorem cauchyProduct_nonneg (a b x : ℝ) : 0 ≤ cauchyProduct a b x := by
  unfold cauchyProduct
  positivity

theorem cauchyProduct_integrableOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (cauchyProduct a b) (Ioi 0) := by
  by_cases hab : a = b
  · subst b
    exact integrableOn_Ioi_deriv_of_nonneg'
      (fun x _ => hasDerivAt_cauchyPrimitiveRepeated ha x)
      (fun x _ => cauchyProduct_nonneg a a x) (tendsto_cauchyPrimitiveRepeated ha)
  · exact integrableOn_Ioi_deriv_of_nonneg'
      (fun x _ => hasDerivAt_cauchyPrimitiveDistinct ha hb hab x)
      (fun x _ => cauchyProduct_nonneg a b x) (tendsto_cauchyPrimitiveDistinct ha hb hab)

theorem cauchyProduct_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, cauchyProduct a b x = π / (2 * (a + b)) := by
  by_cases hab : a = b
  · subst b
    simpa [cauchyPrimitiveRepeated] using integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
      (fun x _ => hasDerivAt_cauchyPrimitiveRepeated ha x)
      (fun x _ => cauchyProduct_nonneg a a x) (tendsto_cauchyPrimitiveRepeated ha)
  · simpa [cauchyPrimitiveDistinct] using integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
      (fun x _ => hasDerivAt_cauchyPrimitiveDistinct ha hb hab x)
      (fun x _ => cauchyProduct_nonneg a b x) (tendsto_cauchyPrimitiveDistinct ha hb hab)

end Zeta5.Analysis
