import Zeta5.Analysis.PhysicalMeasureCauchyFourth

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Zeta5.Analysis

open MeasureTheory Filter Set Real
open scoped Topology

def fourthCauchyPrimitive (b x : ℝ) : ℝ :=
  (24 / b ^ 5) * arctan (x / b) + (24 / b ^ 4) * cauchyAtom b 1 x +
    (16 / b ^ 2) * cauchyAtom b 2 x + 8 * cauchyAtom b 3 x +
    (48 * b ^ 2) * cauchyAtom b 4 x

theorem hasDerivAt_fourthCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (fourthCauchyPrimitive b) (fourthCauchyKernel b x) x := by
  unfold fourthCauchyPrimitive
  have h := (((((hasDerivAt_arctan_div hb x).const_mul (24 / b ^ 5)).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul (24 / b ^ 4))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul (16 / b ^ 2))).add
    ((hasDerivAt_cauchyAtom hb 3 x).const_mul 8)).add
    ((hasDerivAt_cauchyAtom hb 4 x).const_mul (48 * b ^ 2))
  apply h.congr_deriv
  unfold fourthCauchyKernel
  norm_num
  field_simp [hb.ne', ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_fourthCauchyPrimitive {b : ℝ} (hb : 0 < b) :
    Tendsto (fourthCauchyPrimitive b) atTop (𝓝 (12 * π / b ^ 5)) := by
  unfold fourthCauchyPrimitive
  have h := (((((tendsto_arctan_div hb).const_mul (24 / b ^ 5)).add
    ((tendsto_cauchyAtom hb 0).const_mul (24 / b ^ 4))).add
    ((tendsto_cauchyAtom hb 1).const_mul (16 / b ^ 2))).add
    ((tendsto_cauchyAtom hb 2).const_mul 8)).add
    ((tendsto_cauchyAtom hb 3).const_mul (48 * b ^ 2))
  simp only [mul_zero, add_zero] at h
  have he : (24 / b ^ 5) * (π / 2) = 12 * π / b ^ 5 := by ring
  rwa [he] at h

theorem fourthCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, fourthCauchyKernel b x = 12 * π / b ^ 5 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_fourthCauchyPrimitive hb x)
    (fourthCauchyKernel_integrableOn hb) (tendsto_fourthCauchyPrimitive hb)
  simpa [fourthCauchyPrimitive, cauchyAtom] using h

def cauchyInvAtom (b : ℝ) (k : ℕ) (x : ℝ) : ℝ := ((x ^ 2 + b ^ 2)⁻¹) ^ k

theorem hasDerivAt_cauchyInvAtom {b : ℝ} (hb : 0 < b) (k : ℕ) (x : ℝ) :
    HasDerivAt (cauchyInvAtom b k)
      ((k : ℝ) * ((x ^ 2 + b ^ 2)⁻¹) ^ (k - 1) *
        (-(2 * x) / (x ^ 2 + b ^ 2) ^ 2)) x := by
  unfold cauchyInvAtom
  apply (((((hasDerivAt_id x).pow 2).add_const (b ^ 2)).inv
    (ne_of_gt (cauchy_den_pos hb x))).pow k).congr_deriv
  simp only [id_eq, Pi.pow_apply, Pi.inv_apply]
  ring

theorem tendsto_cauchyInvAtom (b : ℝ) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (cauchyInvAtom b k) atTop (𝓝 0) := by
  unfold cauchyInvAtom
  simpa only [zero_pow hk] using (tendsto_inv_cauchy b).pow k

def linearFourthCauchyPrimitive (b x : ℝ) : ℝ :=
  -6 * cauchyInvAtom b 2 x + (48 * b ^ 2) * cauchyInvAtom b 3 x -
    (48 * b ^ 4) * cauchyInvAtom b 4 x

theorem hasDerivAt_linearFourthCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (linearFourthCauchyPrimitive b) (x * fourthCauchyKernel b x) x := by
  unfold linearFourthCauchyPrimitive
  have h := (((hasDerivAt_cauchyInvAtom hb 2 x).const_mul (-6)).add
    ((hasDerivAt_cauchyInvAtom hb 3 x).const_mul (48 * b ^ 2))).sub
    ((hasDerivAt_cauchyInvAtom hb 4 x).const_mul (48 * b ^ 4))
  apply h.congr_deriv
  unfold fourthCauchyKernel
  norm_num
  field_simp [ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_linearFourthCauchyPrimitive {b : ℝ} :
    Tendsto (linearFourthCauchyPrimitive b) atTop (𝓝 0) := by
  unfold linearFourthCauchyPrimitive
  have h := (((tendsto_cauchyInvAtom b (by decide : 2 ≠ 0)).const_mul (-6)).add
    ((tendsto_cauchyInvAtom b (by decide : 3 ≠ 0)).const_mul (48 * b ^ 2))).sub
    ((tendsto_cauchyInvAtom b (by decide : 4 ≠ 0)).const_mul (48 * b ^ 4))
  simpa using h

theorem linear_fourthCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x * fourthCauchyKernel b x = 6 / b ^ 4 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_linearFourthCauchyPrimitive hb x)
    (linear_fourthCauchyKernel_integrableOn hb) tendsto_linearFourthCauchyPrimitive
  rw [h]
  unfold linearFourthCauchyPrimitive cauchyInvAtom
  norm_num
  field_simp [hb.ne']
  ring

def repeatedFourthCauchyPrimitive (b x : ℝ) : ℝ :=
  (3 / (4 * b ^ 5)) * arctan (x / b) + (3 / (4 * b ^ 4)) * cauchyAtom b 1 x +
    (1 / (2 * b ^ 2)) * cauchyAtom b 2 x - (22 / 5) * cauchyAtom b 3 x +
    (204 * b ^ 2 / 5) * cauchyAtom b 4 x - (192 * b ^ 4 / 5) * cauchyAtom b 5 x

theorem hasDerivAt_repeatedFourthCauchyPrimitive {b : ℝ} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (repeatedFourthCauchyPrimitive b)
      (x ^ 2 / (x ^ 2 + b ^ 2) * fourthCauchyKernel b x) x := by
  unfold repeatedFourthCauchyPrimitive
  have h := ((((((hasDerivAt_arctan_div hb x).const_mul (3 / (4 * b ^ 5))).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul (3 / (4 * b ^ 4)))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul (1 / (2 * b ^ 2)))).sub
    ((hasDerivAt_cauchyAtom hb 3 x).const_mul (22 / 5))).add
    ((hasDerivAt_cauchyAtom hb 4 x).const_mul (204 * b ^ 2 / 5))).sub
    ((hasDerivAt_cauchyAtom hb 5 x).const_mul (192 * b ^ 4 / 5))
  apply h.congr_deriv
  unfold fourthCauchyKernel
  norm_num
  field_simp [hb.ne', ne_of_gt (cauchy_den_pos hb x)]
  ring

theorem tendsto_repeatedFourthCauchyPrimitive {b : ℝ} (hb : 0 < b) :
    Tendsto (repeatedFourthCauchyPrimitive b) atTop (𝓝 (12 * π / (b + b) ^ 5)) := by
  unfold repeatedFourthCauchyPrimitive
  have h := ((((((tendsto_arctan_div hb).const_mul (3 / (4 * b ^ 5))).add
    ((tendsto_cauchyAtom hb 0).const_mul (3 / (4 * b ^ 4)))).add
    ((tendsto_cauchyAtom hb 1).const_mul (1 / (2 * b ^ 2)))).sub
    ((tendsto_cauchyAtom hb 2).const_mul (22 / 5))).add
    ((tendsto_cauchyAtom hb 3).const_mul (204 * b ^ 2 / 5))).sub
    ((tendsto_cauchyAtom hb 4).const_mul (192 * b ^ 4 / 5))
  simp only [mul_zero, add_zero, sub_zero] at h
  have he : (3 / (4 * b ^ 5)) * (π / 2) = 12 * π / (b + b) ^ 5 := by ring
  rwa [he] at h

theorem repeated_fourthCauchyKernel_integral {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x ^ 2 / (x ^ 2 + b ^ 2) * fourthCauchyKernel b x =
      12 * π / (b + b) ^ 5 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => hasDerivAt_repeatedFourthCauchyPrimitive hb x)
    (product_fourthCauchyKernel_integrableOn hb hb) (tendsto_repeatedFourthCauchyPrimitive hb)
  simpa [repeatedFourthCauchyPrimitive, cauchyAtom] using h

def distinctFourthCauchyPrimitive (a b x : ℝ) : ℝ :=
  (24 * a * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 5) * arctan (x / a) +
  (-24 * b * (5 * a ^ 4 + 10 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 5) * arctan (x / b) +
  (24 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 4) * cauchyAtom b 1 x +
  (-8 * (a ^ 4 + 9 * a ^ 2 * b ^ 2 + 2 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 3) * cauchyAtom b 2 x +
  (8 * b ^ 2 * (7 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2) * cauchyAtom b 3 x +
  (-48 * b ^ 4 / (a ^ 2 - b ^ 2)) * cauchyAtom b 4 x

set_option maxHeartbeats 2000000 in
theorem hasDerivAt_distinctFourthCauchyPrimitive {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (x : ℝ) :
    HasDerivAt (distinctFourthCauchyPrimitive a b)
      (x ^ 2 / (x ^ 2 + a ^ 2) * fourthCauchyKernel b x) x := by
  unfold distinctFourthCauchyPrimitive
  have h := ((((((hasDerivAt_arctan_div ha x).const_mul
    (24 * a * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 5)).add
    ((hasDerivAt_arctan_div hb x).const_mul
      (-24 * b * (5 * a ^ 4 + 10 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 5))).add
    ((hasDerivAt_cauchyAtom hb 1 x).const_mul
      (24 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 4))).add
    ((hasDerivAt_cauchyAtom hb 2 x).const_mul
      (-8 * (a ^ 4 + 9 * a ^ 2 * b ^ 2 + 2 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 3))).add
    ((hasDerivAt_cauchyAtom hb 3 x).const_mul
      (8 * b ^ 2 * (7 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2))).add
    ((hasDerivAt_cauchyAtom hb 4 x).const_mul (-48 * b ^ 4 / (a ^ 2 - b ^ 2)))
  apply h.congr_deriv
  unfold fourthCauchyKernel
  norm_num
  field_simp [ne_of_gt (cauchy_den_pos ha x), ne_of_gt (cauchy_den_pos hb x),
    cauchy_square_sub_ne_zero hb ha hab.symm]
  ring

theorem tendsto_distinctFourthCauchyPrimitive {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Tendsto (distinctFourthCauchyPrimitive a b) atTop (𝓝 (12 * π / (a + b) ^ 5)) := by
  unfold distinctFourthCauchyPrimitive
  have h := ((((((tendsto_arctan_div ha).const_mul
    (24 * a * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 5)).add
    ((tendsto_arctan_div hb).const_mul
      (-24 * b * (5 * a ^ 4 + 10 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 5))).add
    ((tendsto_cauchyAtom hb 0).const_mul
      (24 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 4))).add
    ((tendsto_cauchyAtom hb 1).const_mul
      (-8 * (a ^ 4 + 9 * a ^ 2 * b ^ 2 + 2 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 3))).add
    ((tendsto_cauchyAtom hb 2).const_mul
      (8 * b ^ 2 * (7 * a ^ 2 + b ^ 2) / (a ^ 2 - b ^ 2) ^ 2))).add
    ((tendsto_cauchyAtom hb 3).const_mul (-48 * b ^ 4 / (a ^ 2 - b ^ 2)))
  simp only [mul_zero, add_zero] at h
  have he : (24 * a * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) / (a ^ 2 - b ^ 2) ^ 5) * (π / 2) +
      (-24 * b * (5 * a ^ 4 + 10 * a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 - b ^ 2) ^ 5) * (π / 2) =
        12 * π / (a + b) ^ 5 := by
    field_simp [ne_of_gt (add_pos ha hb), cauchy_square_sub_ne_zero hb ha hab.symm]
    ring
  rwa [he] at h

/-- The fourth Cauchy integral, including coincident parameters. -/
theorem product_fourthCauchyKernel_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x ^ 2 / (x ^ 2 + a ^ 2) * fourthCauchyKernel b x =
      12 * π / (a + b) ^ 5 := by
  by_cases hab : a = b
  · subst b
    exact repeated_fourthCauchyKernel_integral ha
  · have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
      (fun x _ => hasDerivAt_distinctFourthCauchyPrimitive ha hb hab x)
      (product_fourthCauchyKernel_integrableOn ha hb) (tendsto_distinctFourthCauchyPrimitive ha hb hab)
    simpa [distinctFourthCauchyPrimitive, cauchyAtom] using h

end Zeta5.Analysis
