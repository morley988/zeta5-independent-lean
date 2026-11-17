import Zeta5.Analysis.PhysicalMeasureCauchy

/-!
# The fourth Cauchy kernel

Explicit antiderivatives prove the fourth-kernel identities needed for the
Stieltjes transform.  All improper-integral exchanges are avoided here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Zeta5.Analysis

open MeasureTheory Filter Set Real
open scoped Topology

def fourthCauchyKernel (b x : ℝ) : ℝ :=
  24 * (x ^ 4 - 10 * x ^ 2 * b ^ 2 + 5 * b ^ 4) / (x ^ 2 + b ^ 2) ^ 5

def cauchyAtom (b : ℝ) (k : ℕ) (x : ℝ) : ℝ := x / (x ^ 2 + b ^ 2) ^ k

theorem tendsto_inv_cauchy (b : ℝ) :
    Tendsto (fun x : ℝ => (x ^ 2 + b ^ 2)⁻¹) atTop (𝓝 0) := by
  apply Filter.Tendsto.inv_tendsto_atTop
  exact tendsto_atTop_mono (fun x : ℝ => le_add_of_nonneg_right (sq_nonneg b))
    (tendsto_pow_atTop (by decide : 2 ≠ 0))

theorem tendsto_cauchyAtom {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Tendsto (cauchyAtom b (n + 1)) atTop (𝓝 0) := by
  have he : cauchyAtom b (n + 1) =
      fun x : ℝ => (x / (x ^ 2 + b ^ 2)) * ((x ^ 2 + b ^ 2)⁻¹) ^ n := by
    funext x
    simp only [cauchyAtom, pow_succ, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  rw [he]
  simpa using (tendsto_linear_div_cauchy hb).mul ((tendsto_inv_cauchy b).pow n)

theorem hasDerivAt_cauchyAtom {b : ℝ} (hb : 0 < b) (k : ℕ) (x : ℝ) :
    HasDerivAt (cauchyAtom b k)
      (((x ^ 2 + b ^ 2) ^ k - x * ((k : ℝ) * (x ^ 2 + b ^ 2) ^ (k - 1) * (2 * x))) /
        ((x ^ 2 + b ^ 2) ^ k) ^ 2) x := by
  unfold cauchyAtom
  apply ((hasDerivAt_id x).div ((((hasDerivAt_id x).pow 2).add_const (b ^ 2)).pow k)
    (pow_ne_zero k (ne_of_gt (cauchy_den_pos hb x)))).congr_deriv
  simp only [id_eq, Pi.pow_apply]
  ring

theorem cauchy_inverse_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => 1 / (x ^ 2 + b ^ 2)) (Ioi 0) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => arctan (x / b) / b)
      (1 / (x ^ 2 + b ^ 2)) x := by
    intro x
    apply ((hasDerivAt_arctan_div hb x).div_const b).congr_deriv
    field_simp [hb.ne']
  exact integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x)
    (fun x _ => by positivity) ((tendsto_arctan_div hb).div_const b)

theorem cauchy_linear_square_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x / (x ^ 2 + b ^ 2) ^ 2) (Ioi 0) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -(1 / 2 : ℝ) * (x ^ 2 + b ^ 2)⁻¹)
      (x / (x ^ 2 + b ^ 2) ^ 2) x := by
    intro x
    apply (((((hasDerivAt_id x).pow 2).add_const (b ^ 2)).inv
      (ne_of_gt (cauchy_den_pos hb x))).const_mul (-(1 / 2 : ℝ))).congr_deriv
    simp only [id_eq, Pi.pow_apply]
    ring
  have ht := (tendsto_inv_cauchy b).const_mul (-(1 / 2 : ℝ))
  exact integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x)
    (fun x hx => div_nonneg hx.le (sq_nonneg _)) ht

theorem fourthCauchyKernel_abs_bound {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |fourthCauchyKernel b x| ≤ 120 / (x ^ 2 + b ^ 2) ^ 3 := by
  have hd := cauchy_den_pos hb x
  have hpoly : |x ^ 4 - 10 * x ^ 2 * b ^ 2 + 5 * b ^ 4| ≤ 5 * (x ^ 2 + b ^ 2) ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (x ^ 2), sq_nonneg (b ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg b)]
  unfold fourthCauchyKernel
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24), abs_of_pos (pow_pos hd 5)]
  calc
    24 * |x ^ 4 - 10 * x ^ 2 * b ^ 2 + 5 * b ^ 4| / (x ^ 2 + b ^ 2) ^ 5 ≤
        24 * (5 * (x ^ 2 + b ^ 2) ^ 2) / (x ^ 2 + b ^ 2) ^ 5 := by gcongr
    _ = 120 / (x ^ 2 + b ^ 2) ^ 3 := by field_simp; ring

theorem fourthCauchyKernel_continuous {b : ℝ} (hb : 0 < b) :
    Continuous (fourthCauchyKernel b) := by
  unfold fourthCauchyKernel
  fun_prop (disch := exact fun x => pow_ne_zero 5 (ne_of_gt (cauchy_den_pos hb x)))

theorem fourthCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fourthCauchyKernel b) (Ioi 0) := by
  apply ((cauchy_inverse_integrableOn hb).const_mul (120 / b ^ 4)).mono'
    (fourthCauchyKernel_continuous hb).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  refine (fourthCauchyKernel_abs_bound hb x).trans ?_
  have hd := cauchy_den_pos hb x
  have hl : b ^ 2 ≤ x ^ 2 + b ^ 2 := le_add_of_nonneg_left (sq_nonneg x)
  calc
    120 / (x ^ 2 + b ^ 2) ^ 3 =
        (120 / (x ^ 2 + b ^ 2) ^ 2) * (1 / (x ^ 2 + b ^ 2)) := by field_simp
    _ ≤ (120 / (b ^ 2) ^ 2) * (1 / (x ^ 2 + b ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_left₀ (sq_nonneg b) hl 2
    _ = _ := by ring

theorem linear_fourthCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x * fourthCauchyKernel b x) (Ioi 0) := by
  apply ((cauchy_linear_square_integrableOn hb).const_mul (120 / b ^ 2)).mono'
    (continuous_id.mul (fourthCauchyKernel_continuous hb)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖x * fourthCauchyKernel b x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx]
  calc
    x * |fourthCauchyKernel b x| ≤ x * (120 / (x ^ 2 + b ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left (fourthCauchyKernel_abs_bound hb x) hx.le
    _ = (120 / (x ^ 2 + b ^ 2)) * (x / (x ^ 2 + b ^ 2) ^ 2) := by field_simp
    _ ≤ (120 / b ^ 2) * (x / (x ^ 2 + b ^ 2) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hx.le (sq_nonneg _))
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (le_add_of_nonneg_left (sq_nonneg x))

theorem product_fourthCauchyKernel_integrableOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ 2 / (x ^ 2 + a ^ 2) * fourthCauchyKernel b x) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => x ^ 2 / (x ^ 2 + a ^ 2) * fourthCauchyKernel b x) := by
    apply Continuous.mul _ (fourthCauchyKernel_continuous hb)
    exact (continuous_id.pow 2).div ((continuous_id.pow 2).add continuous_const)
      (fun x => ne_of_gt (cauchy_den_pos ha x))
  apply (fourthCauchyKernel_integrableOn hb).norm.mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [norm_mul, Real.norm_eq_abs (x ^ 2 / (x ^ 2 + a ^ 2)), abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (cauchy_den_pos ha x)).mpr
    (le_add_of_nonneg_right (sq_nonneg a)))

theorem square_fourthCauchyKernel_integrableOn {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ 2 * fourthCauchyKernel b x) (Ioi 0) := by
  apply ((cauchy_inverse_integrableOn hb).const_mul (120 / b ^ 2)).mono'
    ((continuous_id.pow 2).mul (fourthCauchyKernel_continuous hb)).aestronglyMeasurable
  filter_upwards with x
  change ‖x ^ 2 * fourthCauchyKernel b x‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x)]
  have hd := cauchy_den_pos hb x
  calc
    x ^ 2 * |fourthCauchyKernel b x| ≤ x ^ 2 * (120 / (x ^ 2 + b ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left (fourthCauchyKernel_abs_bound hb x) (sq_nonneg x)
    _ ≤ (x ^ 2 + b ^ 2) * (120 / (x ^ 2 + b ^ 2) ^ 3) := by
      apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg b))
      positivity
    _ = (120 / (x ^ 2 + b ^ 2)) * (1 / (x ^ 2 + b ^ 2)) := by field_simp
    _ ≤ (120 / b ^ 2) * (1 / (x ^ 2 + b ^ 2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (le_add_of_nonneg_left (sq_nonneg x))

end Zeta5.Analysis
