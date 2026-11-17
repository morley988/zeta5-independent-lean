import Zeta5.Analysis.PhysicalMeasureLaplace
import Zeta5.Analysis.PhysicalMeasurePushforward

/-!
# From the positive density to the fourth rational Bose kernel

This file justifies the summation of the four Laplace integration-by-parts
steps. All series/interchanges use explicit integrable majorants.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def exponentialRate (n : ℕ) : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)

theorem exponentialRate_pos (n : ℕ) : 0 < exponentialRate n := by
  unfold exponentialRate
  positivity

private theorem stieltjesTerm_factor (n : ℕ) (y : ℝ) :
    (fun x : ℝ => momentTerm 0 n x / (x ^ 2 + y ^ 2)) =
      (fun x : ℝ => exponentialRate n ^ 4 / 12 *
        (laplaceKernel 0 y x * Real.exp (-(exponentialRate n * x)))) := by
  funext x
  simp only [momentTerm, laplaceKernel, laplaceNumerator, eval_pow, eval_X,
    mul_zero, zero_add, pow_one, exponentialRate]
  ring

theorem stieltjesTerm_integrable (n : ℕ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => momentTerm 0 n x / (x ^ 2 + y ^ 2)) (Ioi 0) := by
  rw [stieltjesTerm_factor]
  exact (laplaceKernel_exp_integrable 0 hy (exponentialRate_pos n)).const_mul _

theorem stieltjesTerm_laplace (n : ℕ) {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in Ioi 0, momentTerm 0 n x / (x ^ 2 + y ^ 2)) =
      (1 / 12 : ℝ) * ∫ x : ℝ in Ioi 0, laplaceKernel 4 y x * boseTerm n x := by
  rw [stieltjesTerm_factor, integral_const_mul]
  have h := laplaceKernel_four_integral hy (exponentialRate_pos n)
  change _ = _ * ∫ x : ℝ in Ioi 0, laplaceKernel 4 y x * Real.exp (-(exponentialRate n * x))
  rw [h]
  simp only [laplaceKernel, laplaceNumerator, eval_pow, eval_X, zero_add, pow_one]
  ring

theorem stieltjesTerm_integral_norm_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun n => ∫ x : ℝ in Ioi 0, ‖momentTerm 0 n x / (x ^ 2 + y ^ 2)‖) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) _
    ((momentTerm_integrals_summable 0).mul_left (1 / y ^ 2))
  intro n
  rw [← integral_const_mul]
  apply integral_mono_ae (stieltjesTerm_integrable n hy).norm ((momentTerm_integrable 0 n).const_mul _)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hm := momentTerm_nonneg 0 n hx.le
  rw [Real.norm_of_nonneg (div_nonneg hm (by positivity))]
  have h := div_le_div_of_nonneg_left hm (sq_pos_of_pos hy)
    (by nlinarith [sq_nonneg x] : y ^ 2 ≤ x ^ 2 + y ^ 2)
  simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using h

private theorem x_boseTerm_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x * boseTerm n x) (Ioi 0) := by
  simpa only [boseTerm, exponentialRate, pow_one] using
    integrableOn_pow_mul_exp_neg_mul 1 (exponentialRate_pos n)

private theorem x_boseTerm_integral (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x * boseTerm n x) = 1 / exponentialRate n ^ 2 := by
  simpa only [boseTerm, exponentialRate, pow_one, Nat.factorial_one, Nat.cast_one,
    one_add_one_eq_two] using integral_pow_mul_exp_neg_mul 1 (exponentialRate_pos n)

private theorem x_boseTerm_integrals_summable :
    Summable (fun n => ∫ x : ℝ in Ioi 0, x * boseTerm n x) := by
  simp_rw [x_boseTerm_integral, exponentialRate, mul_pow, ← one_div_mul_one_div]
  exact ((summable_nat_add_iff 1).mpr
    (summable_one_div_nat_pow.mpr (by omega : 1 < 2))).mul_left _

theorem laplaceFourthTerm_integrable (n : ℕ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => laplaceKernel 4 y x * boseTerm n x) (Ioi 0) :=
  laplaceKernel_exp_integrable 4 hy (exponentialRate_pos n)

theorem laplaceFourth_integral_norm_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun n => ∫ x : ℝ in Ioi 0, ‖laplaceKernel 4 y x * boseTerm n x‖) := by
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) _
    (x_boseTerm_integrals_summable.mul_left (120 / y ^ 2))
  intro n
  rw [← integral_const_mul]
  apply integral_mono_ae (laplaceFourthTerm_integrable n hy).norm
    ((x_boseTerm_integrable n).const_mul _)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hb : 0 < boseTerm n x := Real.exp_pos _
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hb]
  calc
    _ ≤ ((120 / y ^ 2) * x) * boseTerm n x :=
      mul_le_mul_of_nonneg_right (laplaceKernel_four_abs_le hy hx.le) hb.le
    _ = _ := by ring

/-- The physical Stieltjes transform is the fourth rational Bose-kernel
integral, with all integration-by-parts and interchange steps checked. -/
theorem stieltjesTransform_laplaceFourth {y : ℝ} (hy : 0 < y) :
    stieltjesTransform y =
      (1 / 12 : ℝ) * ∫ x : ℝ in Ioi 0, laplaceKernel 4 y x * bose x := by
  have hF := hasSum_integral_of_summable_integral_norm
    (fun n => stieltjesTerm_integrable n hy) (stieltjesTerm_integral_norm_summable hy)
  have hG := hasSum_integral_of_summable_integral_norm
    (fun n => laplaceFourthTerm_integrable n hy)
    (laplaceFourth_integral_norm_summable hy)
  rw [stieltjesTransform_density]
  calc
    _ = ∑' n : ℕ, ∫ x : ℝ in Ioi 0, momentTerm 0 n x / (x ^ 2 + y ^ 2) := by
      rw [hF.tsum_eq]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [tsum_div_const, momentTerm_tsum]
      simp
    _ = (1 / 12 : ℝ) * ∑' n : ℕ, ∫ x : ℝ in Ioi 0, laplaceKernel 4 y x * boseTerm n x := by
      simp_rw [stieltjesTerm_laplace _ hy]
      rw [tsum_mul_left]
    _ = _ := by
      congr 1
      rw [hG.tsum_eq]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (∑' n, laplaceKernel 4 y x * boseTerm n x) = _
      rw [tsum_mul_left, (boseTerm_hasSum hx).tsum_eq]

end Zeta5.Analysis.PhysicalMeasure
