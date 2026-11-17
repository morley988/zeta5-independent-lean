import Zeta5.Analysis.PhysicalMeasureStieltjesLaplace
import Zeta5.Analysis.PhysicalMeasureCoth
import Zeta5.Analysis.PhysicalMeasureCauchyFourth

/-!
# Absolute interchange of the coth partial fractions

The square-weighted fourth kernel is integrable. Its norm dominates every
coth term by a summable multiple `1/(n+1)²`, so the next decomposition is an
actual equality of convergent improper integrals.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

private theorem signed_tsum_integrableOn {F : ℕ → ℝ → ℝ}
    (hm : ∀ n, Measurable (F n)) (hi : ∀ n, IntegrableOn (F n) (Ioi 0))
    (hs : ∀ x, 0 < x → Summable (fun n => F n x))
    (hIs : Summable (fun n => ∫ x in Ioi 0, ‖F n x‖)) :
    IntegrableOn (fun x => ∑' n, F n x) (Ioi 0) := by
  have habs := nonneg_tsum_integrableOn (fun n => (hm n).norm) (fun n => (hi n).norm)
    (fun n x _ => norm_nonneg _) (fun x hx => (hs x hx).norm) hIs
  apply habs.mono' (Measurable.tsum hm).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact norm_tsum_le_tsum_norm (hs x hx).norm

def cothFourthTerm (n : ℕ) (y x : ℝ) : ℝ :=
  x ^ 2 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) * Zeta5.Analysis.fourthCauchyKernel y x

theorem cothFourthTerm_measurable (n : ℕ) (y : ℝ) : Measurable (cothFourthTerm n y) := by
  unfold cothFourthTerm Zeta5.Analysis.fourthCauchyKernel
  fun_prop

theorem cothFourthTerm_integrable (n : ℕ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (cothFourthTerm n y) (Ioi 0) :=
  Zeta5.Analysis.product_fourthCauchyKernel_integrableOn (by positivity) hy

theorem cothFourthTerm_summable (y x : ℝ) : Summable (fun n => cothFourthTerm n y x) := by
  apply ((cauchySeries_summable x).mul_left
    (x ^ 2 * Zeta5.Analysis.fourthCauchyKernel y x)).congr
  intro n
  unfold cothFourthTerm
  ring

theorem cothFourthTerm_integral_norm_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun n => ∫ x : ℝ in Ioi 0, ‖cothFourthTerm n y x‖) := by
  have hbase := Zeta5.Analysis.square_fourthCauchyKernel_integrableOn hy
  have hs := ((summable_nat_add_iff 1).mpr
    (summable_one_div_nat_pow.mpr (by omega : 1 < 2))).mul_left
      (∫ x : ℝ in Ioi 0, ‖x ^ 2 * Zeta5.Analysis.fourthCauchyKernel y x‖)
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) _ hs
  intro n
  rw [mul_comm, ← integral_const_mul]
  apply integral_mono_ae (cothFourthTerm_integrable n hy).norm (hbase.norm.const_mul _)
  filter_upwards with x
  have hd : 0 < x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have he : cothFourthTerm n y x =
      (x ^ 2 * Zeta5.Analysis.fourthCauchyKernel y x) / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
    unfold cothFourthTerm
    ring
  rw [he, norm_div, Real.norm_of_nonneg hd.le]
  have h := div_le_div_of_nonneg_left (norm_nonneg
    (x ^ 2 * Zeta5.Analysis.fourthCauchyKernel y x))
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ) ^ 2)
    (by nlinarith [sq_nonneg x] : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)
  simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using h

theorem cothFourthSeries_integrable {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x => ∑' n : ℕ, cothFourthTerm n y x) (Ioi 0) :=
  signed_tsum_integrableOn (fun n => cothFourthTerm_measurable n y)
    (fun n => cothFourthTerm_integrable n hy) (fun x _ => cothFourthTerm_summable y x)
    (cothFourthTerm_integral_norm_summable hy)

/-- The Bose integral is decomposed into three absolutely convergent pieces. -/
theorem bose_fourth_integral_coth {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in Ioi 0, (x * bose x) * Zeta5.Analysis.fourthCauchyKernel y x) =
      1 / (2 * Real.pi) * (∫ x : ℝ in Ioi 0, Zeta5.Analysis.fourthCauchyKernel y x) -
      (1 / 2 : ℝ) * (∫ x : ℝ in Ioi 0, x * Zeta5.Analysis.fourthCauchyKernel y x) +
      1 / Real.pi * ∑' n : ℕ, ∫ x : ℝ in Ioi 0, cothFourthTerm n y x := by
  have hpoint {x : ℝ} (hx : 0 < x) :
      (x * bose x) * Zeta5.Analysis.fourthCauchyKernel y x =
        1 / (2 * Real.pi) * Zeta5.Analysis.fourthCauchyKernel y x -
        (1 / 2 : ℝ) * (x * Zeta5.Analysis.fourthCauchyKernel y x) +
        1 / Real.pi * ∑' n : ℕ, cothFourthTerm n y x := by
    have hs : (∑' n : ℕ, cothFourthTerm n y x) =
        (x ^ 2 * Zeta5.Analysis.fourthCauchyKernel y x) *
          ∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold cothFourthTerm
      ring
    rw [x_bose_coth hx, hs]
    ring
  calc
    _ = ∫ x : ℝ in Ioi 0,
        1 / (2 * Real.pi) * Zeta5.Analysis.fourthCauchyKernel y x -
        (1 / 2 : ℝ) * (x * Zeta5.Analysis.fourthCauchyKernel y x) +
        1 / Real.pi * ∑' n : ℕ, cothFourthTerm n y x := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpoint hx)
    _ = _ := by
      have hA : IntegrableOn (fun x : ℝ => 1 / (2 * Real.pi) * Zeta5.Analysis.fourthCauchyKernel y x) (Ioi 0) :=
        (Zeta5.Analysis.fourthCauchyKernel_integrableOn hy).const_mul _
      have hB : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * (x * Zeta5.Analysis.fourthCauchyKernel y x)) (Ioi 0) :=
        (Zeta5.Analysis.linear_fourthCauchyKernel_integrableOn hy).const_mul _
      have hC : IntegrableOn (fun x : ℝ => 1 / Real.pi * ∑' n : ℕ, cothFourthTerm n y x) (Ioi 0) :=
        (cothFourthSeries_integrable hy).const_mul _
      have hAB : IntegrableOn (fun x : ℝ => 1 / (2 * Real.pi) * Zeta5.Analysis.fourthCauchyKernel y x -
        (1 / 2 : ℝ) * (x * Zeta5.Analysis.fourthCauchyKernel y x)) (Ioi 0) := hA.sub hB
      rw [integral_add hAB hC, integral_sub hA hB]
      simp only [integral_const_mul]
      rw [(hasSum_integral_of_summable_integral_norm (fun n => cothFourthTerm_integrable n hy)
        (cothFourthTerm_integral_norm_summable hy)).tsum_eq]

/-- The physical Stieltjes transform is now reduced to explicitly evaluable
rational integrals, with no Binet identity or exchange hypotheses. -/
theorem stieltjesTransform_coth {y : ℝ} (hy : 0 < y) :
    stieltjesTransform y = y ^ 4 / 12 *
      (1 / (2 * Real.pi) * (∫ x : ℝ in Ioi 0, Zeta5.Analysis.fourthCauchyKernel y x) -
        (1 / 2 : ℝ) * (∫ x : ℝ in Ioi 0, x * Zeta5.Analysis.fourthCauchyKernel y x) +
        1 / Real.pi * ∑' n : ℕ, ∫ x : ℝ in Ioi 0, cothFourthTerm n y x) := by
  rw [stieltjesTransform_laplaceFourth hy]
  have hfun : (fun x : ℝ => laplaceKernel 4 y x * bose x) =
      (fun x : ℝ => y ^ 4 * ((x * bose x) * Zeta5.Analysis.fourthCauchyKernel y x)) := by
    funext x
    rw [laplaceKernel_four]
    unfold Zeta5.Analysis.fourthCauchyKernel
    ring
  rw [hfun, integral_const_mul, bose_fourth_integral_coth hy]
  ring

end Zeta5.Analysis.PhysicalMeasure
