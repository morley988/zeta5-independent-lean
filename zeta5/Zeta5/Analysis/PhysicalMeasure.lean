import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A positive series for the physical measure

The manuscript's density is represented on `x > 0` by its positive exponential
series.  Its pushforward under `x ↦ x²` will be used for the polynomial moments.
No Binet or Stieltjes identity is assumed in this file.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter
open scoped Topology BigOperators

/-- The positive exponential summands, indexed by `n+1`. -/
def expTerm (n : ℕ) (x : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))

/-- The positive-series version of `x^5 f''''(x)/12` on the positive half line. -/
def density (x : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 / 12 * x ^ 5 * ∑' n : ℕ, expTerm n x

theorem expTerm_pos (n : ℕ) (x : ℝ) : 0 < expTerm n x := by
  unfold expTerm
  positivity

theorem expTerm_measurable (n : ℕ) : Measurable (expTerm n) := by
  unfold expTerm
  fun_prop

theorem expTerm_summable {x : ℝ} (hx : 0 < x) : Summable (fun n => expTerm n x) := by
  have hc : -(2 * Real.pi * x) < 0 := neg_neg_of_pos (by positivity)
  have hs := summable_pow_mul_geometric_of_norm_lt_one 4
    (r := Real.exp (-(2 * Real.pi * x))) (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      exact hc)
  apply (summable_nat_add_iff 1).mpr hs |>.congr
  intro n
  dsimp [expTerm]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

theorem density_pos {x : ℝ} (hx : 0 < x) : 0 < density x := by
  have hsum : 0 < ∑' n : ℕ, expTerm n x := by
    exact lt_of_lt_of_le (expTerm_pos 0 x)
      ((expTerm_summable hx).le_tsum 0 (fun n _ => (expTerm_pos n x).le))
  exact mul_pos (by positivity) hsum

theorem density_measurable : Measurable density := by
  unfold density
  exact ((measurable_const.mul (measurable_id.pow_const 5)).mul
    (Measurable.tsum expTerm_measurable))

/-- Natural-power form of the convergent gamma integrand after positive scaling. -/
theorem integrableOn_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ m * Real.exp (-(r * x))) (Ioi 0) := by
  have hf : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ m) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity) using 1 <;>
      simp
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ m) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ m) 0 hr).mpr (by simpa using hf)
  apply IntegrableOn.congr_fun (hg.const_mul (r ^ m)⁻¹) _ measurableSet_Ioi
  intro x hx
  dsimp
  rw [mul_pow]
  field_simp [hr.ne']

/-- The exact elementary gamma integral needed for every moment. -/
theorem integral_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, x ^ m * Real.exp (-(r * x))) =
      (Nat.factorial m : ℝ) / r ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m : ℝ) + 1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The `k`-th moment integrand decomposed into positive summands. -/
def momentTerm (k n : ℕ) (x : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 / 12 * ((n + 1 : ℕ) : ℝ) ^ 4 *
    (x ^ (2 * k + 5) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x)))

theorem momentTerm_nonneg (k n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ momentTerm k n x := by
  unfold momentTerm
  positivity

theorem momentTerm_measurable (k n : ℕ) : Measurable (momentTerm k n) := by
  unfold momentTerm
  fun_prop

theorem momentTerm_integrable (k n : ℕ) : IntegrableOn (momentTerm k n) (Ioi 0) := by
  exact (integrableOn_pow_mul_exp_neg_mul (2 * k + 5) (by positivity)).const_mul _

/-- Coefficient of the ordinary even zeta series in the `k`-th moment. -/
def momentFactor (k : ℕ) : ℝ :=
  (Nat.factorial (2 * k + 5) : ℝ) / (12 * (2 * Real.pi) ^ (2 * k + 2))

theorem momentTerm_integral (k n : ℕ) :
    (∫ x : ℝ in Ioi 0, momentTerm k n x) =
      momentFactor k * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2)) := by
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold momentTerm momentFactor
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul _ (by positivity)]
  rw [show 2 * k + 5 + 1 = (2 * k + 2) + 4 by omega, mul_pow, pow_add, pow_add]
  field_simp
  <;> ring

theorem momentTerm_summable (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => momentTerm k n x) := by
  apply ((expTerm_summable hx).mul_left ((2 * Real.pi) ^ 4 / 12 * x ^ (2 * k + 5))).congr
  intro n
  dsimp [momentTerm, expTerm]
  ring

theorem momentTerm_tsum (k : ℕ) (x : ℝ) :
    (∑' n : ℕ, momentTerm k n x) = x ^ (2 * k) * density x := by
  calc
    _ = ∑' n : ℕ, (x ^ (2 * k) * ((2 * Real.pi) ^ 4 / 12 * x ^ 5)) * expTerm n x := by
      apply tsum_congr
      intro n
      simp only [momentTerm, expTerm, pow_add]
      ring
    _ = _ := by rw [tsum_mul_left]; simp [density, mul_assoc]

theorem momentTerm_integrals_summable (k : ℕ) :
    Summable (fun n => ∫ x : ℝ in Ioi 0, momentTerm k n x) := by
  simp_rw [momentTerm_integral]
  apply Summable.mul_left
  have h := (hasSum_zeta_nat (k := k + 1) (by omega)).summable
  have h' := (summable_nat_add_iff 1).mpr h
  simpa [mul_add] using h'

/-- Nonnegative termwise summation, with the integrability conclusion explicit. -/
theorem nonneg_tsum_integrableOn {F : ℕ → ℝ → ℝ}
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, IntegrableOn (F n) (Ioi 0))
    (hFn : ∀ n x, 0 < x → 0 ≤ F n x)
    (hFs : ∀ x, 0 < x → Summable (fun n => F n x))
    (hIs : Summable (fun n => ∫ x in Ioi 0, F n x)) :
    IntegrableOn (fun x => ∑' n, F n x) (Ioi 0) := by
  have hn (n : ℕ) : 0 ≤ᵐ[volume.restrict (Ioi 0)] F n := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact hFn n x hx
  have hin (n : ℕ) : 0 ≤ ∫ x in Ioi 0, F n x := integral_nonneg_of_ae (hn n)
  have hs : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun x => ∑' n, F n x) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact tsum_nonneg (fun n => hFn n x hx)
  refine ⟨(Measurable.tsum hFm).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hs).mpr ?_⟩
  have he : (∫⁻ x in Ioi 0, ENNReal.ofReal (∑' n, F n x)) =
      ENNReal.ofReal (∑' n, ∫ x in Ioi 0, F n x) := by
    calc
      _ = ∫⁻ x in Ioi 0, ∑' n, ENNReal.ofReal (F n x) := by
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => hFn n x hx) (hFs x hx)
      _ = ∑' n, ∫⁻ x in Ioi 0, ENNReal.ofReal (F n x) :=
        lintegral_tsum (fun n => (hFm n).ennreal_ofReal.aemeasurable)
      _ = ∑' n, ENNReal.ofReal (∫ x in Ioi 0, F n x) := by
        congr 1
        funext n
        exact (ofReal_integral_eq_lintegral_ofReal (hFi n) (hn n)).symm
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hin hIs).symm
  rw [he]
  exact ENNReal.ofReal_lt_top

/-- Every polynomial moment of the density is integrable. -/
theorem density_moment_integrable (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * k) * density x) (Ioi 0) := by
  have h := nonneg_tsum_integrableOn (momentTerm_measurable k) (momentTerm_integrable k)
    (fun n x hx => momentTerm_nonneg k n hx.le)
    (fun x hx => momentTerm_summable k hx) (momentTerm_integrals_summable k)
  simpa only [momentTerm_tsum] using h

theorem density_integrable : IntegrableOn density (Ioi 0) := by
  simpa using density_moment_integrable 0

/-- Evaluation of the physical moment as an even zeta series. -/
theorem density_moment_zeta (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * k) * density x) =
      momentFactor k * ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2) := by
  have hnorm : Summable (fun n => ∫ x in Ioi 0, ‖momentTerm k n x‖) := by
    convert momentTerm_integrals_summable k using 1
    ext n
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact Real.norm_of_nonneg (momentTerm_nonneg k n hx.le)
  have h := hasSum_integral_of_summable_integral_norm (momentTerm_integrable k) hnorm
  simpa only [momentTerm_tsum, momentTerm_integral, tsum_mul_left] using h.tsum_eq.symm

end Zeta5.Analysis.PhysicalMeasure
