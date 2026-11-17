import Zeta5.Analysis.PhysicalMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Bose factor and the elementary coth partial fractions

These are ingredients for the outstanding Stieltjes identity. The positive
series definition is retained throughout; no special-function integral
representation is asserted by definition.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

/-- The elementary Bose factor on the positive half line. -/
def bose (x : ℝ) : ℝ := 1 / (Real.exp (2 * Real.pi * x) - 1)

def boseTerm (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x))

theorem bose_pos {x : ℝ} (hx : 0 < x) : 0 < bose x := by
  unfold bose
  exact one_div_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))

theorem bose_measurable : Measurable bose := by unfold bose; fun_prop

theorem bose_eq_geometric {x : ℝ} (hx : 0 < x) :
    bose x = Real.exp (-(2 * Real.pi * x)) / (1 - Real.exp (-(2 * Real.pi * x))) := by
  have he : Real.exp (2 * Real.pi * x) ≠ 0 := (Real.exp_pos _).ne'
  have he' : Real.exp (2 * Real.pi * x) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  unfold bose
  rw [Real.exp_neg]
  field_simp
  <;> ring

theorem boseTerm_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => boseTerm n x) (bose x) := by
  have hq : ‖Real.exp (-(2 * Real.pi * x))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact neg_neg_of_pos (by positivity)
  have h := (hasSum_geometric_of_norm_lt_one hq).mul_left (Real.exp (-(2 * Real.pi * x)))
  rw [bose_eq_geometric hx]
  have heq : (fun n : ℕ => Real.exp (-(2 * Real.pi * x)) * Real.exp (-(2 * Real.pi * x)) ^ n) =
      (fun n => boseTerm n x) := by
    funext n
    rw [← pow_succ', ← Real.exp_nat_mul]
    dsimp [boseTerm]
    congr 1
    push_cast
    ring
  rw [heq] at h
  simpa only [div_eq_mul_inv] using h


/-- A positive integrable majorant needed when exchanging the Bose series
with bounded rational kernels. -/
theorem x_bose_integrable : IntegrableOn (fun x : ℝ => x * bose x) (Ioi 0) := by
  let F (n : ℕ) (x : ℝ) := x * boseTerm n x
  have hm n : Measurable (F n) := by dsimp [F, boseTerm]; fun_prop
  have hi n : IntegrableOn (F n) (Ioi 0) := by
    simpa only [F, boseTerm, pow_one] using
      integrableOn_pow_mul_exp_neg_mul 1 (r := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hI n : (∫ x in Ioi 0, F n x) =
      (1 / (2 * Real.pi) ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [F, boseTerm, pow_one, Nat.factorial_one, Nat.cast_one, one_add_one_eq_two,
      mul_pow, one_div_mul_one_div] using
      integral_pow_mul_exp_neg_mul 1 (r := 2 * Real.pi * ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hIs : Summable (fun n => ∫ x in Ioi 0, F n x) := by
    simp_rw [hI]
    exact ((summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr (by omega : 1 < 2))).mul_left _
  have h := nonneg_tsum_integrableOn hm hi (fun n x hx => by dsimp [F, boseTerm]; positivity)
    (fun x hx => (boseTerm_hasSum hx).summable.mul_left x) hIs
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro x hx
  dsimp [F]
  rw [tsum_mul_left, (boseTerm_hasSum hx).tsum_eq]

end Zeta5.Analysis.PhysicalMeasure
