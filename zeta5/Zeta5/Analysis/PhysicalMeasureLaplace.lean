import Zeta5.Analysis.PhysicalMeasureBose
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Laplace integration by parts for the physical Stieltjes kernel

The exponential terms are treated individually, so no unproved statement
about differentiating the Bose series is required.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

theorem polynomial_exp_integrable (P : ℝ[X]) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => P.eval x * Real.exp (-(r * x))) (Ioi 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [eval_add, add_mul]
    exact hP.add hQ
  | monomial n a =>
    simp only [eval_monomial, mul_assoc]
    exact (integrableOn_pow_mul_exp_neg_mul n hr).const_mul a

theorem polynomial_exp_tendsto_zero (P : ℝ[X]) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => P.eval x * Real.exp (-(r * x))) atTop (𝓝 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [eval_add, add_mul, add_zero] using hP.add hQ
  | monomial n a =>
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r hr).const_mul a
    simpa only [Real.rpow_natCast, eval_monomial, mul_assoc, mul_zero, neg_mul] using h

/-- Rational functions with a positive quadratic denominator remain Laplace
integrable after multiplication by any real polynomial. -/
theorem polynomial_div_quadratic_exp_integrable (P : ℝ[X]) (k : ℕ) {y r : ℝ}
    (hy : 0 < y) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => P.eval x / (x ^ 2 + y ^ 2) ^ (k + 1) *
      Real.exp (-(r * x))) (Ioi 0) := by
  have hmeas : Measurable (fun x : ℝ => P.eval x / (x ^ 2 + y ^ 2) ^ (k + 1) *
      Real.exp (-(r * x))) := by fun_prop
  apply ((polynomial_exp_integrable P hr).norm.div_const ((y ^ 2) ^ (k + 1))).mono'
    hmeas.aestronglyMeasurable
  filter_upwards with x
  have hd : 0 < (x ^ 2 + y ^ 2) ^ (k + 1) := by positivity
  calc
    ‖P.eval x / (x ^ 2 + y ^ 2) ^ (k + 1) * Real.exp (-(r * x))‖ =
        ‖P.eval x * Real.exp (-(r * x))‖ / (x ^ 2 + y ^ 2) ^ (k + 1) := by
      simp only [div_mul_eq_mul_div, norm_div, Real.norm_eq_abs, abs_of_pos hd]
    _ ≤ ‖P.eval x * Real.exp (-(r * x))‖ / (y ^ 2) ^ (k + 1) := by
      apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      exact pow_le_pow_left₀ (sq_nonneg y) (by nlinarith [sq_nonneg x]) _

theorem polynomial_div_quadratic_exp_tendsto_zero (P : ℝ[X]) (k : ℕ) {y r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun x : ℝ => P.eval x / (x ^ 2 + y ^ 2) ^ (k + 1) *
      Real.exp (-(r * x))) atTop (𝓝 0) := by
  have hd : Tendsto (fun x : ℝ => (x ^ 2 + y ^ 2) ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero k)).comp
      (tendsto_atTop_add_const_right atTop (y ^ 2) (tendsto_pow_atTop (by omega : (2 : ℕ) ≠ 0)))
  simpa only [div_mul_eq_mul_div] using (polynomial_exp_tendsto_zero P hr).div_atTop hd

/-- Differentiate a rational function whose denominator is a power of a
positive quadratic, retaining a polynomial numerator. -/
theorem hasDerivAt_polynomial_div_quadratic (P : ℝ[X]) (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t : ℝ => P.eval t / (t ^ 2 + y ^ 2) ^ (k + 1))
      (((P.derivative * (X ^ 2 + C (y ^ 2)) - C (2 * ((k + 1 : ℕ) : ℝ)) * X * P).eval x) /
        (x ^ 2 + y ^ 2) ^ (k + 2)) x := by
  have hd : x ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  convert! (P.hasDerivAt x).div (hquad.pow (k + 1)) (pow_ne_zero _ hd) using 1
  simp only [Pi.pow_apply, Pi.mul_apply, eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp
  <;> ring

/-- Numerators of the first four derivatives of `x⁵/(x²+y²)`. -/
def laplaceNumerator (y : ℝ) : ℕ → ℝ[X]
  | 0 => X ^ 5
  | k + 1 => (laplaceNumerator y k).derivative * (X ^ 2 + C (y ^ 2)) -
      C (2 * ((k + 1 : ℕ) : ℝ)) * X * laplaceNumerator y k

def laplaceKernel (k : ℕ) (y x : ℝ) : ℝ :=
  (laplaceNumerator y k).eval x / (x ^ 2 + y ^ 2) ^ (k + 1)

theorem laplaceKernel_hasDerivAt (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (laplaceKernel k y) (laplaceKernel (k + 1) y x) x := by
  exact hasDerivAt_polynomial_div_quadratic (laplaceNumerator y k) k hy x

theorem laplaceKernel_exp_integrable (k : ℕ) {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => laplaceKernel k y x * Real.exp (-(r * x))) (Ioi 0) :=
  polynomial_div_quadratic_exp_integrable _ k hy hr

theorem laplaceKernel_exp_tendsto_zero (k : ℕ) {y r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => laplaceKernel k y x * Real.exp (-(r * x))) atTop (𝓝 0) :=
  polynomial_div_quadratic_exp_tendsto_zero _ k hr

/-- A single Laplace integration-by-parts step, including the zero and infinity
boundary conditions. -/
theorem laplace_integral_derivative {f f' : ℝ → ℝ} {r : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hzero : f 0 = 0)
    (hi : IntegrableOn (fun x => f x * Real.exp (-(r * x))) (Ioi 0))
    (hi' : IntegrableOn (fun x => f' x * Real.exp (-(r * x))) (Ioi 0))
    (hinfty : Tendsto (fun x => f x * Real.exp (-(r * x))) atTop (𝓝 0)) :
    (∫ x : ℝ in Ioi 0, f' x * Real.exp (-(r * x))) =
      r * ∫ x : ℝ in Ioi 0, f x * Real.exp (-(r * x)) := by
  have hd (x : ℝ) : HasDerivAt (fun t => f t * Real.exp (-(r * t)))
      (f' x * Real.exp (-(r * x)) + (-r) * (f x * Real.exp (-(r * x)))) x := by
    convert! (hf x).mul (((hasDerivAt_id x).const_mul r).neg.exp) using 1 <;>
      simp only [Pi.neg_apply, id_eq] <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (hi'.add (hi.const_mul (-r))) hinfty
  rw [integral_add hi' (hi.const_mul (-r)), integral_const_mul] at h
  simp only [hzero, mul_zero, neg_zero, Real.exp_zero, zero_mul, sub_zero] at h
  linarith

theorem laplaceKernel_zero (k : ℕ) (hk : k < 4) (y : ℝ) : laplaceKernel k y 0 = 0 := by
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    norm_num [laplaceKernel, laplaceNumerator, derivative_mul, derivative_pow,
      derivative_sub, derivative_add, map_mul, map_pow]

/-- Four integrations by parts are justified for each exponential term. -/
theorem laplaceKernel_four_integral {y r : ℝ} (hy : 0 < y) (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, laplaceKernel 4 y x * Real.exp (-(r * x))) =
      r ^ 4 * ∫ x : ℝ in Ioi 0, x ^ 5 / (x ^ 2 + y ^ 2) * Real.exp (-(r * x)) := by
  have hstep (k : ℕ) (hk : k < 4) :
      (∫ x : ℝ in Ioi 0, laplaceKernel (k + 1) y x * Real.exp (-(r * x))) =
        r * ∫ x : ℝ in Ioi 0, laplaceKernel k y x * Real.exp (-(r * x)) :=
    laplace_integral_derivative (laplaceKernel_hasDerivAt k hy) (laplaceKernel_zero k hk y)
      (laplaceKernel_exp_integrable k hy hr) (laplaceKernel_exp_integrable (k + 1) hy hr)
      (laplaceKernel_exp_tendsto_zero k hr)
  rw [hstep 3 (by omega), hstep 2 (by omega), hstep 1 (by omega), hstep 0 (by omega)]
  simp only [laplaceKernel, laplaceNumerator, eval_pow, eval_X, zero_add, pow_one]
  ring

/-- Explicit fourth kernel, obtained from the recursive polynomial derivative. -/
theorem laplaceKernel_four (y x : ℝ) :
    laplaceKernel 4 y x =
      24 * x * y ^ 4 * (x ^ 4 - 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4) /
        (x ^ 2 + y ^ 2) ^ 5 := by
  unfold laplaceKernel
  congr 1
  norm_num [laplaceNumerator, derivative_mul, derivative_pow, derivative_sub, derivative_add,
    map_mul, map_pow, eval_sub, eval_add, eval_mul, eval_pow]
  <;> ring

/-- A uniform linear majorant of the fourth integration-by-parts kernel.
It permits absolute interchange with the positive Bose series. -/
theorem laplaceKernel_four_abs_le {y x : ℝ} (hy : 0 < y) (hx : 0 ≤ x) :
    |laplaceKernel 4 y x| ≤ (120 / y ^ 2) * x := by
  have hd : 0 < x ^ 2 + y ^ 2 := by positivity
  have hp : |x ^ 4 - 10 * x ^ 2 * y ^ 2 + 5 * y ^ 4| ≤ 5 * (x ^ 2 + y ^ 2) ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2),
      mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have hden : y ^ 4 / (x ^ 2 + y ^ 2) ^ 3 ≤ 1 / y ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hd 3) (sq_pos_of_pos hy)).mpr
    have h := pow_le_pow_left₀ (sq_nonneg y) (by nlinarith [sq_nonneg x] : y ^ 2 ≤ x ^ 2 + y ^ 2) 3
    nlinarith
  rw [laplaceKernel_four, abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24),
    abs_of_nonneg hx, abs_of_nonneg (pow_nonneg hy.le 4), abs_of_pos (pow_pos hd 5)]
  calc
    _ ≤ 24 * x * y ^ 4 * (5 * (x ^ 2 + y ^ 2) ^ 2) / (x ^ 2 + y ^ 2) ^ 5 := by
      gcongr
    _ = (120 * x) * (y ^ 4 / (x ^ 2 + y ^ 2) ^ 3) := by field_simp; ring
    _ ≤ (120 * x) * (1 / y ^ 2) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

end Zeta5.Analysis.PhysicalMeasure
