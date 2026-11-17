import Zeta5.Analysis.ExternalField
import Zeta5.Analysis.PhysicalMeasureGram

/-! # Exact monotone Riemann bounds for the physical polynomial weight -/

noncomputable section
namespace Zeta5.Analysis
open Real Set MeasureTheory Filter Polynomial Finset
open scoped Topology BigOperators

theorem monotone_grid_integral_bounds (f : ℝ → ℝ) (hf : Continuous f)
    (hm : MonotoneOn f (Ici 0)) {N : ℝ} (hN : 0 < N) (m : ℕ) :
    (∑ i ∈ range m, f ((i : ℝ) / N)) ≤ N * ∫ t in 0..((m : ℝ) / N), f t ∧
    N * (∫ t in 0..((m : ℝ) / N), f t) ≤ ∑ i ∈ range m, f (((i + 1 : ℕ) : ℝ) / N) := by
  have hab (i : ℕ) : (i : ℝ) / N ≤ ((i + 1 : ℕ) : ℝ) / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast Nat.le_succ i
  have hi (i : ℕ) : IntervalIntegrable f volume ((i : ℝ) / N) (((i + 1 : ℕ) : ℝ) / N) :=
    hf.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / N) (fun i (_ : i < m) => hi i)
  simp only [Nat.cast_zero, zero_div] at hsum
  have hlength (i : ℕ) : ((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N = 1 / N := by
    push_cast
    ring
  have hlow (i : ℕ) : (1 / N) * f ((i : ℝ) / N) ≤
      ∫ t in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, f t := by
    have h := intervalIntegral.integral_mono_on (hab i) intervalIntegrable_const (hi i)
      (fun t ht => hm (show 0 ≤ (i : ℝ) / N by positivity)
        (le_trans (show 0 ≤ (i : ℝ) / N by positivity) ht.1) ht.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hlength] using h
  have hupp (i : ℕ) : (∫ t in (i : ℝ) / N..((i + 1 : ℕ) : ℝ) / N, f t) ≤
      (1 / N) * f (((i + 1 : ℕ) : ℝ) / N) := by
    have h := intervalIntegral.integral_mono_on (hab i) (hi i) intervalIntegrable_const
      (fun t ht => hm (le_trans (show 0 ≤ (i : ℝ) / N by positivity) ht.1)
        (show 0 ≤ ((i + 1 : ℕ) : ℝ) / N by positivity) ht.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hlength] using h
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ range m) => hlow i)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ range m) => hupp i)
  rw [hsum, ← Finset.mul_sum] at hl hu
  constructor
  · have h := mul_le_mul_of_nonneg_left hl hN.le
    simpa only [← mul_assoc, mul_one_div_cancel hN.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hu hN.le
    simpa only [← mul_assoc, mul_one_div_cancel hN.ne', one_mul] using h

theorem logarithmic_grid_bounds {y N : ℝ} (hy : 0 < y) (hN : 0 < N) (m : ℕ) :
    (∑ i ∈ range m, Real.log (y ^ 2 + ((i : ℝ) / N) ^ 2)) ≤
        N * externalIntegral ((m : ℝ) / N) y ∧
    N * externalIntegral ((m : ℝ) / N) y ≤
      ∑ i ∈ range m, Real.log (y ^ 2 + (((i + 1 : ℕ) : ℝ) / N) ^ 2) := by
  apply monotone_grid_integral_bounds _
    ((continuous_const.add (continuous_id.pow 2)).log
      (fun t => ne_of_gt (by positivity : 0 < y ^ 2 + t ^ 2))) _ hN m
  intro a ha b hb hab
  change Real.log (y ^ 2 + a ^ 2) ≤ Real.log (y ^ 2 + b ^ 2)
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  exact Real.log_le_log (by positivity) (by nlinarith)

def realWindowBasis (m : ℕ) : ℝ[X] :=
  (Zeta5.Construction.windowBasis m).map (Rat.castHom ℝ)

theorem realWindowBasis_eval_abs (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(realWindowBasis m).eval t| = (Nat.factorial (2 * m) : ℝ)⁻¹ *
      ∏ i ∈ range m, (t + (i : ℝ) ^ 2) := by
  simp only [realWindowBasis, Zeta5.Construction.windowBasis, Zeta5.Construction.centralPolynomial,
    Zeta5.Construction.rootPolynomial, Polynomial.map_comp, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_neg, eval_comp, eval_neg, eval_X, eval_mul, eval_C, eval_prod,
    eval_sub, Rat.coe_castHom, Rat.cast_inv, Rat.cast_natCast, Rat.cast_pow]
  rw [abs_mul, abs_inv, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.factorial (2 * m)),
    Finset.abs_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [show -t - (i : ℝ) ^ 2 = -(t + (i : ℝ) ^ 2) by ring, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ t + (i : ℝ) ^ 2)]

theorem shifted_square_product_scale {N : ℝ} (hN : 0 < N) (m : ℕ) (y : ℝ) (a : ℕ) :
    (∏ i ∈ range m, (N ^ 2 * y ^ 2 + ((i + a : ℕ) : ℝ) ^ 2)) =
      N ^ (2 * m) * ∏ i ∈ range m, (y ^ 2 + (((i + a : ℕ) : ℝ) / N) ^ 2) := by
  have he (i : ℕ) : N ^ 2 * y ^ 2 + ((i + a : ℕ) : ℝ) ^ 2 =
      N ^ 2 * (y ^ 2 + (((i + a : ℕ) : ℝ) / N) ^ 2) := by
    field_simp
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]

theorem realDenominator_scaled (N : ℕ) (hN : 0 < N) (y : ℝ) :
    (PhysicalMeasure.realDenominator N).eval ((N : ℝ) ^ 2 * y ^ 2) =
      (N : ℝ) ^ (2 * N) * ∏ i ∈ range N, (y ^ 2 + (((i + 1 : ℕ) : ℝ) / N) ^ 2) := by
  simp only [PhysicalMeasure.realDenominator, Zeta5.Construction.denominator,
    Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    eval_prod, eval_add, eval_X, eval_C, Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast]
  exact shifted_square_product_scale (by exact_mod_cast hN) N y 1

/-- The denominator is bounded below by the exponential of the actual
right Riemann integral. -/
theorem realDenominator_riemann_lower (N : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    (N : ℝ) ^ (2 * N) * Real.exp ((N : ℝ) * externalIntegral 1 y) ≤
      (PhysicalMeasure.realDenominator N).eval ((N : ℝ) ^ 2 * y ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid := (logarithmic_grid_bounds hy hNr N).2
  rw [div_self hNr.ne'] at hgrid
  rw [realDenominator_scaled N hN]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hNr.le _)
  have h := Real.exp_le_exp.mpr hgrid
  rw [Real.exp_sum] at h
  have he (i : ℕ) : Real.exp (Real.log (y ^ 2 + (((i + 1 : ℕ) : ℝ) / N) ^ 2)) =
      y ^ 2 + (((i + 1 : ℕ) : ℝ) / N) ^ 2 := Real.exp_log (by positivity)
  simpa only [he] using h

/-- The left Riemann integral bounds the common factorial polynomial. -/
theorem realWindowBasis_riemann_upper (N m : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    |(realWindowBasis m).eval ((N : ℝ) ^ 2 * y ^ 2)| ≤
      (Nat.factorial (2 * m) : ℝ)⁻¹ * (N : ℝ) ^ (2 * m) *
        Real.exp ((N : ℝ) * externalIntegral ((m : ℝ) / N) y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgrid := (logarithmic_grid_bounds hy hNr m).1
  rw [realWindowBasis_eval_abs m (by positivity)]
  have hscale := shifted_square_product_scale hNr m y 0
  simp only [Nat.add_zero] at hscale
  rw [hscale, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Real.exp_le_exp.mpr hgrid
  rw [Real.exp_sum] at h
  have he (i : ℕ) : Real.exp (Real.log (y ^ 2 + ((i : ℝ) / N) ^ 2)) =
      y ^ 2 + ((i : ℝ) / N) ^ 2 := Real.exp_log (by positivity)
  simpa only [he] using h

end Zeta5.Analysis
