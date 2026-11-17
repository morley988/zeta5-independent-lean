import Zeta5.Analysis.LogQuadrature
import Zeta5.Analysis.QuantilePartition
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Monic trial polynomials from Hölder small-ball control

This is a quantitative discretization theorem for an actual finite measure.
Its assumptions concern only mass, compact interval cells and a small-ball
bound; the logarithmic quadrature estimate and the polynomial norm inequality
are proved here.  A separate potential identity is needed to apply it to the
specific auxiliary measure of the zeta argument.
-/

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace Zeta5.Analysis

noncomputable def quantilePolynomial (n : ℕ) (sample : ℕ → ℝ) : ℝ[X] :=
  ∏ j ∈ Finset.range n, (X-C (sample j))

lemma quantilePolynomial_monic (n : ℕ) (sample : ℕ → ℝ) :
    (quantilePolynomial n sample).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma quantilePolynomial_natDegree (n : ℕ) (sample : ℕ → ℝ) :
    (quantilePolynomial n sample).natDegree = n := by
  simp [quantilePolynomial]

lemma quantilePolynomial_eval (n : ℕ) (sample : ℕ → ℝ) (v : ℝ) :
    (quantilePolynomial n sample).eval v = ∏ j ∈ Finset.range n, (v-sample j) := by
  simp [quantilePolynomial, Polynomial.eval_prod]

/-- Explicit uniform pointwise control for a product whose roots are samples
from equal-mass intervals. -/
theorem quantilePolynomial_sq_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N C B v : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (n : ℕ) (a sample : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = B)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1/N)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    |(quantilePolynomial n sample).eval v|^2 ≤
      Real.exp (8*C) * (1+B)^4 * N^16 *
        Real.exp (2*N*(∫ w in 0..B, Real.log |v-w| ∂μ)) := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hzero : ∃ j < n, v = sample j
  · obtain ⟨j, hj, hv⟩ := hzero
    rw [quantilePolynomial_eval, Finset.prod_eq_zero (Finset.mem_range.mpr hj)
      (sub_eq_zero.mpr hv)]
    simp only [abs_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hne : ∀ j < n, v ≠ sample j := by simpa only [not_exists, not_and] using hzero
  have hq := log_equalMass_quadrature_log_error μ hN hC hB n a sample
    ha0 han ha hsample hmass hsmall hne
  have hfactor : ∀ j ∈ Finset.range n, 0 < |v-sample j| := by
    intro j hj
    exact abs_pos.mpr (sub_ne_zero.mpr (hne j (Finset.mem_range.mp hj)))
  have hprod : 0 < ∏ j ∈ Finset.range n, |v-sample j| := Finset.prod_pos hfactor
  have hl := Real.log_prod (fun j hj => (hfactor j hj).ne')
  have hsquare : 0 < (∏ j ∈ Finset.range n, |v-sample j|)^2 := pow_pos hprod _
  have heN : Real.exp (16*Real.log N) = N^16 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hNpos] using Real.exp_nat_mul (Real.log N) 16
  have heB : Real.exp (4*Real.log (1+B)) = (1+B)^4 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (show 0 < 1+B by positivity)] using
      Real.exp_nat_mul (Real.log (1+B)) 4
  rw [quantilePolynomial_eval, Finset.abs_prod]
  calc
    (∏ j ∈ Finset.range n, |v-sample j|)^2 =
        Real.exp (Real.log ((∏ j ∈ Finset.range n, |v-sample j|)^2)) :=
      (Real.exp_log hsquare).symm
    _ ≤ Real.exp (2*(N*(∫ w in 0..B, Real.log |v-w| ∂μ) +
          8*Real.log N + 2*Real.log (1+B) + 4*C)) := by
      apply Real.exp_le_exp.mpr
      rw [Real.log_pow, hl]
      norm_num only [Nat.cast_ofNat]
      linarith
    _ = Real.exp (8*C) * (1+B)^4 * N^16 *
        Real.exp (2*N*(∫ w in 0..B, Real.log |v-w| ∂μ)) := by
      rw [show 2*(N*(∫ w in 0..B, Real.log |v-w| ∂μ) +
          8*Real.log N + 2*Real.log (1+B) + 4*C) =
          (8*C + 4*Real.log (1+B)) + 16*Real.log N +
            2*N*(∫ w in 0..B, Real.log |v-w| ∂μ) by ring]
      rw [Real.exp_add, Real.exp_add, Real.exp_add, heN, heB]

noncomputable def scaledQuantilePolynomial (N : ℝ) (n : ℕ) (sample : ℕ → ℝ) : ℝ[X] :=
  quantilePolynomial n (fun j => N^2*sample j)

lemma scaledQuantilePolynomial_eval (N : ℝ) (n : ℕ) (sample : ℕ → ℝ) (v : ℝ) :
    (scaledQuantilePolynomial N n sample).eval (N^2*v) =
      N^(2*n) * (quantilePolynomial n sample).eval v := by
  simp only [scaledQuantilePolynomial, quantilePolynomial_eval]
  simp_rw [← mul_sub]
  rw [Finset.prod_mul_distrib]
  simp [pow_mul]

/-- The scaling `t=N²v` contributes exactly `N^(4n)` to the squared bound. -/
theorem scaledQuantilePolynomial_sq_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N C B v : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (n : ℕ) (a sample : ℕ → ℝ)
    (ha0 : a 0 = 0) (han : a n = B)
    (ha : ∀ j < n, a j ≤ a (j+1))
    (hsample : ∀ j < n, sample j ∈ Icc (a j) (a (j+1)))
    (hmass : ∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1/N)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    |(scaledQuantilePolynomial N n sample).eval (N^2*v)|^2 ≤
      Real.exp (8*C) * (1+B)^4 * N^(4*n+16) *
        Real.exp (2*N*(∫ w in 0..B, Real.log |v-w| ∂μ)) := by
  have hn0 : 0 ≤ N := (zero_le_one.trans hN)
  have hq := quantilePolynomial_sq_bound μ hN hC hB n a sample
    ha0 han ha hsample hmass hsmall
  rw [scaledQuantilePolynomial_eval, abs_mul, abs_of_nonneg (pow_nonneg hn0 _),
    mul_pow, ← pow_mul, show 2*n*2 = 4*n by omega]
  calc
    N^(4*n) * |(quantilePolynomial n sample).eval v|^2 ≤
      N^(4*n) * (Real.exp (8*C) * (1+B)^4 * N^16 *
        Real.exp (2*N*(∫ w in 0..B, Real.log |v-w| ∂μ))) :=
      mul_le_mul_of_nonneg_left hq (pow_nonneg hn0 _)
    _ = _ := by rw [pow_add]; ring

/-- A complete discretization theorem: a finite measure with uniform Hölder
small-ball control supplies monic real trial polynomials, with an explicit
polynomial loss independent of the evaluation point. -/
theorem exists_monic_scaled_trial_polynomial (μ : Measure ℝ) [IsFiniteMeasure μ]
    {N C B : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (n : ℕ) (hn : 0 < n) (hmass : μ.real (Ioc 0 B) = (n : ℝ)/N)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    ∃ p : ℝ[X], p.Monic ∧ p.natDegree = n ∧ ∀ v : ℝ,
      |p.eval (N^2*v)|^2 ≤
        Real.exp (8*C) * (1+B)^4 * N^(4*n+16) *
          Real.exp (2*N*(∫ w in 0..B, Real.log |v-w| ∂μ)) := by
  letI : NullSingletonClass μ := nullSingletonClass_of_fourth_power_smallBall μ hC hsmall
  obtain ⟨a, ha0, han, _hamem, ha, hcells⟩ := exists_equalMass_partition μ
    (lt_of_lt_of_le zero_lt_one hN) hB n hn hmass
  let sample : ℕ → ℝ := fun j => (a j+a (j+1))/2
  have hs (j : ℕ) (hj : j < n) : sample j ∈ Icc (a j) (a (j+1)) := by
    have h := ha j hj
    dsimp [sample]
    constructor <;> linarith
  refine ⟨scaledQuantilePolynomial N n sample,
    quantilePolynomial_monic n _, quantilePolynomial_natDegree n _, ?_⟩
  intro v
  exact scaledQuantilePolynomial_sq_bound μ hN hC hB n a sample ha0 han
    (fun j hj => (ha j hj).le) hs hcells (hsmall v)

end Zeta5.Analysis
