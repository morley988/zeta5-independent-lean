import Zeta5.Analysis.PolynomialGram
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Gram determinant bounds for arbitrary monic trial polynomials

Cauchy--Schwarz follows directly from positivity on polynomial squares.
Leibniz's determinant formula then gives the sufficient bound `r!` times the
product of diagonal norms.  A monic triangular change of basis preserves the
determinant, so no orthogonal-polynomial minimizer is assumed or constructed.
-/

open Polynomial Matrix
open scoped BigOperators

namespace Zeta5.Analysis

lemma positive_square_nonneg (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p^2)) (p : ℝ[X]) : 0 ≤ L (p^2) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact (hL p hp).le

lemma positive_square_cauchy_schwarz (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p^2)) (p q : ℝ[X]) (hq : q ≠ 0) :
    (L (p*q))^2 ≤ L (p^2)*L (q^2) := by
  let b := L (q^2)
  let c := L (p*q)
  have hb : 0 < b := hL q hq
  have hpoly : (b • p-c • q)^2 =
      (b*b) • (p^2)-(2*b*c) • (p*q)+(c*c) • (q^2) := by
    simp only [Polynomial.smul_eq_C_mul, map_mul, map_ofNat]
    ring
  have h := positive_square_nonneg L hL (b • p-c • q)
  rw [hpoly, map_add, map_sub, map_smul, map_smul, map_smul] at h
  simp only [smul_eq_mul] at h
  change 0 ≤ b*b*L (p^2)-2*b*c*c+c*c*b at h
  have hc : c^2 ≤ L (p^2)*b := by nlinarith
  exact hc

lemma positive_square_abs_mul_le (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p^2)) (p q : ℝ[X]) (hq : q ≠ 0) :
    |L (p*q)| ≤ Real.sqrt (L (p^2))*Real.sqrt (L (q^2)) := by
  have hp0 := positive_square_nonneg L hL p
  have hq0 := positive_square_nonneg L hL q
  have h := positive_square_cauchy_schwarz L hL p q hq
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hq0] using h

lemma abs_det_le_factorial_prod_of_entry_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hA : ∀ i j, |A i j| ≤ d i*d j) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ)*∏ i, (d i)^2 := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |(Equiv.Perm.sign σ : ℝ)*∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      have hsign : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
        exact_mod_cast Equiv.Perm.sign_abs σ
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, (d i)^2 := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ i, d (σ i)*d i :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, (d i)^2 := by
          rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]
          simp only [pow_two, Finset.prod_mul_distrib]
    _ = _ := by simp [Fintype.card_perm]

theorem polynomialGram_det_le_factorial_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p^2))
    (p : ι → ℝ[X]) (hp : ∀ i, p i ≠ 0) :
    (polynomialGram L p).det ≤ (Nat.factorial (Fintype.card ι) : ℝ)*∏ i, L ((p i)^2) := by
  apply (le_abs_self _).trans
  have h := abs_det_le_factorial_prod_of_entry_bound (polynomialGram L p)
    (fun i => Real.sqrt (L ((p i)^2))) (fun i => Real.sqrt_nonneg _)
    (fun i j => positive_square_abs_mul_le L hL (p i) (p j) (hp j))
  simpa only [Real.sq_sqrt (positive_square_nonneg L hL _)] using h

noncomputable def realCoefficientMatrix (r : ℕ) (p : Fin r → ℝ[X]) :
    Matrix (Fin r) (Fin r) ℝ := fun i j => (p j).coeff i.val

noncomputable def realMonomialGram (L : ℝ[X] →ₗ[ℝ] ℝ) (r : ℕ) :
    Matrix (Fin r) (Fin r) ℝ := polynomialGram L (fun i => X^i.val)

lemma real_polynomial_finite_expansion (r : ℕ) (p : ℝ[X]) (hp : p.natDegree < r) :
    p = ∑ i : Fin r, (p.coeff i.val) • X^i.val := by
  simpa only [← Fin.sum_univ_eq_sum_range, Polynomial.smul_eq_C_mul] using
    p.as_sum_range_C_mul_X_pow' hp

theorem real_polynomialGram_change_of_basis (L : ℝ[X] →ₗ[ℝ] ℝ) (r : ℕ)
    (p : Fin r → ℝ[X]) (hp : ∀ i, (p i).natDegree < r) :
    polynomialGram L p =
      (realCoefficientMatrix r p).transpose * realMonomialGram L r *
        realCoefficientMatrix r p := by
  ext i j : 2
  change L (p i*p j) = _
  conv_lhs => rw [real_polynomial_finite_expansion r (p i) (hp i),
    real_polynomial_finite_expansion r (p j) (hp j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, realMonomialGram, realCoefficientMatrix,
    polynomialGram, Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma monic_coefficientMatrix_det (r : ℕ) (p : Fin r → ℝ[X])
    (hpm : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = i.val) :
    (realCoefficientMatrix r p).det = 1 := by
  have htri : (realCoefficientMatrix r p).IsUpperTriangular := by
    intro i j hij
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpd]
    exact hij
  rw [Matrix.det_of_isUpperTriangular htri]
  have hdiag (i : Fin r) : realCoefficientMatrix r p i i = 1 := by
    change (p i).coeff i.val = 1
    rw [← hpd i, coeff_natDegree, (hpm i).leadingCoeff]
  simp only [hdiag, Finset.prod_const_one]

/-- Every monic degree-ordered family gives exactly the same Gram determinant
as the monomials. -/
theorem monic_polynomialGram_det_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (r : ℕ)
    (p : Fin r → ℝ[X]) (hpm : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = i.val) :
    (polynomialGram L p).det = (realMonomialGram L r).det := by
  rw [real_polynomialGram_change_of_basis L r p (fun i => by rw [hpd]; exact i.isLt),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    monic_coefficientMatrix_det r p hpm hpd, one_mul, mul_one]

/-- The determinant bound needed for the asymptotic proof, for any supplied
monic trial family.  The factorial loss is only of order `r log r` in logs. -/
theorem realMonomialGram_det_le_trial_product (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p^2)) (r : ℕ) (p : Fin r → ℝ[X])
    (hpm : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = i.val) :
    (realMonomialGram L r).det ≤ (Nat.factorial r : ℝ)*∏ i, L ((p i)^2) := by
  rw [← monic_polynomialGram_det_eq L r p hpm hpd]
  simpa only [Fintype.card_fin] using polynomialGram_det_le_factorial_prod L hL p
    (fun i => (hpm i).ne_zero)

end Zeta5.Analysis
