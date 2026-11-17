import Zeta5.Construction.Functional
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact change from the factorial window to monomials

The generic Gram congruence is the polynomial-valued generalization of
`momentGram_change_of_basis` in the four-value proof.  Unlike a scalar moment
matrix, the functional here takes values in `ℚ[X]`.
-/

noncomputable section
namespace Zeta5.Construction
open Polynomial

theorem polynomial_finite_expansion (r : ℕ) (q : ℚ[X]) (hq : q.natDegree < r) :
    q = ∑ i : Fin r, C (q.coeff i.val) * X ^ i.val := by
  simpa only [← Fin.sum_univ_eq_sum_range] using q.as_sum_range_C_mul_X_pow' hq

def coefficientMatrix (r : ℕ) (q : Fin r → ℚ[X]) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => C ((q j).coeff i.val)

def monomialGram (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => L (X ^ (i.val + j.val))

theorem polynomialValuedGram_change_of_basis (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (r : ℕ)
    (q : Fin r → ℚ[X]) (hq : ∀ i, (q i).natDegree < r) :
    (fun i j => L (q i * q j) : Matrix (Fin r) (Fin r) ℚ[X]) =
      (coefficientMatrix r q).transpose * monomialGram L r * coefficientMatrix r q := by
  ext i j : 2
  conv_lhs => rw [polynomial_finite_expansion r (q i) (hq i),
    polynomial_finite_expansion r (q j) (hq j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, monomialGram, coefficientMatrix,
    Finset.sum_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [show (C ((q i).coeff a.val) * X ^ a.val) *
        (C ((q j).coeff b.val) * X ^ b.val) =
      (((q i).coeff a.val) * ((q j).coeff b.val)) • X ^ (a.val + b.val) by
        rw [Polynomial.smul_eq_C_mul, map_mul, pow_add]; ring,
    map_smul, Polynomial.smul_eq_C_mul, map_mul]
  ring

def commonFactor (m : ℕ) : ℚ[X] := (rootPolynomial m).comp (-X)

def tailFactor (m k : ℕ) : ℚ[X] :=
  ∏ a ∈ Finset.range k, (-X - C (((m + a : ℕ) : ℚ) ^ 2))

def windowTail (m k : ℕ) : ℚ[X] :=
  C ((Nat.factorial (2 * (m + k)) : ℚ)⁻¹) * tailFactor m k

theorem commonFactor_add (m k : ℕ) :
    commonFactor (m + k) = commonFactor m * tailFactor m k := by
  simp only [commonFactor, rootPolynomial, prod_comp, sub_comp, X_comp, C_comp]
  rw [Finset.prod_range_add]
  simp only [tailFactor, Nat.cast_add]

theorem windowBasis_eq_commonFactor_mul_tail (m k : ℕ) :
    windowBasis (m + k) = commonFactor m * windowTail m k := by
  simp only [windowBasis, centralPolynomial, mul_comp, C_comp]
  change C _ * commonFactor (m + k) = _
  rw [commonFactor_add, windowTail]
  ring

theorem tailFactor_natDegree (m k : ℕ) : (tailFactor m k).natDegree = k := by
  have heq : ∀ a : ℕ, (-X - C (((m + a : ℕ) : ℚ) ^ 2) : ℚ[X]) =
      -(X + C (((m + a : ℕ) : ℚ) ^ 2)) := fun a => by ring
  simp only [tailFactor, heq]
  rw [natDegree_prod]
  · simp only [natDegree_neg, natDegree_X_add_C, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  · intro a ha
    exact neg_ne_zero.mpr (monic_X_add_C _).ne_zero

theorem tailFactor_leadingCoeff (m k : ℕ) :
    (tailFactor m k).leadingCoeff = (-1 : ℚ) ^ k := by
  rw [tailFactor, leadingCoeff_prod]
  simp only [show ∀ a : ℕ, (-X - C (((m + a : ℕ) : ℚ) ^ 2) : ℚ[X]) =
      -(X + C (((m + a : ℕ) : ℚ) ^ 2)) from fun a => by ring,
    leadingCoeff_neg, leadingCoeff_X_add_C, Finset.prod_const, Finset.card_range]

theorem windowTail_natDegree (m k : ℕ) : (windowTail m k).natDegree = k := by
  rw [windowTail, natDegree_C_mul (inv_ne_zero (factorial_cast_ne_zero _)),
    tailFactor_natDegree]

theorem windowTail_leadingCoeff (m k : ℕ) :
    (windowTail m k).leadingCoeff =
      (Nat.factorial (2 * (m + k)) : ℚ)⁻¹ * (-1 : ℚ) ^ k := by
  rw [windowTail, leadingCoeff_mul, leadingCoeff_C, tailFactor_leadingCoeff]

def weightedNumeratorFunctional (N m : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional N).comp (LinearMap.mulLeft ℚ ((commonFactor m) ^ 2))

def monomialPencil (N m r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  monomialGram (weightedNumeratorFunctional N m) r

def windowTailMatrix (m r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  coefficientMatrix r (fun k => windowTail m k.val)

theorem unscaledWindow_congruence (N m r : ℕ) :
    (fun i j : Fin r => numeratorFunctional N
      (windowBasis (m + i.val) * windowBasis (m + j.val))) =
      (windowTailMatrix m r).transpose * monomialPencil N m r * windowTailMatrix m r := by
  have h := polynomialValuedGram_change_of_basis (weightedNumeratorFunctional N m) r
    (fun k => windowTail m k.val) (fun k => by rw [windowTail_natDegree]; exact k.isLt)
  change _ = (coefficientMatrix r (fun k => windowTail m k.val)).transpose *
    monomialGram (weightedNumeratorFunctional N m) r *
      coefficientMatrix r (fun k => windowTail m k.val)
  rw [← h]
  funext i j
  simp only [windowBasis_eq_commonFactor_mul_tail, weightedNumeratorFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply]
  congr 1
  ring

theorem windowTailMatrix_isUpperTriangular (m r : ℕ) :
    (windowTailMatrix m r).IsUpperTriangular := by
  intro i j hij
  change C ((windowTail m j.val).coeff i.val) = 0
  rw [coeff_eq_zero_of_natDegree_lt, C_0]
  rw [windowTail_natDegree]
  exact hij

theorem windowTailMatrix_det (m r : ℕ) :
    (windowTailMatrix m r).det =
      ∏ k : Fin r, C ((Nat.factorial (2 * (m + k.val)) : ℚ)⁻¹ * (-1 : ℚ) ^ k.val) := by
  rw [Matrix.det_of_isUpperTriangular (windowTailMatrix_isUpperTriangular m r)]
  apply Finset.prod_congr rfl
  intro k hk
  change C ((windowTail m k.val).coeff k.val) = _
  have hc := coeff_natDegree (p := windowTail m k.val)
  rw [windowTail_natDegree] at hc
  rw [hc, windowTail_leadingCoeff]

theorem windowTailMatrix_det_sq (m r : ℕ) :
    (windowTailMatrix m r).det ^ 2 =
      C (∏ k : Fin r, ((Nat.factorial (2 * (m + k.val)) : ℚ)⁻¹) ^ 2) := by
  rw [windowTailMatrix_det, ← Finset.prod_pow, map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [← map_pow, mul_pow]
  have hs : ((-1 : ℚ) ^ k.val) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k.val 2, pow_mul]
    norm_num
  rw [hs, mul_one]

/-- The exact factorial prefactor for the manuscript's change of basis. -/
theorem windowDeterminant_change_of_basis (N m r : ℕ) :
    Matrix.det (fun i j : Fin r => entry N (m + i.val) (m + j.val)) =
      C ((Nat.factorial N : ℚ) ^ (2 * r) *
        ∏ k : Fin r, ((Nat.factorial (2 * (m + k.val)) : ℚ)⁻¹) ^ 2) *
        (monomialPencil N m r).det := by
  have heq : (fun i j : Fin r => entry N (m + i.val) (m + j.val)) =
      C ((Nat.factorial N : ℚ) ^ 2) •
        ((windowTailMatrix m r).transpose * monomialPencil N m r * windowTailMatrix m r) := by
    rw [← unscaledWindow_congruence]
    funext i j
    exact entry_eq_numeratorFunctional N (m + i.val) (m + j.val)
  rw [heq, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [show (windowTailMatrix m r).det * (monomialPencil N m r).det *
      (windowTailMatrix m r).det =
      (windowTailMatrix m r).det ^ 2 * (monomialPencil N m r).det by ring]
  rw [windowTailMatrix_det_sq, ← mul_assoc, ← map_pow, ← map_mul]
  simp only [Fintype.card_fin, ← pow_mul]

theorem concrete_windowDeterminant_change_of_basis (n : ℕ) :
    windowDeterminant n =
      C ((Nat.factorial (20 * n) : ℚ) ^ (48 * n) *
        ∏ k : Fin (24 * n), ((Nat.factorial (2 * (n + k.val)) : ℚ)⁻¹) ^ 2) *
        (monomialPencil (20 * n) n (24 * n)).det := by
  have h := windowDeterminant_change_of_basis (20 * n) n (24 * n)
  change Matrix.det (fun i j : Fin (24 * n) => entry (20 * n) (n + i.val) (n + j.val)) = _
  simpa only [show 2 * (24 * n) = 48 * n by omega] using h

#print axioms concrete_windowDeterminant_change_of_basis


end Zeta5.Construction
