import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The manuscript's central-factorial polynomials

`rootPolynomial j` is the unnormalized product with roots `0²,…,(j-1)²`.
`centralPolynomial j` is the manuscript's `P_j`, and `windowBasis j` is
`B_j(t) = P_j(-t)`.  The denominator is `D_N(t) = ∏_{i=1}^N (t+i²)`.
All definitions in this file use rational coefficients.
-/

noncomputable section
namespace Zeta5.Construction

open Polynomial

def rootPolynomial (j : ℕ) : ℚ[X] :=
  ∏ a ∈ Finset.range j, (X - C ((a : ℚ) ^ 2))

def centralPolynomial (j : ℕ) : ℚ[X] :=
  C ((Nat.factorial (2 * j) : ℚ)⁻¹) * rootPolynomial j

def windowBasis (j : ℕ) : ℚ[X] := (centralPolynomial j).comp (-X)

def denominator (N : ℕ) : ℚ[X] :=
  ∏ i ∈ Finset.range N, (X + C (((i + 1 : ℕ) : ℚ) ^ 2))

theorem rootPolynomial_monic (j : ℕ) : (rootPolynomial j).Monic := by
  exact monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C _)

theorem rootPolynomial_natDegree (j : ℕ) : (rootPolynomial j).natDegree = j := by
  rw [rootPolynomial, natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro a ha
    exact monic_X_sub_C _

theorem rootPolynomial_ne_zero (j : ℕ) : rootPolynomial j ≠ 0 :=
  (rootPolynomial_monic j).ne_zero

theorem rootPolynomial_dvd_of_le {m j : ℕ} (h : m ≤ j) :
    rootPolynomial m ∣ rootPolynomial j := by
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

theorem rootPolynomial_eval_square_eq_zero {i j : ℕ} (hij : i < j) :
    (rootPolynomial j).eval ((i : ℚ) ^ 2) = 0 := by
  rw [rootPolynomial, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hij)
  simp

theorem factorial_cast_ne_zero (j : ℕ) : (Nat.factorial (2 * j) : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero (2 * j)

theorem centralPolynomial_natDegree (j : ℕ) :
    (centralPolynomial j).natDegree = j := by
  rw [centralPolynomial, natDegree_C_mul]
  · exact rootPolynomial_natDegree j
  · exact inv_ne_zero (factorial_cast_ne_zero j)

theorem centralPolynomial_ne_zero (j : ℕ) : centralPolynomial j ≠ 0 := by
  exact mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (factorial_cast_ne_zero j)))
    (rootPolynomial_ne_zero j)

theorem centralPolynomial_eval_square_eq_zero {i j : ℕ} (hij : i < j) :
    (centralPolynomial j).eval ((i : ℚ) ^ 2) = 0 := by
  simp [centralPolynomial, rootPolynomial_eval_square_eq_zero hij]

theorem windowBasis_natDegree (j : ℕ) : (windowBasis j).natDegree = j := by
  simp [windowBasis, natDegree_comp, centralPolynomial_natDegree]

theorem windowBasis_eval_neg_square_eq_zero {i j : ℕ} (hij : i < j) :
    (windowBasis j).eval (-((i : ℚ) ^ 2)) = 0 := by
  simp [windowBasis, eval_comp, centralPolynomial_eval_square_eq_zero hij]

theorem denominator_monic (N : ℕ) : (denominator N).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_add_C _

theorem denominator_ne_zero (N : ℕ) : denominator N ≠ 0 :=
  (denominator_monic N).ne_zero

theorem denominator_natDegree (N : ℕ) : (denominator N).natDegree = N := by
  rw [denominator, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro i hi
    exact monic_X_add_C _

theorem denominator_eval_neg_square_eq_zero {i N : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    (denominator N).eval (-((i : ℚ) ^ 2)) = 0 := by
  rw [denominator, eval_prod]
  apply Finset.prod_eq_zero (i := i - 1) (Finset.mem_range.mpr (by omega))
  have his : i - 1 + 1 = i := by omega
  simp [his]

end Zeta5.Construction
