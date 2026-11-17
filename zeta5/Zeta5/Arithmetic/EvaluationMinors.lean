import Zeta5.Arithmetic.Moments
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-!
# Vandermonde divisibility of arbitrary polynomial evaluation determinants

Reducing every column polynomial modulo the monic node polynomial produces
an integral coefficient matrix of degree below the number of nodes. Hence
the evaluation matrix factors as a Vandermonde matrix times an integral
matrix. This proves the full Vandermonde divisibility for arbitrary selected
monomials, including nonconsecutive exponent selections.

The valuation consequence allows every pair of congruent nodes to contribute
one power of the prime. It is stronger than a rank-only first-order bound.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Matrix Finset OddZeta.FourValue
open scoped BigOperators

def evaluationNodePolynomial {n : ℕ} (t : Fin n → ℤ) : ℤ[X] :=
  ∏ i : Fin n, (X - C (t i))

theorem evaluationNodePolynomial_monic {n : ℕ} (t : Fin n → ℤ) :
    (evaluationNodePolynomial t).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)

theorem evaluationNodePolynomial_natDegree {n : ℕ} (t : Fin n → ℤ) :
    (evaluationNodePolynomial t).natDegree = n := by
  rw [evaluationNodePolynomial, natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
  · intro i hi
    exact monic_X_sub_C _

theorem evaluationNodePolynomial_eval {n : ℕ} (t : Fin n → ℤ) (i : Fin n) :
    (evaluationNodePolynomial t).eval (t i) = 0 := by
  rw [evaluationNodePolynomial, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

def evaluationRemainder {n : ℕ} (t : Fin n → ℤ) (P : ℤ[X]) : ℤ[X] :=
  P %ₘ evaluationNodePolynomial t

theorem evaluationRemainder_eval {n : ℕ} (t : Fin n → ℤ) (P : ℤ[X]) (i : Fin n) :
    (evaluationRemainder t P).eval (t i) = P.eval (t i) := by
  simpa [evaluationRemainder] using
    (eval₂_modByMonic_eq_self_of_root (f := RingHom.id ℤ) (p := P)
      (by simpa using evaluationNodePolynomial_eval t i))

theorem evaluationRemainder_natDegree {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℤ) (P : ℤ[X]) : (evaluationRemainder t P).natDegree < n := by
  have hne : evaluationNodePolynomial t ≠ 1 := by
    intro h
    have hd := evaluationNodePolynomial_natDegree t
    rw [h, natDegree_one] at hd
    omega
  have h := natDegree_modByMonic_lt P (evaluationNodePolynomial_monic t) hne
  simpa [evaluationRemainder, evaluationNodePolynomial_natDegree] using h

def evaluationCoefficientMatrix {n : ℕ} (t : Fin n → ℤ) (P : Fin n → ℤ[X]) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k j => (evaluationRemainder t (P j)).coeff k

theorem polynomialEvaluationMatrix_factorization {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℤ) (P : Fin n → ℤ[X]) :
    Matrix.of (fun i j => (P j).eval (t i)) =
      Matrix.vandermonde t * evaluationCoefficientMatrix t P := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, Matrix.vandermonde_apply, evaluationCoefficientMatrix]
  rw [← evaluationRemainder_eval t (P j) i]
  have hd := evaluationRemainder_natDegree hn t (P j)
  rw [(evaluationRemainder t (P j)).eval_eq_sum_range' hd]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [mul_comm]

/-- Every polynomial evaluation determinant over the integers contains
the complete Vandermonde factor, even for arbitrary column degrees. -/
theorem vandermonde_dvd_polynomialEvaluationDet {n : ℕ}
    (t : Fin n → ℤ) (P : Fin n → ℤ[X]) :
    (Matrix.vandermonde t).det ∣ (Matrix.of fun i j => (P j).eval (t i)).det := by
  cases n with
  | zero => simp
  | succ n =>
    rw [polynomialEvaluationMatrix_factorization (Nat.succ_pos _) t P, Matrix.det_mul]
    exact dvd_mul_right _ _

theorem pairProduct_dvd_polynomialEvaluationDet {n : ℕ}
    (t : Fin n → ℤ) (P : Fin n → ℤ[X]) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (t j - t i)) ∣
      (Matrix.of fun i j => (P j).eval (t i)).det := by
  rw [← Matrix.det_vandermonde]
  exact vandermonde_dvd_polynomialEvaluationDet t P

variable {p : ℕ} [Fact p.Prime]

theorem padicLower_int_of_dvd (a : ℤ) (hpa : (p : ℤ) ∣ a) :
    PadicLower p 1 (a : ℚ) := by
  obtain ⟨b, rfl⟩ := hpa
  have hp : PadicLower p 1 (p : ℚ) := by
    right
    rw [padicValRat.self (Fact.out : p.Prime).one_lt]
  simpa using hp.mul (padicLower_int (p := p) b)

/-- Pairwise valuation gains add before multiplying by the integral
coefficient determinant. The supplied weights can be the indicators of
belonging to the same residue class. -/
theorem polynomialEvaluationDet_padicLower {n : ℕ}
    (t : Fin n → ℤ) (P : Fin n → ℤ[X]) (weight : Fin n → Fin n → ℤ)
    (hweight : ∀ i j, i < j → PadicLower p (weight i j) ((t j - t i : ℤ) : ℚ)) :
    PadicLower p (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, weight i j)
      (((Matrix.of fun i j => (P j).eval (t i)).det : ℤ) : ℚ) := by
  obtain ⟨q, hq⟩ := pairProduct_dvd_polynomialEvaluationDet t P
  rw [hq]
  push_cast
  have hprod : PadicLower p (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, weight i j)
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((t j : ℚ) - (t i : ℚ))) := by
    apply padicLower_prod
    intro i hi
    apply padicLower_prod
    intro j hj
    simpa using hweight i j (Finset.mem_Ioi.mp hj)
  simpa using hprod.mul (padicLower_int (p := p) q)

/-- The form used by a selected monomial evaluation minor. -/
theorem monomialEvaluationDet_padicLower {n : ℕ}
    (t : Fin n → ℤ) (exponent : Fin n → ℕ) (weight : Fin n → Fin n → ℤ)
    (hweight : ∀ i j, i < j → PadicLower p (weight i j) ((t j - t i : ℤ) : ℚ)) :
    PadicLower p (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, weight i j)
      (Matrix.of fun i j => (t i : ℚ) ^ exponent j).det := by
  have h := polynomialEvaluationDet_padicLower t
    (fun j => (X : ℤ[X]) ^ exponent j) weight hweight
  have he : (Matrix.of (fun i j => t i ^ exponent j)).map (fun x : ℤ => (x : ℚ)) =
      Matrix.of (fun i j => (t i : ℚ) ^ exponent j) := by
    ext i j
    simp
  simpa [Int.cast_det, he] using h

def orderedIndexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

theorem sum_Ioi_eq_sum_orderedIndexPairs {n : ℕ} (f : Fin n → Fin n → ℤ) :
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, f i j) =
      ∑ ij ∈ orderedIndexPairs n, f ij.1 ij.2 := by
  unfold orderedIndexPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i < j) := by
    ext j
    simp
  rw [he, Finset.sum_filter]

theorem orderedIndexPairs_card (n : ℕ) : (orderedIndexPairs n).card = n.choose 2 := by
  unfold orderedIndexPairs
  simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

theorem sum_Ioi_one (n : ℕ) :
    (∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, (1 : ℤ)) = (n.choose 2 : ℤ) := by
  rw [sum_Ioi_eq_sum_orderedIndexPairs]
  simp [orderedIndexPairs_card]

/-- A minor whose nodes all belong to one residue class gains
`choose(n,2)` powers of the prime, regardless of the selected exponents. -/
theorem monomialEvaluationDet_same_residue {n : ℕ}
    (t : Fin n → ℤ) (exponent : Fin n → ℕ)
    (hcongr : ∀ i j, i < j → (p : ℤ) ∣ t j - t i) :
    PadicLower p (n.choose 2 : ℤ)
      (Matrix.of fun i j => (t i : ℚ) ^ exponent j).det := by
  have h := monomialEvaluationDet_padicLower t exponent (fun _ _ => 1)
    (fun i j hij => padicLower_int_of_dvd _ (hcongr i j hij))
  simpa only [sum_Ioi_one] using h

def congruentIndexPairs {n : ℕ} (p : ℕ) (t : Fin n → ℤ) : Finset (Fin n × Fin n) :=
  (orderedIndexPairs n).filter fun ij => (p : ℤ) ∣ t ij.2 - t ij.1

theorem monomialEvaluationDet_congruent_pairs {n : ℕ}
    (t : Fin n → ℤ) (exponent : Fin n → ℕ) :
    PadicLower p ((congruentIndexPairs p t).card : ℤ)
      (Matrix.of fun i j => (t i : ℚ) ^ exponent j).det := by
  classical
  have h := monomialEvaluationDet_padicLower t exponent
    (fun i j => if (p : ℤ) ∣ t j - t i then 1 else 0) (by
      intro i j hij
      split_ifs with hd
      · exact padicLower_int_of_dvd _ hd
      · exact padicLower_int _)
  rw [sum_Ioi_eq_sum_orderedIndexPairs] at h
  simpa [congruentIndexPairs] using h

end Zeta5.Arithmetic
