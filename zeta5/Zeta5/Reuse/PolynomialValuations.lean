import Zeta5.Arithmetic.Moments
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Coefficientwise valuation calculus

The definition and multiplication, constant, addition, finite-sum, power,
Taylor, and integral-composition arguments are adapted from
`FourValueArithmeticDenominators`, `FourValueTaylorDenominators`, and
`FourValueUniformLaurent` at the reference commit documented in PadicMinors.
Those sources are MIT-licensed. The determinant extension below is new.
-/

noncomputable section
namespace OddZeta.FourValue
open Polynomial
variable {p : ℕ} [Fact p.Prime]

def PolynomialPadicLower (p : ℕ) (w : ℤ) (P : ℚ[X]) : Prop :=
  ∀ j, PadicLower p w (P.coeff j)

theorem PolynomialPadicLower.zero (w : ℤ) : PolynomialPadicLower p w 0 := by
  intro j
  exact PadicLower.zero w

theorem PolynomialPadicLower.mono {v w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (hvw : v ≤ w) : PolynomialPadicLower p v P :=
  fun j => (hP j).mono hvw

theorem PolynomialPadicLower.mul {v w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p v P) (hQ : PolynomialPadicLower p w Q) :
    PolynomialPadicLower p (v + w) (P * Q) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact padicLower_sum _ _ _ (fun ij hij => (hP ij.1).mul (hQ ij.2))

theorem PolynomialPadicLower.constant {w : ℤ} {q : ℚ} (hq : PadicLower p w q) :
    PolynomialPadicLower p w (C q) := by
  intro j
  by_cases hj : j = 0
  · simpa [hj] using hq
  · simp [Polynomial.coeff_C, hj, PadicLower]

theorem PolynomialPadicLower.neg {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) : PolynomialPadicLower p w (-P) := by
  intro j
  simpa only [coeff_neg] using (hP j).neg

theorem PolynomialPadicLower.add {w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (hQ : PolynomialPadicLower p w Q) :
    PolynomialPadicLower p w (P + Q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (hP j).add (hQ j)

theorem PolynomialPadicLower.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (w : ℤ)
    (hf : ∀ i ∈ s, PolynomialPadicLower p w (f i)) :
    PolynomialPadicLower p w (∑ i ∈ s, f i) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact padicLower_sum s _ w (fun i hi => hf i hi j)

theorem PolynomialPadicLower.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (w : ι → ℤ)
    (hf : ∀ i ∈ s, PolynomialPadicLower p (w i) (f i)) :
    PolynomialPadicLower p (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using PolynomialPadicLower.constant (Zeta5.Arithmetic.padicLower_nat (p := p) 1)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

theorem PolynomialPadicLower.pow {w : ℤ} {P : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (k : ℕ) :
    PolynomialPadicLower p ((k : ℤ) * w) (P ^ k) := by
  induction k with
  | zero =>
      simpa using PolynomialPadicLower.constant (Zeta5.Arithmetic.padicLower_nat (p := p) 1)
  | succ k ih => simpa [pow_succ, add_mul] using ih.mul hP

theorem polynomialPadicLower_X : PolynomialPadicLower p 0 (X : ℚ[X]) := by
  intro j
  by_cases hj : j = 1
  · subst j
    simpa using Zeta5.Arithmetic.padicLower_nat (p := p) 1
  · simp [coeff_X, Ne.symm hj, PadicLower]

theorem PolynomialPadicLower.comp_integral {w : ℤ} {P Q : ℚ[X]}
    (hP : PolynomialPadicLower p w P) (hQ : PolynomialPadicLower p 0 Q) :
    PolynomialPadicLower p w (P.comp Q) := by
  rw [P.as_sum_range_C_mul_X_pow]
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  apply PolynomialPadicLower.sum
  intro i hi
  simpa using (PolynomialPadicLower.constant (hP i)).mul (hQ.pow i)

theorem PolynomialPadicLower.eval_integral {w : ℤ} {P : ℚ[X]} {x : ℚ}
    (hP : PolynomialPadicLower p w P) (hx : PadicLower p 0 x) :
    PadicLower p w (P.eval x) := by
  have h := hP.comp_integral (PolynomialPadicLower.constant hx)
  rw [comp_C] at h
  simpa using h 0

theorem polynomialPadicLower_integer_map (P : ℤ[X]) :
    PolynomialPadicLower p 0 (P.map (Int.castRingHom ℚ)) := by
  intro j
  rw [coeff_map]
  change PadicLower p 0 ((P.coeff j : ℤ) : ℚ)
  exact Zeta5.Arithmetic.padicLower_int (p := p) (P.coeff j)

theorem PolynomialPadicLower.sign_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : ℤ} {P : ℚ[X]} (hP : PolynomialPadicLower p w P) (σ : Equiv.Perm ι) :
    PolynomialPadicLower p w (Equiv.Perm.sign σ • P) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hP
  · simpa [hs] using hP.neg

theorem polynomialPadicLower_det_weighted {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (row col : ι → ℤ) (c : ℤ)
    (hA : ∀ i j, PolynomialPadicLower p (row i + col j + c) (A i j)) :
    PolynomialPadicLower p ((∑ i, row i) + (∑ j, col j) + Fintype.card ι * c) A.det := by
  rw [Matrix.det_apply]
  apply PolynomialPadicLower.sum
  intro σ _
  apply PolynomialPadicLower.sign_smul
  have h := PolynomialPadicLower.prod (p := p) Finset.univ
    (fun i => A (σ i) i) (fun i => row (σ i) + col i + c)
    (fun i _ => hA (σ i) i)
  simpa only [Finset.sum_add_distrib, Equiv.sum_comp, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

end OddZeta.FourValue
