import Zeta5.Arithmetic.BernoulliLoss
import Zeta5.Construction.Functional

/-! # The exact Bernoulli functional representation of the rational moments -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

def bernoulliMomentNumerator (P : ℚ[X]) : ℚ[X] := X ^ 5 * P.comp (-(X ^ 2))

theorem bernoulliMomentNumerator_add (P Q : ℚ[X]) :
    bernoulliMomentNumerator (P + Q) = bernoulliMomentNumerator P + bernoulliMomentNumerator Q := by
  simp only [bernoulliMomentNumerator, add_comp, mul_add]

theorem bernoulliMomentNumerator_monomial (n : ℕ) (a : ℚ) :
    bernoulliMomentNumerator (monomial n a) = C (a * (-1 : ℚ) ^ n) * X ^ (2 * n + 5) := by
  apply Polynomial.funext
  intro x
  simp only [bernoulliMomentNumerator, eval_mul, eval_pow, eval_X, eval_comp,
    eval_neg, eval_monomial, eval_C]
  rw [neg_pow, pow_add, pow_mul]
  ring

theorem bernoulliMomentNumerator_natDegree_le (P : ℚ[X]) :
    (bernoulliMomentNumerator P).natDegree ≤ 2 * P.natDegree + 5 := by
  apply (natDegree_mul_le).trans
  rw [natDegree_X_pow, natDegree_comp, natDegree_neg, natDegree_X_pow]
  omega

theorem bernoulliMoment_monomial (n : ℕ) (a : ℚ) :
    (1 / 24 : ℚ) * bernoulliFunctional (derivative^[3] (bernoulliMomentNumerator (monomial n a))) =
      a * rationalMoment n := by
  rw [bernoulliMomentNumerator_monomial]
  change (1 / 24 : ℚ) * bernoulliFunctional
    (derivative (derivative (derivative (C (a * (-1 : ℚ) ^ n) * X ^ (2 * n + 5))))) = _
  rw [derivative_C_mul_X_pow, show 2 * n + 5 - 1 = 2 * n + 4 by omega,
    derivative_C_mul_X_pow, show 2 * n + 4 - 1 = 2 * n + 3 by omega,
    derivative_C_mul_X_pow, show 2 * n + 3 - 1 = 2 * n + 2 by omega,
    bernoulliFunctional_C_mul, bernoulliFunctional_X_pow]
  simp only [rationalMoment]
  push_cast
  ring

/-- The manuscript's exact identity J(P)=B((x⁵P(-x²))''')/24. -/
theorem polynomialMoment_eq_bernoulliFunctional (P : ℚ[X]) :
    polynomialMoment P =
      (1 / 24 : ℚ) * bernoulliFunctional (derivative^[3] (bernoulliMomentNumerator P)) := by
  change polynomialMomentMap P = _
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, bernoulliMomentNumerator_add]
    change _ = (1 / 24 : ℚ) * bernoulliFunctional (derivative (derivative (derivative _)))
    simp only [derivative_add, map_add, mul_add]
    rfl
  | monomial n a =>
    rw [bernoulliMoment_monomial]
    simp [polynomialMomentMap, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

variable {p : ℕ} [Fact p.Prime]

/-- The degree threshold and the integer-value bound on the actual transformed
quotient give exactly the four-power loss used by the manuscript. -/
theorem polynomialMoment_padicLower_of_integerValuedNumerator {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hp : 5 < p) (hP : IntegerValuedLower p w (bernoulliMomentNumerator P))
    (hL : (bernoulliMomentNumerator P).natDegree ≤ L) (hLp : L + 1 < p ^ 2) :
    PadicLower p (w - 4) (polynomialMoment P) := by
  rw [polynomialMoment_eq_bernoulliFunctional]
  have h := (twentyFour_prime_integral (p := p) hp).mul
    (bernoulliFunctional_iterate_derivative_below_square hP hL hLp 3)
  simpa only [Nat.cast_ofNat, zero_add, show w - 3 - 1 = w - 4 by omega] using h

/-- All-prime version with the logarithmic derivative/evaluation cost and
the exact valuation of the fixed factor 24. -/
theorem polynomialMoment_padicLower_log {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w (bernoulliMomentNumerator P))
    (hL : (bernoulliMomentNumerator P).natDegree ≤ L) :
    PadicLower p (w - 4 * (Nat.log p (L + 1) : ℤ) - (padicValNat p 24 : ℤ))
      (polynomialMoment P) := by
  rw [polynomialMoment_eq_bernoulliFunctional]
  have h24 : PadicLower p (-(padicValNat p 24 : ℤ)) (1 / 24 : ℚ) := by
    right
    simp only [one_div, padicValRat.inv]
    norm_cast
  have h := h24.mul (bernoulliFunctional_iterate_derivative_log hP hL 3)
  convert h using 1 <;> push_cast <;> ring

end Zeta5.Arithmetic
