import Zeta5.Arithmetic.BernoulliFunctional
import Zeta5.Arithmetic.NewtonDerivative

/-! # Weighted Bernoulli evaluation and derivative losses -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue

variable {p : ℕ} [Fact p.Prime]

theorem bernoulliFunctional_integerValuedLower {P : ℚ[X]} {w d : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w P) (hL : P.natDegree ≤ L)
    (hden : ∀ b : ℕ, 0 < b → b ≤ L + 1 → PadicLower p (-d) ((b : ℚ)⁻¹)) :
    PadicLower p (w - d) (bernoulliFunctional P) := by
  rw [← newtonExpansion_eq P hL, newtonExpansion, map_sum]
  apply padicLower_sum
  intro n hn
  rw [bernoulliFunctional_C_mul, bernoulliFunctional_binomialPolynomial, div_eq_mul_inv]
  have hr := hden (n + 1) (by omega) (by have := mem_range.mp hn; omega)
  have hs : PadicLower p 0 ((-1 : ℚ) ^ n) := by
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ n)
  simpa only [Nat.cast_add, Nat.cast_one, zero_add, sub_eq_add_neg] using
    (newtonCoefficient_padicLower_weighted hP n).mul (hs.mul hr)

theorem bernoulliFunctional_integerValuedLower_log {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w P) (hL : P.natDegree ≤ L) :
    PadicLower p (w - (Nat.log p (L + 1) : ℤ)) (bernoulliFunctional P) := by
  apply bernoulliFunctional_integerValuedLower hP hL
  intro b hb hbL
  right
  rw [padicValRat.inv, padicValRat.of_nat]
  exact neg_le_neg (by exact_mod_cast
    (padicValNat_le_nat_log b).trans (Nat.log_mono_right hbL))

theorem bernoulliFunctional_integerValuedLower_below_square {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w P) (hL : P.natDegree ≤ L) (hLp : L + 1 < p ^ 2) :
    PadicLower p (w - 1) (bernoulliFunctional P) := by
  apply bernoulliFunctional_integerValuedLower hP hL
  intro b hb hbL
  simpa using reciprocalPower_padicLower (p := p) b 1 hb (hbL.trans_lt hLp)

/-- Each derivative, and the final Bernoulli evaluation, costs at most one
power of p below the square threshold. -/
theorem bernoulliFunctional_iterate_derivative_below_square {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w P) (hL : P.natDegree ≤ L) (hLp : L + 1 < p ^ 2) (k : ℕ) :
    PadicLower p (w - (k : ℤ) - 1) (bernoulliFunctional (derivative^[k] P)) := by
  apply bernoulliFunctional_integerValuedLower_below_square
    (integerValuedLower_iterate_derivative_below_square hP hL (by omega) k)
    ((natDegree_iterate_derivative P k).trans ((Nat.sub_le _ _).trans hL)) hLp

/-- A common logarithmic degree bound suffices for all derivative orders. -/
theorem bernoulliFunctional_iterate_derivative_log {P : ℚ[X]} {w : ℤ} {L : ℕ}
    (hP : IntegerValuedLower p w P) (hL : P.natDegree ≤ L) (k : ℕ) :
    PadicLower p (w - ((k : ℤ) + 1) * (Nat.log p (L + 1) : ℤ))
      (bernoulliFunctional (derivative^[k] P)) := by
  have hden : ∀ b : ℕ, 0 < b → b ≤ L + 1 →
      PadicLower p (-(Nat.log p (L + 1) : ℤ)) ((b : ℚ)⁻¹) := by
    intro b hb hbL
    right
    rw [padicValRat.inv, padicValRat.of_nat]
    exact neg_le_neg (by exact_mod_cast
      (padicValNat_le_nat_log b).trans (Nat.log_mono_right hbL))
  have hd := integerValuedLower_iterate_derivative hP hL
    (fun b hb hbL => hden b hb (by omega)) k
  have h := bernoulliFunctional_integerValuedLower hd
    ((natDegree_iterate_derivative P k).trans ((Nat.sub_le _ _).trans hL)) hden
  convert h using 1 <;> ring

end Zeta5.Arithmetic
