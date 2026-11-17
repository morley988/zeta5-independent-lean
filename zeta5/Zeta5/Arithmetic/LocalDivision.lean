import Zeta5.Reuse.PolynomialValuations
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial division over the local integers

Monic division is performed in the subring of rational numbers integral
at `p`.  For an actual quotient by a polynomial with unit constant term,
coefficient induction preserves every lower valuation bound.  Reversing
polynomials gives the corresponding assertion for a monic divisor.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue

variable {p : ℕ} [Fact p.Prime]

def padicIntegralSubring (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | PadicLower p 0 x}
  zero_mem' := PadicLower.zero 0
  one_mem' := padicLower_nat 1
  add_mem' := fun ha hb => ha.add hb
  neg_mem' := fun ha => ha.neg
  mul_mem' := fun ha hb => by simpa using ha.mul hb

theorem polynomial_coeffs_mem_padicIntegralSubring {P : ℚ[X]}
    (hP : PolynomialPadicLower p 0 P) :
    (↑P.coeffs : Set ℚ) ⊆ padicIntegralSubring p := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp ha
  exact hP n

theorem polynomialPadicLower_subring_map (P : (padicIntegralSubring p)[X]) :
    PolynomialPadicLower p 0 (P.map (padicIntegralSubring p).subtype) := by
  intro k
  rw [coeff_map]
  exact (P.coeff k).property

theorem polynomialPadicLower_divByMonic {P U : ℚ[X]}
    (hP : PolynomialPadicLower p 0 P) (hU : PolynomialPadicLower p 0 U) (hmonic : U.Monic) :
    PolynomialPadicLower p 0 (P /ₘ U) := by
  let P' := P.toSubring (padicIntegralSubring p) (polynomial_coeffs_mem_padicIntegralSubring hP)
  let U' := U.toSubring (padicIntegralSubring p) (polynomial_coeffs_mem_padicIntegralSubring hU)
  have hm : U'.Monic := by simpa [U'] using hmonic
  have h := polynomialPadicLower_subring_map (p := p) (P' /ₘ U')
  rw [map_divByMonic _ hm] at h
  simpa [P', U'] using h

theorem polynomialPadicLower_modByMonic {P U : ℚ[X]}
    (hP : PolynomialPadicLower p 0 P) (hU : PolynomialPadicLower p 0 U) (hmonic : U.Monic) :
    PolynomialPadicLower p 0 (P %ₘ U) := by
  rw [modByMonic_eq_sub_mul_div, sub_eq_add_neg]
  simpa using hP.add ((hU.mul (polynomialPadicLower_divByMonic hP hU hmonic)).neg)

/-- Actual division by an integral polynomial with unit constant term
preserves an arbitrary coefficient valuation lower bound. -/
theorem polynomialPadicLower_quotient_of_unit_constant {P U Q : ℚ[X]} {w : ℤ}
    (hP : PolynomialPadicLower p w P) (hU : PolynomialPadicLower p 0 U)
    (hunit : U.coeff 0 ≠ 0) (hinv : PadicLower p 0 ((U.coeff 0)⁻¹))
    (heq : P = U * Q) : PolynomialPadicLower p w Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let s := (antidiagonal n).erase (0, n)
    have hsum : PadicLower p w (∑ ij ∈ s, U.coeff ij.1 * Q.coeff ij.2) := by
      apply padicLower_sum
      rintro ⟨i, j⟩ hij
      obtain ⟨hne, hij⟩ := mem_erase.mp hij
      have hij' : i + j = n := mem_antidiagonal.mp hij
      have hj : j < n := by
        by_contra hj
        have hi0 : i = 0 := by omega
        have hjn : j = n := by omega
        subst i
        subst j
        exact hne rfl
      simpa using (hU i).mul (ih j hj)
    have hidentity : (∑ ij ∈ s, U.coeff ij.1 * Q.coeff ij.2) + U.coeff 0 * Q.coeff n =
        P.coeff n := by
      rw [heq, coeff_mul]
      exact sum_erase_add _ _ (by simp)
    have hcoeff : Q.coeff n =
        (P.coeff n - ∑ ij ∈ s, U.coeff ij.1 * Q.coeff ij.2) * (U.coeff 0)⁻¹ := by
      rw [← hidentity]
      field_simp
      ring
    rw [hcoeff]
    simpa only [add_zero, sub_eq_add_neg] using ((hP n).add hsum.neg).mul hinv

theorem polynomialPadicLower_reverse_iff {P : ℚ[X]} {w : ℤ} :
    PolynomialPadicLower p w P.reverse ↔ PolynomialPadicLower p w P := by
  constructor
  · intro h n
    simpa only [coeff_reverse, revAt_invol] using h (revAt P.natDegree n)
  · intro h n
    rw [coeff_reverse]
    exact h _

/-- The weighted form needed when a numerator gains an additional factor
of `p` on the restriction kernel. -/
theorem polynomialPadicLower_quotient_of_monic {P U Q : ℚ[X]} {w : ℤ}
    (hP : PolynomialPadicLower p w P) (hU : PolynomialPadicLower p 0 U)
    (hmonic : U.Monic) (heq : P = U * Q) : PolynomialPadicLower p w Q := by
  apply polynomialPadicLower_reverse_iff.mp
  apply polynomialPadicLower_quotient_of_unit_constant
    (polynomialPadicLower_reverse_iff.mpr hP) (polynomialPadicLower_reverse_iff.mpr hU)
  · simp [coeff_zero_reverse, hmonic.leadingCoeff]
  · simpa [coeff_zero_reverse, hmonic.leadingCoeff] using padicLower_nat (p := p) 1
  · rw [heq, reverse_mul_of_domain]

end Zeta5.Arithmetic
