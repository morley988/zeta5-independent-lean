import Zeta5.Arithmetic.Moments
import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomial quotient moments and the terminal support bound

The monomial basis uses the square of the common root factor. Its sign is
irrelevant after squaring, so integral monic factors `X+a²` are used here.
Division by the monic denominator is performed over `ℤ[X]` itself.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem polynomialMoment_padicLower (q : ℚ[X]) (hp : 5 < p)
    (hq : ∀ k, PadicLower p 0 (q.coeff k)) :
    PadicLower p (-1) (polynomialMoment q) := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]
  apply padicLower_sum
  intro k hk
  simpa using (hq k).mul (rationalMoment_padicLower (p := p) k hp)

theorem polynomialMoment_integral_of_degree_lt (q : ℚ[X]) (hp : 5 < p)
    (hq : ∀ k, PadicLower p 0 (q.coeff k)) (hdeg : q.natDegree < 2 * p - 3) :
    PadicLower p 0 (polynomialMoment q) := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]
  apply padicLower_sum
  intro k hk
  have hkdeg : k ≤ q.natDegree := le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  simpa using (hq k).mul
    (rationalMoment_integral_of_lt (p := p) k hp (lt_of_le_of_lt hkdeg hdeg))

theorem intPolynomial_coeff_integral (q : ℤ[X]) (k : ℕ) :
    PadicLower p 0 ((q.map (Int.castRingHom ℚ)).coeff k) := by
  simpa using padicLower_int (p := p) (q.coeff k)

theorem intPolynomialMoment_padicLower (q : ℤ[X]) (hp : 5 < p) :
    PadicLower p (-1) (polynomialMoment (q.map (Int.castRingHom ℚ))) :=
  polynomialMoment_padicLower _ hp (intPolynomial_coeff_integral q)

theorem intPolynomialMoment_integral (q : ℤ[X]) (hp : 5 < p)
    (hdeg : q.natDegree < 2 * p - 3) :
    PadicLower p 0 (polynomialMoment (q.map (Int.castRingHom ℚ))) := by
  apply polynomialMoment_integral_of_degree_lt _ hp (intPolynomial_coeff_integral q)
  exact lt_of_le_of_lt (natDegree_map_le) hdeg

def commonRootInt (m : ℕ) : ℤ[X] :=
  ∏ a ∈ Finset.range m, (X + C ((a : ℤ) ^ 2))

def denominatorInt (N : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range N, (X + C (((i + 1 : ℕ) : ℤ) ^ 2))

def monomialNumeratorInt (m k l : ℕ) : ℤ[X] :=
  commonRootInt m ^ 2 * X ^ (k + l)

def monomialQuotientInt (N m k l : ℕ) : ℤ[X] :=
  monomialNumeratorInt m k l /ₘ denominatorInt N

def quotientMoment (N m k l : ℕ) : ℚ :=
  polynomialMoment ((monomialQuotientInt N m k l).map (Int.castRingHom ℚ))

theorem denominatorInt_map (N : ℕ) :
    (denominatorInt N).map (Int.castRingHom ℚ) = denominator N := by
  unfold denominatorInt denominator
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

theorem commonRootInt_map_square (m : ℕ) :
    ((commonRootInt m).map (Int.castRingHom ℚ)) ^ 2 =
      ((rootPolynomial m).comp (-X)) ^ 2 := by
  unfold commonRootInt rootPolynomial
  rw [Polynomial.map_prod, Polynomial.prod_comp]
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp only [map_pow, map_natCast]
  ring

theorem commonRootInt_monic (m : ℕ) : (commonRootInt m).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem denominatorInt_monic (N : ℕ) : (denominatorInt N).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem commonRootInt_natDegree (m : ℕ) : (commonRootInt m).natDegree = m := by
  rw [commonRootInt, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro a ha
    exact monic_X_add_C _

theorem denominatorInt_natDegree (N : ℕ) : (denominatorInt N).natDegree = N := by
  rw [denominatorInt, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · intro a ha
    exact monic_X_add_C _

theorem monomialNumeratorInt_natDegree (m k l : ℕ) :
    (monomialNumeratorInt m k l).natDegree = 2 * m + k + l := by
  rw [monomialNumeratorInt, natDegree_mul
    (pow_ne_zero _ (commonRootInt_monic m).ne_zero) (pow_ne_zero _ X_ne_zero),
    natDegree_pow, commonRootInt_natDegree, natDegree_X_pow]
  omega

theorem monomialQuotientInt_natDegree (N m k l : ℕ) :
    (monomialQuotientInt N m k l).natDegree = (2 * m + k + l) - N := by
  rw [monomialQuotientInt, natDegree_divByMonic _ (denominatorInt_monic N),
    monomialNumeratorInt_natDegree, denominatorInt_natDegree]

/-- The integral polynomial division above is exactly the rational
quotient of the manuscript's squared common-root numerator. -/
theorem monomialQuotientInt_map (N m k l : ℕ) :
    (monomialQuotientInt N m k l).map (Int.castRingHom ℚ) =
      (((rootPolynomial m).comp (-X)) ^ 2 * X ^ (k + l)) / denominator N := by
  rw [monomialQuotientInt, Polynomial.map_divByMonic _ (denominatorInt_monic N),
    denominatorInt_map, divByMonic_eq_div _ (denominator_monic N)]
  congr 1
  simp only [monomialNumeratorInt, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, commonRootInt_map_square]

theorem quotientMoment_eq_manuscript (N m k l : ℕ) :
    quotientMoment N m k l =
      polynomialMoment ((((rootPolynomial m).comp (-X)) ^ 2 * X ^ (k + l)) / denominator N) := by
  rw [quotientMoment, monomialQuotientInt_map]

theorem quotientMoment_padicLower (N m k l : ℕ) (hp : 5 < p) :
    PadicLower p (-1) (quotientMoment N m k l) :=
  intPolynomialMoment_padicLower _ hp

theorem quotientMoment_integral (N m k l : ℕ) (hp : 5 < p)
    (hindex : 2 * m + k + l < N + (2 * p - 3)) :
    PadicLower p 0 (quotientMoment N m k l) := by
  apply intPolynomialMoment_integral _ hp
  rw [monomialQuotientInt_natDegree]
  omega

/-- If one matrix index lies before the terminal block, no fractional
moment can occur. This is an exact finite statement, with no asymptotics. -/
theorem quotientMoment_integral_outside_terminal (N m R k l : ℕ)
    (hp : 5 < p) (hmR : m ≤ R) (hk : k < R - m) (hl : l < R - m)
    (houtside : k < N + 2 * p - 2 - m - R ∨ l < N + 2 * p - 2 - m - R) :
    PadicLower p 0 (quotientMoment N m k l) := by
  apply quotientMoment_integral N m k l hp
  omega

def terminalSize (N m R p : ℕ) : ℕ :=
  min (R - m) (2 * R + 2 - (N + 2 * p))

theorem quotientMoment_integral_outside_terminalSize (N m R k l : ℕ)
    (hp : 5 < p) (hmR : m ≤ R) (hk : k < R - m) (hl : l < R - m)
    (houtside : k < (R - m) - terminalSize N m R p ∨
      l < (R - m) - terminalSize N m R p) :
    PadicLower p 0 (quotientMoment N m k l) := by
  apply quotientMoment_integral_outside_terminal N m R k l hp hmR hk hl
  unfold terminalSize at houtside
  omega

#print axioms quotientMoment_padicLower
#print axioms quotientMoment_integral_outside_terminal

end Zeta5.Arithmetic
