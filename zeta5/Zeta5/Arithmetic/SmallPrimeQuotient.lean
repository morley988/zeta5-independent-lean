import Zeta5.Arithmetic.SmallPrimeScalars

/-!
# Exact high-degree central quotients and their all-prime moment loss

After the denominator divides the central polynomial, the transformed
quotient is a factorial scalar times two integer-valued binomial polynomials.
This supplies the logarithmic small-prime bound without a local square-size
restriction on p.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

def scaledCentralNumerator (N l : ℕ) : ℚ[X] :=
  C ((Nat.factorial N : ℚ)^2)*windowBasis l

def centralTailProduct (N k : ℕ) : ℚ[X] :=
  ∏ a ∈ range k, (X+C (((N+1+a : ℕ) : ℚ)^2))

def centralQuotientPolynomial (N k : ℕ) : ℚ[X] :=
  C (((-1 : ℚ)^(N+k+1))*(Nat.factorial N : ℚ)^2/
    (Nat.factorial (2*(N+k+1)) : ℚ))*X*centralTailProduct N k

lemma windowBasis_eq_signed_product (l : ℕ) :
    windowBasis l = C (((Nat.factorial (2*l) : ℚ)⁻¹)*(-1 : ℚ)^l)*
      ∏ a ∈ range l, (X+C ((a : ℚ)^2)) := by
  simp only [windowBasis, centralPolynomial, rootPolynomial, mul_comp, C_comp,
    Polynomial.prod_comp, sub_comp, X_comp]
  have he (a : ℕ) : (-X-C ((a : ℚ)^2) : ℚ[X]) = C (-1)*(X+C ((a : ℚ)^2)) := by
    simp only [map_neg, map_one]
    ring
  simp_rw [he]
  rw [prod_mul_distrib, prod_const, card_range, ← map_pow, ← mul_assoc, ← map_mul]

lemma positiveRootProduct_split (N k : ℕ) :
    (∏ a ∈ range (N+k+1), (X+C ((a : ℚ)^2))) =
      denominator N*X*centralTailProduct N k := by
  rw [prod_range_succ', prod_range_add]
  simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), map_zero, add_zero]
  have ht : (∏ a ∈ range k, (X+C (((N+a+1 : ℕ) : ℚ)^2))) = centralTailProduct N k := by
    unfold centralTailProduct
    apply prod_congr rfl
    intro a _
    rw [show N+a+1 = N+1+a by omega]
  rw [ht]
  change (denominator N*centralTailProduct N k)*X = _
  ring

theorem scaledCentralNumerator_high_factorization (N k : ℕ) :
    scaledCentralNumerator N (N+k+1) = denominator N*centralQuotientPolynomial N k := by
  rw [scaledCentralNumerator, windowBasis_eq_signed_product, positiveRootProduct_split]
  simp only [centralQuotientPolynomial, div_eq_mul_inv, map_mul]
  ring

lemma centralTailProduct_natDegree (N k : ℕ) : (centralTailProduct N k).natDegree = k := by
  rw [centralTailProduct, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]
  · intro a _
    exact monic_X_add_C _

lemma centralQuotientPolynomial_natDegree_le (N k : ℕ) :
    (centralQuotientPolynomial N k).natDegree ≤ k+1 := by
  unfold centralQuotientPolynomial
  rw [mul_assoc]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans (by
    rw [natDegree_X, centralTailProduct_natDegree]
    omega))

lemma bernoulliCentralQuotient_eval (N k : ℕ) (x : ℚ) :
    (bernoulliMomentNumerator (centralQuotientPolynomial N k)).eval x =
      (-((-1 : ℚ)^(N+k+1)))*centralQuotientScalar N k*x^7*
        (binomialPolynomial k).eval (x-((N+1 : ℕ) : ℚ))*
        (binomialPolynomial k).eval (-x-((N+1 : ℕ) : ℚ)) := by
  have hpair : (∏ a ∈ range k, (-x^2+((N+1+a : ℕ) : ℚ)^2)) =
      (descPochhammer ℚ k).eval (x-((N+1 : ℕ) : ℚ))*
        (descPochhammer ℚ k).eval (-x-((N+1 : ℕ) : ℚ)) := by
    rw [descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range,
      ← prod_mul_distrib]
    apply prod_congr rfl
    intro a _
    push_cast
    ring
  simp only [bernoulliMomentNumerator, centralQuotientPolynomial, centralTailProduct,
    eval_mul, eval_pow, eval_X, eval_comp, eval_neg, eval_C, eval_prod, eval_add]
  rw [hpair]
  simp only [binomialPolynomial, eval_mul, eval_C, centralQuotientScalar]
  have hf : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  field_simp

variable {p : ℕ} [Fact p.Prime]

theorem bernoulliCentralQuotient_integerValuedLower (N k D : ℕ)
    (hD : 2*(N+k+1) ≤ D) :
    IntegerValuedLower p (-5*(Nat.log p D : ℤ))
      (bernoulliMomentNumerator (centralQuotientPolynomial N k)) := by
  intro x
  rw [bernoulliCentralQuotient_eval]
  have hleft : (x : ℚ)-((N+1 : ℕ) : ℚ) = ((x-(N+1 : ℕ) : ℤ) : ℚ) := by
    push_cast
    rfl
  have hright : -(x : ℚ)-((N+1 : ℕ) : ℚ) = ((-x-(N+1 : ℕ) : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [hleft, hright, binomialPolynomial_eval_int, binomialPolynomial_eval_int]
  have hs := (sign_prime_integral (p := p) (N+k+1)).neg
  have hc := centralQuotientScalar_padicLower_log (p := p) N k D hD
  have hx : PadicLower p 0 ((x : ℚ)^7) := by
    right
    rw [padicValRat.pow, padicValRat.of_int]
    positivity
  simpa only [zero_add, add_zero] using
    (((hs.mul hc).mul hx).mul (padicLower_int _)).mul (padicLower_int _)

theorem centralQuotientMoment_padicLower_log (N k D : ℕ)
    (hD : 2*(N+k+1) ≤ D) (hdeg : 2*k+8 ≤ D) :
    PadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (polynomialMoment (centralQuotientPolynomial N k)) := by
  have hi := bernoulliCentralQuotient_integerValuedLower (p := p) N k D hD
  have hd : (bernoulliMomentNumerator (centralQuotientPolynomial N k)).natDegree ≤ 2*k+7 :=
    (bernoulliMomentNumerator_natDegree_le _).trans (by
      have h := centralQuotientPolynomial_natDegree_le N k
      omega)
  have h := polynomialMoment_padicLower_log hi hd
  apply h.mono
  have hl : (Nat.log p (2*k+7+1) : ℤ) ≤ Nat.log p D := by
    exact_mod_cast Nat.log_mono_right hdeg
  omega

theorem numeratorFunctional_scaledCentral_high (N k : ℕ) :
    numeratorFunctional N (scaledCentralNumerator N (N+k+1)) =
      C (polynomialMoment (centralQuotientPolynomial N k)) := by
  rw [numeratorFunctional_apply, scaledCentralNumerator_high_factorization,
    mul_div_cancel_left₀ _ (denominator_ne_zero N)]
  have hz : (∑ i ∈ range N,
      C ((denominator N*centralQuotientPolynomial N k).eval (pole (i+1))/
        (denominator N).derivative.eval (pole (i+1)))*stieltjes (i+1)) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [eval_mul, pole, denominator_eval_neg_square_eq_zero (by omega : 1 ≤ i+1)
      (by simpa using mem_range.mp hi)]
    simp
  rw [hz, add_zero]

end Zeta5.Arithmetic
