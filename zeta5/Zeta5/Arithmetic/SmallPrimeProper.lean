import Zeta5.Arithmetic.SmallPrimeQuotient

/-! # All-prime bounds for the proper-fraction central terms -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

lemma reciprocalPower_padicLower_log (m s D : ℕ) (hmD : m ≤ D) :
    PadicLower p (-(s : ℤ)*(Nat.log p D : ℤ)) (1/(m : ℚ)^s) := by
  right
  simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have hl : (padicValNat p m : ℤ) ≤ Nat.log p D := by
    exact_mod_cast (padicValNat_le_nat_log m).trans (Nat.log_mono_right hmD)
  nlinarith [mul_nonneg (Int.natCast_nonneg s) (sub_nonneg.mpr hl)]

lemma harmonicFive_padicLower_log (n D : ℕ) (hnD : n ≤ D) :
    PadicLower p (-5*(Nat.log p D : ℤ)) (harmonicFive n) := by
  unfold harmonicFive
  apply padicLower_sum
  intro i hi
  exact reciprocalPower_padicLower_log (i+1) 5 D (by have := mem_range.mp hi; omega)

lemma inverse_two_exact_lower :
    PadicLower p (-(padicValNat p 2 : ℤ)) ((2 : ℚ)⁻¹) := by
  right
  rw [padicValRat.inv]
  change -(padicValNat p 2 : ℤ) ≤ -padicValRat p ((2 : ℕ) : ℚ)
  rw [padicValRat.of_nat]

theorem stieltjes_polynomial_padicLower_log (i D : ℕ) (hiD : i ≤ D) :
    PolynomialPadicLower p (-5*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ)) (stieltjes i) := by
  have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
  have h2 : (0 : ℤ) ≤ padicValNat p 2 := by positivity
  have hi4 : PadicLower p 0 ((i : ℚ)^4) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := (hi4.neg).mul (harmonicFive_padicLower_log (i-1) D (by omega))
  have hrec : PadicLower p (-(padicValNat p 2 : ℤ)-(Nat.log p D : ℤ))
      (1/(2*(i : ℚ))) := by
    convert! (inverse_two_exact_lower (p := p)).mul
      (inverse_nat_padicLower_log (p := p) hiD) using 1 <;>
      simp [one_div, mul_inv_rev, mul_comm, sub_eq_add_neg]
  have hquarter : PadicLower p (-2*(padicValNat p 2 : ℤ)) (1/4 : ℚ) := by
    convert! (inverse_two_exact_lower (p := p)).mul (inverse_two_exact_lower (p := p)) using 1
    · ring
    · norm_num
  have hc : PadicLower p (-5*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ))
      (stieltjesConstant i) := by
    have hp' := hprod.mono (show -5*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      0 + -5*(Nat.log p D : ℤ) by omega)
    have hr' := hrec.mono (show -5*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      -(padicValNat p 2 : ℤ)-(Nat.log p D : ℤ) by omega)
    have hq' := hquarter.mono (show -5*(Nat.log p D : ℤ)-2*(padicValNat p 2 : ℤ) ≤
      -2*(padicValNat p 2 : ℤ) by omega)
    simpa only [stieltjesConstant, sub_eq_add_neg] using (hp'.add hr'.neg).add hq'.neg
  exact (PolynomialPadicLower.constant hc).add ((stieltjes_linear_integral i).mono (by omega))

lemma factorialScaledDerivativeInverse_padicLower_log (N i D : ℕ)
    (hi : 0 < i) (hiN : i ≤ N) (hND : 2*N ≤ D) :
    PadicLower p (-(Nat.log p D : ℤ))
      ((Nat.factorial N : ℚ)^2/(denominator N).derivative.eval (pole i)) := by
  have he : (Nat.factorial N : ℚ)^2/(denominator N).derivative.eval (pole i) =
      ((-1 : ℚ)^(i-1))⁻¹*(2*(i : ℚ)^2)*
        ((Nat.factorial N : ℚ)^2/
          ((Nat.factorial (N-i) : ℚ)*(Nat.factorial (N+i) : ℚ))) := by
    rw [denominator_derivative_pole N i hi hiN]
    field_simp
  rw [he]
  have hs : PadicLower p 0 (((-1 : ℚ)^(i-1))⁻¹) := by
    rw [← inv_pow]
    norm_num only [inv_neg, inv_one]
    exact sign_prime_integral (p := p) (i-1)
  have hi2 : PadicLower p 0 (2*(i : ℚ)^2) := by
    have he : ((2*i^2 : ℕ) : ℚ) = 2*(i : ℚ)^2 := by push_cast; rfl
    rw [← he]
    exact padicLower_nat (p := p) (2*i^2)
  simpa using (hs.mul hi2).mul (factorialRatio_padicLower_log N i D hiN hND)

lemma padicValNat_twentyFour (p : ℕ) [Fact p.Prime] :
    padicValNat p 24 = 3*padicValNat p 2+padicValNat p 3 := by
  rw [show 24 = 2^3*3 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.pow]

lemma scaledCentralResidue_padicLower_log (N l i D : ℕ)
    (hi : 0 < i) (hiN : i ≤ N) (hND : 2*N ≤ D) :
    PolynomialPadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (C ((scaledCentralNumerator N l).eval (pole i)/
        (denominator N).derivative.eval (pole i))*stieltjes i) := by
  have hv : PadicLower p (-(padicValNat p 2 : ℤ))
      ((centralPolynomial l).eval ((i : ℚ)^2)) := by
    simpa only [Int.cast_natCast] using centralPolynomial_square_padicLower (p := p) l (i : ℤ)
  have hscaled := (factorialScaledDerivativeInverse_padicLower_log N i D hi hiN hND).mul hv
  have he : (scaledCentralNumerator N l).eval (pole i)/(denominator N).derivative.eval (pole i) =
      ((Nat.factorial N : ℚ)^2/(denominator N).derivative.eval (pole i))*
        (centralPolynomial l).eval ((i : ℚ)^2) := by
    simp only [scaledCentralNumerator, windowBasis, eval_mul, eval_C, eval_comp,
      eval_neg, eval_X, pole, neg_neg]
    ring
  rw [he]
  have h := (PolynomialPadicLower.constant hscaled).mul
    (stieltjes_polynomial_padicLower_log i D (by omega))
  apply h.mono
  have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
  have h3 : (0 : ℤ) ≤ padicValNat p 3 := by positivity
  rw [padicValNat_twentyFour]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma scaledCentralNumerator_ne_zero (N l : ℕ) : scaledCentralNumerator N l ≠ 0 := by
  apply mul_ne_zero
  · apply C_ne_zero.mpr
    positivity
  · intro h
    exact centralPolynomial_ne_zero l (comp_neg_X_eq_zero_iff.mp h)

lemma scaledCentralNumerator_natDegree (N l : ℕ) :
    (scaledCentralNumerator N l).natDegree = l := by
  rw [scaledCentralNumerator, natDegree_C_mul (by positivity), windowBasis_natDegree]

lemma scaledCentralNumerator_leadingCoeff (N l : ℕ) :
    (scaledCentralNumerator N l).leadingCoeff =
      (Nat.factorial N : ℚ)^2*(Nat.factorial (2*l) : ℚ)⁻¹*(-1 : ℚ)^l := by
  rw [scaledCentralNumerator, windowBasis_eq_signed_product,
    leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_prod]
  simp only [leadingCoeff_X_add_C, prod_const_one, mul_one]
  ring

lemma scaledCentralQuotient_zero (N l : ℕ) (hlN : l < N) :
    scaledCentralNumerator N l/denominator N = 0 := by
  apply (Polynomial.div_eq_zero_iff (denominator_ne_zero N)).mpr
  rw [degree_eq_natDegree (scaledCentralNumerator_ne_zero N l),
    degree_eq_natDegree (denominator_ne_zero N), scaledCentralNumerator_natDegree,
    denominator_natDegree]
  exact_mod_cast hlN

lemma scaledCentralQuotient_diagonal (N : ℕ) :
    scaledCentralNumerator N N/denominator N =
      C (((-1 : ℚ)^N)*((Nat.factorial N : ℚ)^2/(Nat.factorial (2*N) : ℚ))) := by
  have hd : (scaledCentralNumerator N N/denominator N).natDegree = 0 := by
    rw [← divByMonic_eq_div _ (denominator_monic N),
      natDegree_divByMonic _ (denominator_monic N), scaledCentralNumerator_natDegree,
      denominator_natDegree, Nat.sub_self]
  have hc := leadingCoeff_div (p := scaledCentralNumerator N N) (q := denominator N) (by
    rw [degree_eq_natDegree (scaledCentralNumerator_ne_zero N N),
      degree_eq_natDegree (denominator_ne_zero N), scaledCentralNumerator_natDegree,
      denominator_natDegree])
  rw [(denominator_monic N).leadingCoeff, div_one, scaledCentralNumerator_leadingCoeff] at hc
  have heq := eq_C_of_natDegree_eq_zero hd
  rw [heq, leadingCoeff_C] at hc
  rw [heq, hc]
  congr 1
  ring

lemma polynomialMoment_C (a : ℚ) : polynomialMoment (C a) = a*rationalMoment 0 := by
  simp [polynomialMoment, Polynomial.sum_C_index]

lemma rationalMoment_zero_padicLower :
    PadicLower p (-(padicValNat p 24 : ℤ)) (rationalMoment 0) := by
  have h24 : PadicLower p (-(padicValNat p 24 : ℤ)) ((24 : ℚ)⁻¹) := by
    right
    rw [padicValRat.inv]
    change -(padicValNat p 24 : ℤ) ≤ -padicValRat p ((24 : ℕ) : ℚ)
    rw [padicValRat.of_nat]
  have h := (padicLower_nat (p := p) 10).mul h24
  rw [rationalMoment_zero]
  norm_num at h ⊢
  exact h

lemma scaledCentralQuotientMoment_padicLower_log (N l D : ℕ)
    (hlN : l ≤ N) (hND : 2*N ≤ D) :
    PadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (polynomialMoment (scaledCentralNumerator N l/denominator N)) := by
  rcases hlN.eq_or_lt with heq | hlN
  · subst l
    rw [scaledCentralQuotient_diagonal, polynomialMoment_C]
    have hr := factorialRatio_padicLower_log (p := p) N N D le_rfl hND
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul,
      show N+N = 2*N by omega] at hr
    have h := ((sign_prime_integral (p := p) N).mul hr).mul
      (rationalMoment_zero_padicLower (p := p))
    apply h.mono
    have hL : (0 : ℤ) ≤ Nat.log p D := by positivity
    omega
  · rw [scaledCentralQuotient_zero N l hlN]
    simp [polynomialMoment, PadicLower]

theorem numeratorFunctional_scaledCentral_proper_padicLower_log (N l D : ℕ)
    (hlN : l ≤ N) (hND : 2*N ≤ D) :
    PolynomialPadicLower p (-9*(Nat.log p D : ℤ)-(padicValNat p 24 : ℤ))
      (numeratorFunctional N (scaledCentralNumerator N l)) := by
  rw [numeratorFunctional_apply]
  apply (PolynomialPadicLower.constant (scaledCentralQuotientMoment_padicLower_log N l D hlN hND)).add
  apply PolynomialPadicLower.sum
  intro i hi
  exact scaledCentralResidue_padicLower_log N l (i+1) D (by omega)
    (by simpa using mem_range.mp hi) hND

end Zeta5.Arithmetic
