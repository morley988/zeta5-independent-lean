import Zeta5.Arithmetic.StieltjesReflection
import Zeta5.Arithmetic.ReflectedMinors
import Zeta5.Arithmetic.LocalDivision

/-! Integral cancellation of an all-low reflected pair. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem integral_two_root_factorization (P : ℚ[X]) (a b : ℚ)
    (hP : PolynomialPadicLower p 0 P) (ha : PadicLower p 0 a)
    (hb : PadicLower p 0 b) (hab : a ≠ b) (hra : P.eval a = 0) (hrb : P.eval b = 0) :
    ∃ E : ℚ[X], PolynomialPadicLower p 0 E ∧ P = (X - C a) * (X - C b) * E := by
  let Q := P /ₘ (X - C a)
  have hQa : (X - C a) * Q = P := mul_divByMonic_eq_iff_isRoot.mpr hra
  have hQb : Q.eval b = 0 := by
    have h := hrb
    rw [← hQa, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab.symm)
  let E := Q /ₘ (X - C b)
  have hEb : (X - C b) * E = Q := mul_divByMonic_eq_iff_isRoot.mpr hQb
  have hA : PolynomialPadicLower p 0 (X - C a) := by
    simpa only [sub_eq_add_neg] using polynomialPadicLower_X.add (PolynomialPadicLower.constant ha).neg
  have hB : PolynomialPadicLower p 0 (X - C b) := by
    simpa only [sub_eq_add_neg] using polynomialPadicLower_X.add (PolynomialPadicLower.constant hb).neg
  have hQ : PolynomialPadicLower p 0 Q := polynomialPadicLower_divByMonic hP hA (monic_X_sub_C a)
  refine ⟨E, polynomialPadicLower_divByMonic hQ hB (monic_X_sub_C b), ?_⟩
  rw [← hQa, ← hEb]
  ring

theorem derivative_eval_two_root_factorization (P E : ℚ[X]) (a b : ℚ)
    (he : P = (X - C a) * (X - C b) * E) :
    P.derivative.eval a = (a - b) * E.eval a ∧
    P.derivative.eval b = (b - a) * E.eval b := by
  rw [he]
  simp [derivative_mul, derivative_sub]

theorem derivative_sum_padicLower_two (P : ℚ[X]) (a b : ℚ)
    (hP : PolynomialPadicLower p 0 P) (ha : PadicLower p 0 a)
    (hb : PadicLower p 0 b) (hab : a ≠ b) (hra : P.eval a = 0) (hrb : P.eval b = 0)
    (hcongr : PadicLower p 1 (a - b)) :
    PadicLower p 2 (P.derivative.eval a + P.derivative.eval b) := by
  obtain ⟨E, hE, he⟩ := integral_two_root_factorization P a b hP ha hb hab hra hrb
  obtain ⟨hda, hdb⟩ := derivative_eval_two_root_factorization P E a b he
  have h := hcongr.mul (padicLower_eval_sub_eval hE ha hb hcongr)
  rw [hda, hdb]
  convert h using 1 <;> ring

theorem inverse_sum_integral_of_sum_gain {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 1) (hvb : padicValRat p b = 1)
    (hsum : PadicLower p 2 (a + b)) : PadicLower p 0 (a⁻¹ + b⁻¹) := by
  have hia : PadicLower p (-1) a⁻¹ := by right; rw [padicValRat.inv, hva]
  have hib : PadicLower p (-1) b⁻¹ := by right; rw [padicValRat.inv, hvb]
  have h := hsum.mul (hia.mul hib)
  have he : a⁻¹ + b⁻¹ = (a + b) * (a⁻¹ * b⁻¹) := by field_simp; ring
  rw [he]
  simpa using h

theorem polynomial_pair_integral (u v : ℚ[X]) (a b : ℚ)
    (hv : PolynomialPadicLower p 0 v) (hdiff : PolynomialPadicLower p 1 (u - v))
    (ha : PadicLower p (-1) a) (hsum : PadicLower p 0 (a + b)) :
    PolynomialPadicLower p 0 (C a * u + C b * v) := by
  have h1 := (PolynomialPadicLower.constant ha).mul hdiff
  have h2 := (PolynomialPadicLower.constant hsum).mul hv
  have h := h1.add h2
  convert h using 1 <;> first | rfl | (simp only [map_add]; ring)

theorem polynomial_product_difference_integral
    (u v : ℚ) (P Q : ℚ[X]) (hu : PadicLower p 0 u) (hQ : PolynomialPadicLower p 0 Q)
    (huv : PadicLower p 1 (u - v)) (hPQ : PolynomialPadicLower p 1 (P - Q)) :
    PolynomialPadicLower p 1 (C u * P - C v * Q) := by
  have h1 := (PolynomialPadicLower.constant hu).mul hPQ
  have h2 := (PolynomialPadicLower.constant huv).mul hQ
  have h := h1.add h2
  convert h using 1 <;> first | rfl | (simp only [map_sub]; ring)

theorem monomialNumerator_integral (m k l : ℕ) :
    PolynomialPadicLower p 0 (commonFactor m ^ 2 * X ^ (k + l)) := by
  have h := polynomialPadicLower_integer_map (p := p) (monomialNumeratorInt m k l)
  simpa only [monomialNumeratorInt, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, commonRootInt_map_square, commonFactor] using h

theorem low_reflected_pair_integral (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hjN : p - c ≤ N)
    (hsmall : 2 * N < p ^ 2) (hcard : (reflectedNodes N p c).card = 2) :
    ∀ k l : Fin r, PolynomialPadicLower p 0
      (monomialAtom N m r c k l + monomialAtom N m r (p - c) k l) := by
  have hcplt : c < p := by omega
  have hj0 : 0 < p - c := by omega
  have hjplt : p - c < p := by omega
  have hcN : c ≤ N := by omega
  have hci : c ∈ reflectedNodes N p c :=
    mem_reflectedNodes.mpr ⟨hc, hcN, Or.inl (Nat.mod_eq_of_lt hcplt)⟩
  have hji : p - c ∈ reflectedNodes N p c :=
    mem_reflectedNodes.mpr ⟨hj0, hjN, Or.inr (Nat.mod_eq_of_lt hjplt)⟩
  have hsize : reflectedSize N p c = 2 :=
    (reflectedNodes_card N p c hc hcp).symm.trans hcard
  have hdc : padicValRat p ((denominator N).derivative.eval (pole c)) = 1 := by
    rw [denominator_derivative_reflected_valuation N c c (by omega) hc hcp hci (by omega), hsize]
    norm_num
  have hdj : padicValRat p ((denominator N).derivative.eval (pole (p - c))) = 1 := by
    rw [denominator_derivative_reflected_valuation N c (p - c) (by omega) hc hcp hji (by omega), hsize]
    norm_num
  have hdc0 : (denominator N).derivative.eval (pole c) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hc] using
      (denominator_derivative_at_pole_ne_zero (N := N) (i := c - 1) (by omega))
  have hdj0 : (denominator N).derivative.eval (pole (p - c)) ≠ 0 := by
    simpa only [Nat.sub_add_cancel hj0] using
      (denominator_derivative_at_pole_ne_zero (N := N) (i := p - c - 1) (by omega))
  have hcint := pole_padicIntegral (p := p) c
  have hjint := pole_padicIntegral (p := p) (p - c)
  have hdiff : PadicLower p 1 (pole c - pole (p - c)) := by
    simpa only [neg_sub] using (reflected_pole_congr hc hcp hji).neg
  have hne : pole c ≠ pole (p - c) := by
    intro he
    have he' : (c : ℚ) ^ 2 = ((p - c : ℕ) : ℚ) ^ 2 := by simpa [pole] using he
    have he'' := (sq_eq_sq₀ (by positivity : (0 : ℚ) ≤ c)
      (by positivity : (0 : ℚ) ≤ (p - c : ℕ))).mp he'
    have heN : c = p - c := by exact_mod_cast he''
    omega
  have hD : PolynomialPadicLower p 0 (denominator N) := by
    rw [← denominatorInt_map]
    exact polynomialPadicLower_integer_map _
  have hDsum := derivative_sum_padicLower_two (denominator N) (pole c) (pole (p - c))
    hD hcint hjint hne
    (denominator_eval_neg_square_eq_zero hc hcN)
    (denominator_eval_neg_square_eq_zero hj0 hjN) hdiff
  have hinvsum := inverse_sum_integral_of_sum_gain hdc0 hdj0 hdc hdj hDsum
  have hcinv : PadicLower p (-1) ((denominator N).derivative.eval (pole c))⁻¹ := by
    right
    rw [padicValRat.inv, hdc]
  intro k l
  let P : ℚ[X] := commonFactor m ^ 2 * X ^ (k.val + l.val)
  have hP : PolynomialPadicLower p 0 P := monomialNumerator_integral m k.val l.val
  have hPi := hP.eval_integral hcint
  have hPj := hP.eval_integral hjint
  have hPdiff := padicLower_eval_sub_eval hP hcint hjint hdiff
  have hkj := stieltjes_polynomial_integral (p := p) (p - c) hp hjplt
  have hkdiff : PolynomialPadicLower p 1 (stieltjes c - stieltjes (p - c)) := by
    simpa only [neg_sub] using (stieltjes_reflection c (by omega) hc hcp).neg
  have hnumdiff := polynomial_product_difference_integral
    (P.eval (pole c)) (P.eval (pole (p - c))) (stieltjes c) (stieltjes (p - c))
    hPi hkj hPdiff hkdiff
  have hv := (PolynomialPadicLower.constant hPj).mul hkj
  have h := polynomial_pair_integral _ _ _ _ hv hnumdiff hcinv hinvsum
  convert h using 1 <;> first | rfl | (simp only [monomialAtom, monomialAtomWeight,
    P, eval_mul, eval_pow, eval_X, map_mul, div_eq_mul_inv]; ring)

#print axioms derivative_sum_padicLower_two
#print axioms polynomial_pair_integral
#print axioms low_reflected_pair_integral

end Zeta5.Arithmetic
