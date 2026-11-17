import Zeta5.Arithmetic.FactorialPrefactor

/-! Integrality of the monomial pencil above N and finite prime support
for the actual window determinant. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Finset Allocation
variable {p : ℕ} [Fact p.Prime]

theorem reflected_class_integral_above_N (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hNp : N < p) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (monomialReflectedClass N m r p c k l) := by
  have hsmall : 2 * N < p ^ 2 := by nlinarith
  have hsize : reflectedSize N p c ≤ 2 := by
    simp only [reflectedSize, Nat.div_eq_of_lt hNp, Nat.mod_eq_of_lt hNp, mul_zero, zero_add]
    split_ifs <;> omega
  by_cases htwo : reflectedSize N p c = 2
  · have hci : c ≤ N ∧ p - c ≤ N := by
      simp only [reflectedSize, Nat.div_eq_of_lt hNp, Nat.mod_eq_of_lt hNp,
        mul_zero, zero_add] at htwo
      split_ifs at htwo <;> omega
    have hset : reflectedNodes N p c = {c, p - c} := by
      ext i
      simp only [mem_reflectedNodes, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hi0, hiN, him⟩
        simpa only [Nat.mod_eq_of_lt (hiN.trans_lt hNp)] using him
      · rintro (rfl | rfl)
        · exact ⟨hc, hci.1, Or.inl (Nat.mod_eq_of_lt (hci.1.trans_lt hNp))⟩
        · exact ⟨by omega, hci.2, Or.inr (Nat.mod_eq_of_lt (hci.2.trans_lt hNp))⟩
    have hcard : (reflectedNodes N p c).card = 2 :=
      (reflectedNodes_card N p c hc hcp).trans htwo
    intro k l
    rw [monomialReflectedClass_eq_sum, hset, sum_pair (by omega : c ≠ p - c), Matrix.add_apply]
    exact low_reflected_pair_integral N m r c hp hc hcp hci.2 hsmall hcard k l
  · have hle : reflectedSize N p c ≤ 1 := by omega
    intro k l
    rw [monomialReflectedClass_eq_sum]
    simp only [Matrix.sum_apply]
    apply PolynomialPadicLower.sum
    intro i hi
    obtain ⟨hi0, hiN, _⟩ := mem_reflectedNodes.mp hi
    have hd : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ 0 := by
      rw [denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi (by omega)]
      omega
    have hw := monomialAtomWeight_bound N m i 0 0 0 (commonFactor_eval_sq_integral m i)
      (stieltjes_polynomial_integral i hp (hiN.trans_lt hNp)) hd
    have hx := PolynomialPadicLower.constant
      (padicIntegral_pow (pole_padicIntegral (p := p) i) (k.val + l.val))
    exact hw.mul hx

theorem zeroClassNodes_empty_above_N (N p : ℕ) (hNp : N < p) : zeroClassNodes N p = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hiI, hpi⟩ := mem_filter.mp hi
  obtain ⟨hi0, hiN⟩ := mem_Ioc.mp hiI
  have hp := Nat.le_of_dvd hi0 hpi
  omega

theorem monomialPencil_integral_above_N (N m r : ℕ) (hp : 5 < p)
    (hNp : N < p) (hdegree : 2 * m + 2 * r ≤ N + (2 * p - 3)) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (monomialPencil N m r k l) := by
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  intro k l
  rw [monomialPencil_reflected_decomposition N m r p hp0 hodd, zeroClassNodes_empty_above_N N p hNp]
  simp only [sum_empty, add_zero, Matrix.add_apply, Matrix.sum_apply]
  apply PolynomialPadicLower.add
  · apply PolynomialPadicLower.constant
    exact quotientMoment_integral N m k.val l.val hp (by have hk := k.isLt; have hl := l.isLt; omega)
  · apply PolynomialPadicLower.sum
    intro c hc
    exact reflected_class_integral_above_N N m r (c.val + 1) hp (by omega)
      (by have hc' := c.isLt; omega) hNp k l

theorem windowDeterminant_largePrime_bound (n : ℕ) (hn : 0 < n) (hNp : 20 * n < p) :
    PolynomialPadicLower p (-factorialCharge (20 * n) n (24 * n) p) (windowDeterminant n) := by
  have hp : 5 < p := by omega
  have hlarge : 50 * n < p ^ 2 := by
    have hs : (20 * n + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hM := integral_matrix_minorLower (p := p) (monomialPencil (20 * n) n (24 * n))
    (monomialPencil_integral_above_N (20 * n) n (24 * n) hp hNp (by omega))
  have hd : PolynomialPadicLower p 0 (monomialPencil (20 * n) n (24 * n)).det := by
    simpa only [Matrix.submatrix_id_id] using hM (24 * n) id id
  simpa using windowDeterminant_padicLower_of_monomial n 0 hlarge hd

theorem windowDeterminant_integral_above_window (n : ℕ) (hn : 0 < n) (hp : 50 * n < p) :
    PolynomialPadicLower p 0 (windowDeterminant n) := by
  have hcharge : factorialCharge (20 * n) n (24 * n) p = 0 := by
    unfold factorialCharge
    have hN : 20 * n < p := by omega
    rw [Nat.div_eq_of_lt hN]
    have he : ∀ k : Fin (24 * n), (2 * (n + k.val)) / p = 0 := by
      intro k
      exact Nat.div_eq_of_lt (by have hk := k.isLt; omega)
    simp only [he, Nat.cast_zero, sum_const_zero, mul_zero, sub_zero]
  simpa only [hcharge, neg_zero] using windowDeterminant_largePrime_bound (p := p) n hn (by omega)

#print axioms monomialPencil_integral_above_N
#print axioms windowDeterminant_integral_above_window

end Zeta5.Arithmetic
