import Zeta5.Arithmetic.ReflectedMinors

/-! Integrality of the zero residue class in the upper prime band. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem commonFactor_zero_class_gain (m i : ℕ) (hm : 0 < m) (hpi : p ∣ i) :
    PadicLower p 4 (((commonFactor m).eval (pole i)) ^ 2) := by
  have hX : (X : ℤ[X]) ∣ commonRootInt m := by
    have h := Finset.dvd_prod_of_mem (fun a : ℕ => (X + C ((a : ℤ) ^ 2) : ℤ[X]))
      (Finset.mem_range.mpr hm)
    norm_num at h
    simpa [commonRootInt] using h
  obtain ⟨Q, hQ⟩ := hX
  have hi : PadicLower p 1 (i : ℚ) := by
    simpa using padicLower_int_of_dvd (p := p) (i : ℤ) (by exact_mod_cast hpi)
  have hi2 : PadicLower p 2 (-((i : ℚ) ^ 2)) := by
    simpa only [pow_two, show (1 : ℤ) + 1 = 2 from rfl] using (hi.mul hi).neg
  have hq := padicLower_int (p := p) (Q.eval (-((i : ℤ) ^ 2)))
  have hprod := hi2.mul hq
  rw [commonFactor_eval_sq_eq_integer, hQ, eval_mul, eval_X]
  push_cast
  simpa only [pow_two, add_zero, show (2 : ℤ) + 2 = 4 from rfl] using hprod.mul hprod

theorem denominator_derivative_zero_class_le_two (N i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hN : N < 3 * p) (hsmall : 2 * N < p ^ 2) :
    padicValRat p ((denominator N).derivative.eval (pole i)) ≤ 2 := by
  have hp0 : 0 < p := by omega
  have hq : N / p < 3 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have hv : 1 ≤ (padicValNat p i : ℤ) := by
    have h := padicLower_int_of_dvd (p := p) (i : ℤ) (by exact_mod_cast hpi)
    have hiQ : ((i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
    have hv := h.of_ne_zero hiQ
    simpa using hv
  have hf := reflected_floor_sum N i p hp0 hiN
  rw [Nat.mod_eq_zero_of_dvd hpi] at hf
  simp only [reflectedSize, Nat.zero_le, if_true, Nat.sub_zero,
    if_neg (not_le_of_gt (Nat.mod_lt N hp0)), Nat.add_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hf
  rw [denominator_derivative_valuation N i hp hi hiN (by omega)]
  omega

theorem zero_class_atom_integral (N m r i : ℕ) (hp : 5 < p)
    (hm : 0 < m) (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hN : N < 3 * p) (hsmall : 2 * N < p ^ 2) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (monomialAtom N m r i k l) := by
  have hw := monomialAtomWeight_bound N m i 4 (-1) 2
    (commonFactor_zero_class_gain m i hm hpi)
    (stieltjes_polynomial_multiple_p i hp hi (by omega) hpi)
    (denominator_derivative_zero_class_le_two N i (by omega) hi hiN hpi hN hsmall)
  have hw0 : PolynomialPadicLower p 0 (monomialAtomWeight N m i) := hw.mono (by norm_num)
  intro k l
  have hx := (polynomialPadicLower_integer_map (p := p)
    (C (-((i : ℤ) ^ 2)) : ℤ[X])).pow (k.val + l.val)
  have hx0 : PolynomialPadicLower p 0 (C ((pole i) ^ (k.val + l.val))) := by
    simpa [pole, map_pow] using hx
  exact hw0.mul hx0

#print axioms commonFactor_zero_class_gain
#print axioms zero_class_atom_integral

end Zeta5.Arithmetic
