import Zeta5.Arithmetic.Newton

/-!
# Local Newton substitution

For a polynomial integer-valued at `p` of degree below `p²`, substitution
`x = c + pY` has integral coefficients, and every coefficient above degree
`floor(L/p)` is divisible by `p`.  This is the coefficient form of the
manuscript's reduction-degree assertion.

The proof groups consecutive falling-factorial factors into blocks of
length `p`.  Every block gains a factor of `p`; independently, its `k`th
coefficient after substitution gains `p^k`.  Dividing by the exact factorial
valuation proves both assertions.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue

def localAffine (p : ℕ) (c : ℤ) : ℚ[X] := C (c : ℚ) + C (p : ℚ) * X

variable {p : ℕ} [Fact p.Prime]

theorem localAffine_integral (c : ℤ) : PolynomialPadicLower p 0 (localAffine p c) := by
  have h : PolynomialPadicLower p 0 (C (p : ℚ) * X) := by
    simpa using (PolynomialPadicLower.constant (padicLower_nat (p := p) p)).mul
      (polynomialPadicLower_X (p := p))
  exact (PolynomialPadicLower.constant (padicLower_int c)).add h

theorem local_integerPolynomial_coeff (P : ℤ[X]) (c : ℤ) (k : ℕ) :
    PadicLower p (k : ℤ)
      (((P.map (Int.castRingHom ℚ)).comp (localAffine p c)).coeff k) := by
  have he : (P.map (Int.castRingHom ℚ)).comp (localAffine p c) =
      ((P.taylor c).map (Int.castRingHom ℚ)).comp (C (p : ℚ) * X) := by
    rw [map_taylor, taylor_apply, comp_assoc]
    simp only [add_comp, X_comp, C_comp, Int.coe_castRingHom]
    simp [localAffine, add_comm]
  rw [he, comp_C_mul_X_coeff]
  have hp : PadicLower p (k : ℤ) ((p : ℚ) ^ k) := by
    right
    simp [padicValRat.self (Fact.out : p.Prime).one_lt]
  simpa using (polynomialPadicLower_integer_map (p := p) (P.taylor c) k).mul hp

theorem local_descPochhammer_coeff (n : ℕ) (c : ℤ) (k : ℕ) :
    PadicLower p (k : ℤ) (((descPochhammer ℚ n).comp (localAffine p c)).coeff k) := by
  simpa using local_integerPolynomial_coeff (p := p) (descPochhammer ℤ n) c k

theorem local_descPochhammer_integral (n : ℕ) (c : ℤ) :
    PolynomialPadicLower p 0 ((descPochhammer ℚ n).comp (localAffine p c)) :=
  fun k => (local_descPochhammer_coeff n c k).mono (Int.natCast_nonneg k)

theorem local_descPochhammer_prime (c : ℤ) :
    PolynomialPadicLower p 1 ((descPochhammer ℚ p).comp (localAffine p c)) := by
  intro k
  by_cases hk : k = 0
  · subst k
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp only [localAffine, eval_add, eval_C, eval_mul, eval_X, mul_zero, add_zero]
    have he : (descPochhammer ℚ p).eval (c : ℚ) =
        (p.factorial : ℚ) * (Ring.choose c p : ℤ) := by
      rw [← descPochhammer_eval_cast]
      have h := Ring.descPochhammer_eq_factorial_smul_choose c p
      rw [← eval_eq_smeval, nsmul_eq_mul] at h
      exact_mod_cast h
    rw [he]
    simpa using (padicLower_nat_of_dvd (p := p) p.factorial
      (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).mul (padicLower_int (Ring.choose c p))
  · exact (local_descPochhammer_coeff p c k).mono (by omega)

theorem local_descPochhammer_blocks (q r : ℕ) (c : ℤ) :
    PolynomialPadicLower p (q : ℤ)
      ((descPochhammer ℚ (p * q + r)).comp (localAffine p c)) := by
  induction q generalizing c with
  | zero => simpa using local_descPochhammer_integral (p := p) r c
  | succ q ih =>
    have hindex : p * (q + 1) + r = p + (p * q + r) := by ring
    rw [hindex, ← descPochhammer_mul, mul_comp, comp_assoc]
    have he : (X - (p : ℚ[X])).comp (localAffine p c) = localAffine p (c - p) := by
      simp only [sub_comp, X_comp, natCast_comp, localAffine, Int.cast_sub, Int.cast_natCast]
      rw [C_sub, C_eq_natCast]
      ring
    rw [he]
    have h := (local_descPochhammer_prime (p := p) c).mul (ih (c - p))
    simpa [add_comm] using h

theorem local_descPochhammer_floor (n : ℕ) (c : ℤ) :
    PolynomialPadicLower p ((n / p : ℕ) : ℤ)
      ((descPochhammer ℚ n).comp (localAffine p c)) := by
  have h := local_descPochhammer_blocks (p := p) (n / p) (n % p) c
  simpa only [Nat.div_add_mod] using h

theorem factorial_padicVal_of_lt_sq {n : ℕ} (hn : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  have hp : p.Prime := Fact.out
  have hq : n / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hn)
  rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul]
  have hnd : ¬p ∣ (n / p).factorial := by
    simpa only [hp.dvd_factorial] using not_le.mpr hq
  rw [padicValNat.eq_zero_of_not_dvd hnd, zero_add]

theorem inverse_factorial_padicLower {n : ℕ} (hn : n < p ^ 2) :
    PadicLower p (-((n / p : ℕ) : ℤ)) ((n.factorial : ℚ)⁻¹) := by
  right
  rw [padicValRat.inv, padicValRat.of_nat, factorial_padicVal_of_lt_sq hn]

theorem local_binomialPolynomial_integral {n : ℕ} (hn : n < p ^ 2) (c : ℤ) :
    PolynomialPadicLower p 0 ((binomialPolynomial n).comp (localAffine p c)) := by
  rw [binomialPolynomial, mul_comp, C_comp]
  have h := (PolynomialPadicLower.constant (inverse_factorial_padicLower hn)).mul
    (local_descPochhammer_floor (p := p) n c)
  simpa using h

theorem local_binomialPolynomial_high_coeff {n k : ℕ} (hn : n < p ^ 2)
    (hk : n / p < k) (c : ℤ) :
    PadicLower p 1 (((binomialPolynomial n).comp (localAffine p c)).coeff k) := by
  rw [binomialPolynomial, mul_comp, C_comp, coeff_C_mul]
  exact ((inverse_factorial_padicLower hn).mul (local_descPochhammer_coeff n c k)).mono
    (by omega)

theorem integerValuedAt_local_integral {g : ℚ[X]} {L : ℕ}
    (hg : IntegerValuedAt p g) (hL : g.natDegree ≤ L) (hLp : L < p ^ 2) (c : ℤ) :
    PolynomialPadicLower p 0 (g.comp (localAffine p c)) := by
  rw [← newtonExpansion_eq g hL, newtonExpansion, Polynomial.sum_comp]
  apply PolynomialPadicLower.sum
  intro a ha
  have haL : a ≤ L := Nat.le_of_lt_succ (mem_range.mp ha)
  rw [mul_comp, C_comp]
  simpa using (PolynomialPadicLower.constant (newtonCoefficient_padicLower hg a)).mul
    (local_binomialPolynomial_integral (haL.trans_lt hLp) c)

theorem integerValuedAt_local_high_coeff {g : ℚ[X]} {L k : ℕ}
    (hg : IntegerValuedAt p g) (hL : g.natDegree ≤ L) (hLp : L < p ^ 2)
    (hk : L / p < k) (c : ℤ) :
    PadicLower p 1 ((g.comp (localAffine p c)).coeff k) := by
  rw [← newtonExpansion_eq g hL, newtonExpansion, Polynomial.sum_comp, finsetSum_coeff]
  apply padicLower_sum
  intro a ha
  have haL : a ≤ L := Nat.le_of_lt_succ (mem_range.mp ha)
  rw [mul_comp, C_comp, coeff_C_mul]
  simpa using (newtonCoefficient_padicLower hg a).mul
    (local_binomialPolynomial_high_coeff (haL.trans_lt hLp)
      ((Nat.div_le_div_right haL).trans_lt hk) c)

end Zeta5.Arithmetic
