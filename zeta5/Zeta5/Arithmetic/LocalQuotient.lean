import Zeta5.Arithmetic.LocalDenominator
import Zeta5.Arithmetic.ReflectedCounts
import Zeta5.Arithmetic.BernoulliMoments

/-!
# Weighted bounds for the actual local polynomial quotient

The explicit monic and unit factors of the physical denominator preserve
the complete valuation lower bound of the numerator, including an extra
power on the restriction kernel. No quotient is treated as a formal
rational expression: the equality with an actual polynomial is required.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

theorem inverse_prime_power_padicLower (n : ℕ) :
    PadicLower p (-(n : ℤ)) (((p : ℚ) ^ n)⁻¹) := by
  right
  simp [padicValRat.inv, padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]

theorem factorial_square_padicLower {N : ℕ} (hN : N < p ^ 2) :
    PadicLower p (2 * ((N / p : ℕ) : ℤ)) ((N.factorial : ℚ) ^ 2) := by
  right
  rw [padicValRat.pow, padicValRat.of_nat, factorial_padicVal_of_lt_sq hN]
  norm_num

theorem localPhysicalQuotient_lower {N : ℕ} {c : ℤ} {P Q : ℚ[X]} {w : ℤ}
    (hP : PolynomialPadicLower p w P)
    (heq : P = (denominator N).comp (-(localAffine p c) ^ 2) * Q) :
    PolynomialPadicLower p (w - (physicalLocalMultiplicity N p c : ℤ)) Q := by
  let h := physicalLocalMultiplicity N p c
  let S : ℚ[X] := C ((p : ℚ) ^ h) * Q
  have hfactor : P = physicalLocalMonic N p c * (physicalLocalUnit N p c * S) := by
    rw [heq, denominator_local_factorization]
    dsimp [S, h]
    ring
  have hUS := polynomialPadicLower_quotient_of_monic hP
    (physicalLocalMonic_integral N c) (physicalLocalMonic_monic N c) hfactor
  have hS : PolynomialPadicLower p w S :=
    polynomialPadicLower_quotient_of_unit_constant hUS (physicalLocalUnit_integral N c)
      (physicalLocalUnit_constant_ne_zero N c) (physicalLocalUnit_inverse_constant_integral N c) rfl
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrecover : C (((p : ℚ) ^ h)⁻¹) * S = Q := by
    dsimp [S]
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hp0), C_1, one_mul]
  have hQ := (PolynomialPadicLower.constant (inverse_prime_power_padicLower (p := p) h)).mul hS
  rw [hrecover] at hQ
  convert hQ using 1 <;> dsimp [h] <;> omega

theorem normalized_localPhysicalQuotient_lower {N : ℕ} {c : ℤ} {P Q : ℚ[X]} {w : ℤ}
    (hN : N < p ^ 2) (hP : PolynomialPadicLower p w P)
    (heq : P = (denominator N).comp (-(localAffine p c) ^ 2) * Q) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - physicalLocalMultiplicity N p c)
      (C ((N.factorial : ℚ) ^ 2) * Q) := by
  have h := (PolynomialPadicLower.constant (factorial_square_padicLower hN)).mul
    (localPhysicalQuotient_lower hP heq)
  convert h using 1 <;> omega

theorem normalized_localPhysicalQuotient_zero {N : ℕ} {P Q : ℚ[X]} {w : ℤ}
    (hN : N < p ^ 2) (hP : PolynomialPadicLower p w P)
    (heq : P = (denominator N).comp (-(localAffine p 0) ^ 2) * Q) :
    PolynomialPadicLower p w (C ((N.factorial : ℚ) ^ 2) * Q) := by
  have h := normalized_localPhysicalQuotient_lower hN hP heq
  rw [physicalLocalMultiplicity_zero] at h
  simpa using h

theorem normalized_localPhysicalQuotient_reflected {N c : ℕ} {P Q : ℚ[X]} {w : ℤ}
    (hc : 0 < c) (hcp : 2 * c < p) (hN : N < p ^ 2)
    (hP : PolynomialPadicLower p w P)
    (heq : P = (denominator N).comp (-(localAffine p c) ^ 2) * Q) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - reflectedSize N p c)
      (C ((N.factorial : ℚ) ^ 2) * Q) := by
  simpa only [physicalLocalMultiplicity_eq_reflectedSize N p c hc hcp] using
    normalized_localPhysicalQuotient_lower hN hP heq

theorem normalized_quotient_comp_lower {N : ℕ} {c : ℤ} {F Q : ℚ[X]} {w : ℤ}
    (hN : N < p ^ 2)
    (hF : PolynomialPadicLower p w (F.comp (-(localAffine p c) ^ 2)))
    (heq : F = denominator N * Q) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - physicalLocalMultiplicity N p c)
      ((C ((N.factorial : ℚ) ^ 2) * Q).comp (-(localAffine p c) ^ 2)) := by
  rw [mul_comp, C_comp]
  apply normalized_localPhysicalQuotient_lower hN hF
  rw [heq, mul_comp]

/-- Every integer has a representative up to sign in the reflected half
of the residue system. -/
theorem reflected_integer_representative (p : ℕ) (hodd : p % 2 = 1) (k : ℤ) :
    ∃ c : ℕ, ∃ y : ℤ, c ≤ (p - 1) / 2 ∧
      (k = (c : ℤ) + p * y ∨ k = -((c : ℤ) + p * y)) := by
  have hp : 0 < (p : ℤ) := by exact_mod_cast (show 0 < p by omega)
  let m := (k % (p : ℤ)).toNat
  have hmcast : (m : ℤ) = k % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne')
  have hm : m < p := by
    have := Int.emod_lt_of_pos k hp
    exact_mod_cast (hmcast ▸ this)
  have hk : k = (m : ℤ) + (p : ℤ) * (k / p) := by
    rw [hmcast]
    exact (Int.emod_add_mul_ediv k p).symm
  by_cases hhalf : 2 * m < p
  · exact ⟨m, k / p, by omega, Or.inl hk⟩
  · refine ⟨p - m, -(k / p) - 1, by omega, Or.inr ?_⟩
    calc
      k = (m : ℤ) + (p : ℤ) * (k / p) := hk
      _ = _ := by rw [Nat.cast_sub hm.le]; ring

theorem negativeSquare_integerValued_of_local {Q : ℚ[X]} {w : ℤ} (hodd : p % 2 = 1)
    (hlocal : ∀ c : ℕ, c ≤ (p - 1) / 2 →
      PolynomialPadicLower p w (Q.comp (-(localAffine p c) ^ 2))) :
    IntegerValuedLower p w (Q.comp (-(X ^ 2))) := by
  intro k
  obtain ⟨c, y, hc, hk⟩ := reflected_integer_representative p hodd k
  have h := (hlocal c hc).eval_integral (padicLower_int y)
  simp only [eval_comp, eval_neg, eval_pow, eval_X, localAffine, eval_add, eval_C, eval_mul] at h ⊢
  rcases hk with hk | hk
  · have hkQ : (k : ℚ) = (c : ℚ) + p * y := by exact_mod_cast hk
    simpa only [hkQ, Int.cast_natCast] using h
  · have hkQ : (k : ℚ) = -((c : ℚ) + p * y) := by exact_mod_cast hk
    simpa only [hkQ, neg_sq, Int.cast_natCast] using h

theorem normalized_quotient_integerValued {N L : ℕ} {F Q : ℚ[X]}
    (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (heq : F = denominator N * Q) :
    IntegerValuedLower p (-1 - ((2 * (N % p) / p : ℕ) : ℤ))
      ((C ((N.factorial : ℚ) ^ 2) * Q).comp (-(X ^ 2))) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  apply negativeSquare_integerValued_of_local hodd
  intro c hc
  have hlocal : PolynomialPadicLower p 0 (F.comp (-(localAffine p c) ^ 2)) := by
    simpa only [comp_assoc, neg_comp, pow_comp, X_comp] using
      integerValuedAt_local_integral hF hL hLp (c : ℤ)
  have h := normalized_quotient_comp_lower hN hlocal heq
  by_cases hc0 : c = 0
  · subst c
    rw [Nat.cast_zero, physicalLocalMultiplicity_zero] at h
    exact h.mono (by simp only [Nat.cast_mul, Nat.cast_ofNat, zero_add]; omega)
  · have hcp : 2 * c < p := by omega
    rw [physicalLocalMultiplicity_eq_reflectedSize N p c (by omega) hcp] at h
    have hsize := reflectedSize_le_max N p c hodd (by omega) hc
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    exact h.mono (by omega)

theorem normalized_quotient_integerValued_on_kernel {N L : ℕ} {F Q : ℚ[X]}
    (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (F.comp (-(localAffine p c) ^ 2)))
    (heq : F = denominator N * Q) :
    IntegerValuedLower p (-((2 * (N % p) / p : ℕ) : ℤ))
      ((C ((N.factorial : ℚ) ^ 2) * Q).comp (-(X ^ 2))) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  apply negativeSquare_integerValued_of_local hodd
  intro c hc
  have hlocal : PolynomialPadicLower p 0 (F.comp (-(localAffine p c) ^ 2)) := by
    simpa only [comp_assoc, neg_comp, pow_comp, X_comp] using
      integerValuedAt_local_integral hF hL hLp (c : ℤ)
  by_cases hc0 : c = 0
  · subst c
    have h := normalized_quotient_comp_lower hN hlocal heq
    rw [Nat.cast_zero, physicalLocalMultiplicity_zero] at h
    exact h.mono (by simp only [Nat.cast_mul, Nat.cast_ofNat, zero_add]; omega)
  · have hcp : 2 * c < p := by omega
    have hsize := reflectedSize_le_max N p c hodd (by omega) hc
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    by_cases hmax : c ∈ maximalReflectedClasses N p
    · have h := normalized_quotient_comp_lower hN (hkernel c hmax) heq
      rw [physicalLocalMultiplicity_eq_reflectedSize N p c (by omega) hcp] at h
      exact h.mono (by omega)
    · have hne : reflectedSize N p c ≠ 2 * (N / p) + 1 + 2 * (N % p) / p := by
        intro he
        exact hmax (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hc⟩, he⟩)
      have h := normalized_quotient_comp_lower hN hlocal heq
      rw [physicalLocalMultiplicity_eq_reflectedSize N p c (by omega) hcp] at h
      have hne' : (reflectedSize N p c : ℤ) ≠
          2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hne
      exact h.mono (by omega)

theorem bernoulliMomentNumerator_integerValued {Q : ℚ[X]} {w : ℤ}
    (hQ : IntegerValuedLower p w (Q.comp (-(X ^ 2)))) :
    IntegerValuedLower p w (bernoulliMomentNumerator Q) := by
  intro k
  have hpower : PadicLower p 0 ((k : ℚ) ^ 5) := by
    have he : ((k ^ 5 : ℤ) : ℚ) = (k : ℚ) ^ 5 := by push_cast; rfl
    rw [← he]
    exact padicLower_int (p := p) (k ^ 5)
  simpa only [bernoulliMomentNumerator, eval_mul, eval_pow, eval_X, zero_add] using
    hpower.mul (hQ k)

theorem normalized_quotient_moment_lower {N L M : ℕ} {F Q : ℚ[X]}
    (hp : 5 < p) (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (hM : (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * Q)).natDegree ≤ M)
    (hMp : M + 1 < p ^ 2) (heq : F = denominator N * Q) :
    PadicLower p (-5 - ((2 * (N % p) / p : ℕ) : ℤ))
      (polynomialMoment (C ((N.factorial : ℚ) ^ 2) * Q)) := by
  have h := polynomialMoment_padicLower_of_integerValuedNumerator hp
    (bernoulliMomentNumerator_integerValued (normalized_quotient_integerValued hodd hN hF hL hLp heq))
    hM hMp
  convert h using 1 <;> omega

theorem normalized_quotient_moment_lower_on_kernel {N L M : ℕ} {F Q : ℚ[X]}
    (hp : 5 < p) (hodd : p % 2 = 1) (hN : N < p ^ 2)
    (hF : IntegerValuedAt p (F.comp (-(X ^ 2))))
    (hL : (F.comp (-(X ^ 2))).natDegree ≤ L) (hLp : L < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (F.comp (-(localAffine p c) ^ 2)))
    (hM : (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * Q)).natDegree ≤ M)
    (hMp : M + 1 < p ^ 2) (heq : F = denominator N * Q) :
    PadicLower p (-4 - ((2 * (N % p) / p : ℕ) : ℤ))
      (polynomialMoment (C ((N.factorial : ℚ) ^ 2) * Q)) := by
  have h := polynomialMoment_padicLower_of_integerValuedNumerator hp
    (bernoulliMomentNumerator_integerValued
      (normalized_quotient_integerValued_on_kernel hodd hN hF hL hLp hkernel heq)) hM hMp
  convert h using 1 <;> omega

end Zeta5.Arithmetic
