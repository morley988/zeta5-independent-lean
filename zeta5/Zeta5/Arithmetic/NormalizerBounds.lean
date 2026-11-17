import Zeta5.Endpoint.PrimitiveNormalization
import Zeta5.Reuse.ProductFormula
import Zeta5.Reuse.PolynomialValuations

/-! Coefficientwise valuations bound the primitive rational normalizer,
including negative local charges. The rational product formula is directly
reused from the four-value proof. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Endpoint Finset
open OddZeta.FourValue.ProductFormula

theorem primitive_coefficient_prime_unit (P : ℤ[X]) (hP : P.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : ∃ n, ¬(p : ℤ) ∣ P.coeff n := by
  by_contra! h
  have hu := hP (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).mpr h)
  rcases Int.isUnit_iff.mp hu with h1 | h2 <;> have hpp := hp.one_lt <;> omega

theorem primitiveNormalizer_padicVal_le (F : ℚ[X]) (hF : F ≠ 0)
    (p : ℕ) [Fact p.Prime] (b : ℤ) (hval : PolynomialPadicLower p b F) :
    padicValRat p (primitiveNormalizer F) ≤ -b := by
  let P := normalizedPolynomial F
  obtain ⟨n, hn⟩ := primitive_coefficient_prime_unit P
    (normalizedPolynomial_isPrimitive F hF) p (Fact.out : p.Prime)
  have hn0 : P.coeff n ≠ 0 := by intro he; exact hn (he ▸ dvd_zero _)
  have hcoeff : ((P.coeff n : ℤ) : ℚ) = primitiveNormalizer F * F.coeff n := by
    have h := congrArg (fun Q : ℚ[X] => Q.coeff n) (normalizedPolynomial_map F)
    simpa [P] using h
  have hq0 := (primitiveNormalizer_pos F).ne'
  have hf0 : F.coeff n ≠ 0 := by
    intro he
    rw [he, mul_zero] at hcoeff
    exact hn0 (by exact_mod_cast hcoeff)
  have hz : padicValRat p (((P.coeff n : ℤ) : ℚ)) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hn]
    rfl
  rw [hcoeff, padicValRat.mul hq0 hf0] at hz
  have hb := (hval n).of_ne_zero hf0
  omega

theorem valuation_zero_off_support (q : ℚ) (p : ℕ) (hp : p.Prime)
    (h : p ∉ primeSupport q) : padicValRat p q = 0 := by
  have hn : q.num.natAbs.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun hh => h (mem_union_left _ hh)
  have hd : q.den.factorization p = 0 := by
    apply Finsupp.notMem_support_iff.mp
    exact fun hh => h (mem_union_right _ hh)
  rw [Nat.factorization_def _ hp] at hn hd
  simp [padicValRat, padicValInt, hn, hd]

theorem finite_prime_upper (q : ℚ) (hq : q ≠ 0) (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hw : ∀ p ∈ S, (padicValRat p q : ℝ) ≤ w p)
    (hout : ∀ p, p.Prime → p ∉ S → padicValRat p q ≤ 0) :
    Real.log |(q : ℝ)| ≤ ∑ p ∈ S, w p * Real.log p := by
  rw [rational_log_product_formula q hq]
  have he : (∑ p ∈ primeSupport q, (padicValRat p q : ℝ) * Real.log p) =
      ∑ p ∈ S ∪ primeSupport q, (padicValRat p q : ℝ) * Real.log p := by
    apply sum_subset subset_union_right
    intro p hp hn
    have hps : p ∈ S := (mem_union.mp hp).resolve_right hn
    rw [valuation_zero_off_support q p (hS p hps) hn]
    simp
  rw [he]
  have hdiscard : (∑ p ∈ S ∪ primeSupport q, (padicValRat p q : ℝ) * Real.log p) ≤
      ∑ p ∈ S, (padicValRat p q : ℝ) * Real.log p := by
    have h := sum_le_sum_of_subset_of_nonneg (f := fun p => -((padicValRat p q : ℝ) * Real.log p))
      (subset_union_left (s₂ := primeSupport q) : S ⊆ S ∪ primeSupport q) (by
        intro p hp hn
        have hpr := support_prime q p ((mem_union.mp hp).resolve_left hn)
        exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
          (by exact_mod_cast hout p hpr hn)
          (Real.log_nonneg (by exact_mod_cast hpr.one_le))))
    simpa only [sum_neg_distrib, neg_le_neg_iff] using h
  exact hdiscard.trans (sum_le_sum (fun p hp =>
    mul_le_mul_of_nonneg_right (hw p hp) (Real.log_nonneg (by exact_mod_cast (hS p hp).one_le))))

theorem log_primitiveNormalizer_le_prime_sum (F : ℚ[X]) (hF : F ≠ 0)
    (S : Finset ℕ) (cost : ℕ → ℤ) (hS : ∀ p ∈ S, p.Prime)
    (hval : ∀ p ∈ S, ∀ hp : Fact p.Prime, PolynomialPadicLower p (-(cost p)) F)
    (hout : ∀ p, p.Prime → p ∉ S → ∀ hp : Fact p.Prime, PolynomialPadicLower p 0 F) :
    Real.log (primitiveNormalizer F : ℝ) ≤ ∑ p ∈ S, (cost p : ℝ) * Real.log p := by
  have hpos : (0 : ℝ) < primitiveNormalizer F := by exact_mod_cast primitiveNormalizer_pos F
  have h := finite_prime_upper (primitiveNormalizer F) (primitiveNormalizer_pos F).ne' S
    (fun p => (cost p : ℝ)) hS (by
      intro p hp
      letI : Fact p.Prime := ⟨hS p hp⟩
      have h := primitiveNormalizer_padicVal_le F hF p (-(cost p)) (hval p hp inferInstance)
      exact_mod_cast (by simpa using h : padicValRat p (primitiveNormalizer F) ≤ cost p)) (by
      intro p hp hpS
      letI : Fact p.Prime := ⟨hp⟩
      simpa using primitiveNormalizer_padicVal_le F hF p 0 (hout p hp hpS inferInstance))
  simpa only [abs_of_pos hpos] using h

#print axioms primitiveNormalizer_padicVal_le
#print axioms log_primitiveNormalizer_le_prime_sum

end Zeta5.Arithmetic
