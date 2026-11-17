import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Minimality of a primitive positive coefficient normalization

The manuscript allows a positive rational normalizer smaller than one, so a
generic denominator-clearing natural number is not a substitute.  The following
lemmas express the required primitive normalization and prove its minimality.
Existence is proved for every nonzero rational polynomial. The module does not
prove that the proposed determinant is nonzero, or bound its normalizer.
-/

noncomputable section
namespace Zeta5.Endpoint
open Polynomial
open scoped nonZeroDivisors

/-- An integer polynomial with primitive coefficients cannot be scaled by a
nonintegral rational while keeping all its coefficients integral. -/
theorem integral_scaling_of_primitive (P : ℤ[X]) (hP : P.IsPrimitive) (c : ℚ)
    (hc : C c * P.map (algebraMap ℤ ℚ) ∈ lifts (algebraMap ℤ ℚ)) :
    ∃ z : ℤ, (z : ℚ) = c := by
  have hC : C c ∈ lifts (algebraMap ℤ ℚ) := hP.mul_map_mem_lifts_iff.mp hc
  have hcoeff := (lifts_iff_coeff_lifts (C c)).mp hC 0
  simpa using hcoeff

/-- A positive rational scaling that produces a primitive integer polynomial.
The equality is coefficientwise in the ordinary polynomial ring. -/
def IsPrimitiveNormalization (F : ℚ[X]) (q : ℚ) : Prop :=
  0 < q ∧ ∃ P : ℤ[X], P.IsPrimitive ∧ P.map (algebraMap ℤ ℚ) = C q * F

theorem exists_primitive_normalization (F : ℚ[X]) (hF : F ≠ 0) :
    ∃ q : ℚ, IsPrimitiveNormalization F q := by
  let B : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) F
  obtain ⟨b, hb, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) F
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hBnz : B ≠ 0 := IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hF
  have hc0 : B.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hBnz
  have hcQ : (B.content : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hR : C (B.content : ℚ) * B.primPart.map (algebraMap ℤ ℚ) = C (b : ℚ) * F := by
    calc
      _ = B.map (algebraMap ℤ ℚ) := by
        conv_rhs => rw [B.eq_C_content_mul_primPart]
        simp
      _ = C (b : ℚ) * F := by
        simpa [B, zsmul_eq_mul] using hB
  have he : B.primPart.map (algebraMap ℤ ℚ) = C ((b : ℚ) / B.content) * F := by
    calc
      _ = C ((B.content : ℚ)⁻¹) * (C (B.content : ℚ) *
          B.primPart.map (algebraMap ℤ ℚ)) := by
        rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hcQ, C_1, one_mul]
      _ = C ((B.content : ℚ)⁻¹) * (C (b : ℚ) * F) := by rw [hR]
      _ = C ((b : ℚ) / B.content) * F := by
        simp only [← mul_assoc, ← Polynomial.C_mul]
        congr 2
        ring
  have hr0 : (b : ℚ) / B.content ≠ 0 := div_ne_zero hbQ hcQ
  rcases lt_or_gt_of_ne hr0 with hr | hr
  · refine ⟨-((b : ℚ) / B.content), neg_pos.mpr hr, -B.primPart, ?_, ?_⟩
    · intro z hz
      exact B.isPrimitive_primPart z (dvd_neg.mp hz)
    · simpa [he] using congrArg Neg.neg he
  · exact ⟨(b : ℚ) / B.content, hr, B.primPart, B.isPrimitive_primPart, he⟩

theorem primitive_normalization_ratio_integer {F : ℚ[X]} {q Q : ℚ}
    (hq : IsPrimitiveNormalization F q) (hQ : 0 < Q)
    (hintegral : C Q * F ∈ lifts (algebraMap ℤ ℚ)) :
    ∃ z : ℤ, 0 < z ∧ (z : ℚ) = Q / q := by
  obtain ⟨hqpos, P, hP, hPF⟩ := hq
  have he : C (Q / q) * P.map (algebraMap ℤ ℚ) = C Q * F := by
    rw [hPF, ← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ Q hqpos.ne']
  obtain ⟨z, hz⟩ := integral_scaling_of_primitive P hP (Q / q) (he ▸ hintegral)
  refine ⟨z, ?_, hz⟩
  have hzpos : (0 : ℚ) < z := by rw [hz]; exact div_pos hQ hqpos
  exact_mod_cast hzpos

theorem primitive_normalization_minimal {F : ℚ[X]} {q Q : ℚ}
    (hq : IsPrimitiveNormalization F q) (hQ : 0 < Q)
    (hintegral : C Q * F ∈ lifts (algebraMap ℤ ℚ)) : q ≤ Q := by
  obtain ⟨z, hzpos, hz⟩ := primitive_normalization_ratio_integer hq hQ hintegral
  have hzge : (1 : ℚ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  rw [hz] at hzge
  have h := (le_div_iff₀ hq.1).mp hzge
  simpa using h

theorem primitive_normalization_unique {F : ℚ[X]} {q Q : ℚ}
    (hq : IsPrimitiveNormalization F q) (hQ : IsPrimitiveNormalization F Q) :
    q = Q := by
  have hiq : C q * F ∈ lifts (algebraMap ℤ ℚ) := by
    obtain ⟨_, P, _, hP⟩ := hq
    exact ⟨P, hP⟩
  have hiQ : C Q * F ∈ lifts (algebraMap ℤ ℚ) := by
    obtain ⟨_, P, _, hP⟩ := hQ
    exact ⟨P, hP⟩
  exact le_antisymm (primitive_normalization_minimal hq hQ.1 hiQ)
    (primitive_normalization_minimal hQ hq.1 hiq)

/-- The unique primitive positive normalizer, with the harmless value one
assigned to the zero polynomial. -/
def primitiveNormalizer (F : ℚ[X]) : ℚ :=
  if hF : F = 0 then 1 else Classical.choose (exists_primitive_normalization F hF)

theorem primitiveNormalizer_spec (F : ℚ[X]) (hF : F ≠ 0) :
    IsPrimitiveNormalization F (primitiveNormalizer F) := by
  simpa only [primitiveNormalizer, dif_neg hF] using
    Classical.choose_spec (exists_primitive_normalization F hF)

theorem primitiveNormalizer_pos (F : ℚ[X]) : 0 < primitiveNormalizer F := by
  by_cases hF : F = 0
  · simp [primitiveNormalizer, hF]
  · exact (primitiveNormalizer_spec F hF).1

/-- The integer polynomial produced by primitive positive normalization. -/
def normalizedPolynomial (F : ℚ[X]) : ℤ[X] :=
  if hF : F = 0 then 0 else Classical.choose (primitiveNormalizer_spec F hF).2

theorem normalizedPolynomial_map (F : ℚ[X]) :
    (normalizedPolynomial F).map (algebraMap ℤ ℚ) = C (primitiveNormalizer F) * F := by
  by_cases hF : F = 0
  · simp [normalizedPolynomial, hF]
  · simpa only [normalizedPolynomial, dif_neg hF] using
      (Classical.choose_spec (primitiveNormalizer_spec F hF).2).2

theorem normalizedPolynomial_isPrimitive (F : ℚ[X]) (hF : F ≠ 0) :
    (normalizedPolynomial F).IsPrimitive := by
  simpa only [normalizedPolynomial, dif_neg hF] using
    (Classical.choose_spec (primitiveNormalizer_spec F hF).2).1

theorem normalizedPolynomial_natDegree (F : ℚ[X]) :
    (normalizedPolynomial F).natDegree = F.natDegree := by
  have h := Polynomial.natDegree_map_eq_of_injective
    (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective)
    (normalizedPolynomial F)
  rw [normalizedPolynomial_map, natDegree_C_mul (primitiveNormalizer_pos F).ne'] at h
  exact h.symm

theorem normalizedPolynomial_eval_real (F : ℚ[X]) (x : ℝ) :
    (normalizedPolynomial F).eval₂ (Int.castRingHom ℝ) x =
      (primitiveNormalizer F : ℝ) * F.eval₂ (Rat.castHom ℝ) x := by
  have h := congrArg (fun P : ℚ[X] => P.eval₂ (Rat.castHom ℝ) x)
    (normalizedPolynomial_map F)
  have hh : (Rat.castHom ℝ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℝ := by
    ext n
    simp
  rw [Polynomial.eval₂_map, hh] at h
  simpa using h

#print axioms integral_scaling_of_primitive
#print axioms exists_primitive_normalization
#print axioms primitive_normalization_ratio_integer
#print axioms primitive_normalization_minimal
#print axioms primitive_normalization_unique
#print axioms primitiveNormalizer_spec
#print axioms normalizedPolynomial_map
#print axioms normalizedPolynomial_natDegree
#print axioms normalizedPolynomial_eval_real

end Zeta5.Endpoint
