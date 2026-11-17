import Zeta5.Analysis.GramBound
import Zeta5.Analysis.PhysicalNorm
import Zeta5.Analysis.PhysicalMeasureStieltjes
import Zeta5.Construction.BasisChange

/-!
# The actual determinant is bounded by trial-polynomial physical norms

The exact rational change of basis is evaluated at the actual value ζ(5).
The physical Stieltjes identity identifies the resulting polynomial functional.
The monic Gram estimate then applies to any trial family, with every factorial
normalization retained explicitly.
-/

noncomputable section

namespace Zeta5.Analysis

open Polynomial Matrix Zeta5.Construction
open scoped BigOperators

def realCommonFactor (m : ℕ) : ℝ[X] := (commonFactor m).map (Rat.castHom ℝ)

def commonMomentFunctional (N m : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (PhysicalMeasure.momentFunctional N).comp (LinearMap.mulLeft ℝ ((realCommonFactor m)^2))

lemma commonFactor_ne_zero (m : ℕ) : commonFactor m ≠ 0 := by
  intro h
  exact rootPolynomial_ne_zero m (Polynomial.comp_neg_X_eq_zero_iff.mp h)

lemma realCommonFactor_ne_zero (m : ℕ) : realCommonFactor m ≠ 0 := by
  exact Polynomial.map_ne_zero (commonFactor_ne_zero m)

lemma commonMomentFunctional_square_pos (N m : ℕ) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < commonMomentFunctional N m (p^2) := by
  change 0 < PhysicalMeasure.momentFunctional N ((realCommonFactor m)^2*p^2)
  rw [← mul_pow]
  exact PhysicalMeasure.momentFunctional_square_pos N _ (mul_ne_zero (realCommonFactor_ne_zero m) hp)

lemma commonFactor_eq_factorial_mul_windowBasis (m : ℕ) :
    commonFactor m = C (Nat.factorial (2*m) : ℚ)*windowBasis m := by
  rw [windowBasis, centralPolynomial, mul_comp, C_comp]
  change commonFactor m = C _*(C _*commonFactor m)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (factorial_cast_ne_zero _), map_one, one_mul]

lemma realCommonFactor_eq_factorial_mul_windowBasis (m : ℕ) :
    realCommonFactor m = C (Nat.factorial (2*m) : ℝ)*realWindowBasis m := by
  rw [realCommonFactor, commonFactor_eq_factorial_mul_windowBasis,
    Polynomial.map_mul, Polynomial.map_C]
  simp only [Rat.coe_castHom, Rat.cast_natCast, realWindowBasis]

lemma commonMomentFunctional_square_eq (N m : ℕ) (p : ℝ[X]) :
    commonMomentFunctional N m (p^2) =
      (Nat.factorial (2*m) : ℝ)^2*windowSquaredNorm N m p := by
  change PhysicalMeasure.momentFunctional N ((realCommonFactor m)^2*p^2) = _
  rw [realCommonFactor_eq_factorial_mul_windowBasis]
  have heq : (C (Nat.factorial (2*m) : ℝ)*realWindowBasis m)^2*p^2 =
      ((Nat.factorial (2*m) : ℝ)^2) • ((realWindowBasis m)^2*p^2) := by
    rw [Polynomial.smul_eq_C_mul, map_pow]
    ring
  rw [heq, map_smul]
  rfl

theorem monomialPencil_eval_realZetaFive (N m r : ℕ) :
    (monomialPencil N m r).map
        (Polynomial.eval₂RingHom (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5)) =
      realMonomialGram (commonMomentFunctional N m) r := by
  ext i j : 2
  simp only [Matrix.map_apply, monomialPencil, monomialGram,
    weightedNumeratorFunctional, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Polynomial.coe_eval₂RingHom, realMonomialGram, polynomialGram, commonMomentFunctional]
  rw [← PhysicalMeasure.momentFunctional_eq_numeratorFunctional_realZetaFive]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, realCommonFactor, pow_add]

def gramNormFactor (N m k : ℕ) : ℝ :=
  (Nat.factorial N : ℝ)^2*(Nat.factorial (2*m) : ℝ)^2/
    (Nat.factorial (2*(m+k)) : ℝ)^2

lemma gramNormFactor_pos (N m k : ℕ) : 0 < gramNormFactor N m k := by
  unfold gramNormFactor
  positivity

theorem evaluated_windowDeterminant_factorization (N m r : ℕ) :
    (Matrix.det (fun i j : Fin r => entry N (m+i.val) (m+j.val))).eval₂
        (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) =
      (∏ k : Fin r, (Nat.factorial N : ℝ)^2*
        ((Nat.factorial (2*(m+k.val)) : ℝ)⁻¹)^2)*
          (realMonomialGram (commonMomentFunctional N m) r).det := by
  rw [windowDeterminant_change_of_basis, eval₂_mul, eval₂_C]
  have hdet : ((monomialPencil N m r).det).eval₂
      (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) =
      (realMonomialGram (commonMomentFunctional N m) r).det := by
    change (Polynomial.eval₂RingHom _ _) (monomialPencil N m r).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply, monomialPencil_eval_realZetaFive]
  rw [hdet]
  congr 1
  simp only [Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_prod, Rat.cast_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- The actual determinant evaluated at ζ(5), bounded by any finite monic
degree-ordered trial family for the physical norm. -/
theorem evaluated_windowDeterminant_le_trial_norms (N m r : ℕ) (p : Fin r → ℝ[X])
    (hpm : ∀ k, (p k).Monic) (hpd : ∀ k, (p k).natDegree = k.val) :
    (Matrix.det (fun i j : Fin r => entry N (m+i.val) (m+j.val))).eval₂
        (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) ≤
      (Nat.factorial r : ℝ)*∏ k : Fin r,
        gramNormFactor N m k.val*windowSquaredNorm N m (p k) := by
  have hg := realMonomialGram_det_le_trial_product (commonMomentFunctional N m)
    (commonMomentFunctional_square_pos N m) r p hpm hpd
  rw [evaluated_windowDeterminant_factorization]
  calc
    _ ≤ (∏ k : Fin r, (Nat.factorial N : ℝ)^2*
        ((Nat.factorial (2*(m+k.val)) : ℝ)⁻¹)^2)*
          ((Nat.factorial r : ℝ)*∏ k, commonMomentFunctional N m ((p k)^2)) :=
      mul_le_mul_of_nonneg_left hg (Finset.prod_nonneg (fun _ _ => by positivity))
    _ = (Nat.factorial r : ℝ)*∏ k : Fin r,
        ((Nat.factorial N : ℝ)^2*((Nat.factorial (2*(m+k.val)) : ℝ)⁻¹)^2)*
          commonMomentFunctional N m ((p k)^2) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      rw [commonMomentFunctional_square_eq]
      simp only [gramNormFactor, div_eq_mul_inv, inv_pow]
      ring

theorem windowDeterminant_le_trial_norms (n : ℕ) (p : Fin (24*n) → ℝ[X])
    (hpm : ∀ k, (p k).Monic) (hpd : ∀ k, (p k).natDegree = k.val) :
    (windowDeterminant n).eval₂ (Rat.castHom ℝ) (Zeta5.Endpoint.realZeta 5) ≤
      (Nat.factorial (24*n) : ℝ)*∏ k : Fin (24*n),
        gramNormFactor (20*n) n k.val*windowSquaredNorm (20*n) n (p k) :=
  evaluated_windowDeterminant_le_trial_norms (20*n) n (24*n) p hpm hpd

end Zeta5.Analysis
