import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Polynomial Gram matrices and affine determinant adapters

These are unconditional general lemmas.  The positive-square hypothesis
on a linear functional is explicit; this file does not assume that the
manuscript's particular functional has that property.
-/

namespace Zeta5.Analysis

open Polynomial Matrix
open scoped BigOperators

section PolynomialGram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gram matrix of a real polynomial family for a linear functional. -/
noncomputable def polynomialGram (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ι → ℝ[X]) : Matrix ι ι ℝ :=
  fun i j => L (p i * p j)

theorem polynomialGram_isHermitian (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ι → ℝ[X]) :
    (polynomialGram L p).IsHermitian := by
  ext i j
  simp [polynomialGram, Matrix.conjTranspose_apply, mul_comm]

/-- The quadratic form of a polynomial Gram matrix is the functional on
the square of the corresponding polynomial linear combination. -/
theorem polynomialGram_quadratic (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ι → ℝ[X])
    (x : ι → ℝ) :
    star x ⬝ᵥ ((polynomialGram L p) *ᵥ x) =
      L ((∑ i, x i • p i) ^ 2) := by
  simp [polynomialGram, dotProduct, mulVec, pow_two, Finset.mul_sum,
    map_sum, map_smul, smul_eq_mul, mul_left_comm, mul_comm]

theorem polynomialGram_posDef (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))
    (p : ι → ℝ[X]) (hp : LinearIndependent ℝ p) :
    (polynomialGram L p).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (polynomialGram_isHermitian L p)
  intro x hx
  rw [polynomialGram_quadratic]
  apply hL
  intro hzero
  apply hx
  funext i
  exact Fintype.linearIndependent_iff.mp hp x hzero i

theorem polynomialGram_det_pos (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))
    (p : ι → ℝ[X]) (hp : LinearIndependent ℝ p) :
    0 < (polynomialGram L p).det :=
  (polynomialGram_posDef L hL p hp).det_pos

theorem scaled_polynomialGram_det_pos (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))
    (p : ι → ℝ[X]) (hp : LinearIndependent ℝ p)
    (c : ℝ) (hc : 0 < c) :
    0 < (c • polynomialGram L p).det := by
  rw [Matrix.det_smul]
  exact mul_pos (pow_pos hc _) (polynomialGram_det_pos L hL p hp)

/-- Any consecutive finite window in a polynomial sequence is independent. -/
theorem sequence_window_linearIndependent (S : Polynomial.Sequence ℝ) (m r : ℕ) :
    LinearIndependent ℝ (fun k : Fin r => S (m + k.val)) := by
  apply S.linearIndependent.comp
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel hij

theorem sequence_window_gram_det_pos (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))
    (S : Polynomial.Sequence ℝ) (m r : ℕ) :
    0 < (polynomialGram L (fun k : Fin r => S (m + k.val))).det :=
  polynomialGram_det_pos L hL _ (sequence_window_linearIndependent S m r)

end PolynomialGram

section AffinePencil

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing S]

/-- An affine polynomial matrix, with constant and linear coefficient matrices. -/
noncomputable def affinePencil (A₀ A₁ : Matrix ι ι R) : Matrix ι ι R[X] :=
  fun i j => C (A₀ i j) + X * C (A₁ i j)

noncomputable def affineDet (A₀ A₁ : Matrix ι ι R) : R[X] :=
  (affinePencil A₀ A₁).det

theorem affinePencil_eq (A₀ A₁ : Matrix ι ι R) :
    affinePencil A₀ A₁ = (X : R[X]) • A₁.map C + A₀.map C := by
  ext i j
  simp [affinePencil, add_comm]

/-- The matrix-size bound is enough for the irrationality contradiction,
since the matrix size is a fixed linear function of the asymptotic index. -/
theorem affineDet_natDegree_le (A₀ A₁ : Matrix ι ι R) :
    (affineDet A₀ A₁).natDegree ≤ Fintype.card ι := by
  rw [affineDet, affinePencil_eq]
  exact Polynomial.natDegree_det_X_add_C_le A₁ A₀

theorem eval₂_affineDet (A₀ A₁ : Matrix ι ι R) (f : R →+* S) (x : S) :
    Polynomial.eval₂ f x (affineDet A₀ A₁) =
      (A₀.map f + x • A₁.map f).det := by
  change (Polynomial.eval₂RingHom f x) (affinePencil A₀ A₁).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [affinePencil, Matrix.map_apply]
  exact mul_comm _ _

end AffinePencil

section RationalPencil

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem affineDet_pos_of_gram (A₀ A₁ : Matrix ι ι ℚ) (x : ℝ)
    (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))
    (p : ι → ℝ[X]) (hp : LinearIndependent ℝ p)
    (c : ℝ) (hc : 0 < c)
    (hgram : A₀.map (Rat.castHom ℝ) + x • A₁.map (Rat.castHom ℝ) =
      c • polynomialGram L p) :
    0 < Polynomial.eval₂ (Rat.castHom ℝ) x (affineDet A₀ A₁) := by
  rw [eval₂_affineDet, hgram]
  exact scaled_polynomialGram_det_pos L hL p hp c hc

theorem affineDet_ne_zero_of_eval₂_pos (A₀ A₁ : Matrix ι ι ℚ) (x : ℝ)
    (hpos : 0 < Polynomial.eval₂ (Rat.castHom ℝ) x (affineDet A₀ A₁)) :
    affineDet A₀ A₁ ≠ 0 := by
  intro hzero
  simp [hzero] at hpos

end RationalPencil

end Zeta5.Analysis
