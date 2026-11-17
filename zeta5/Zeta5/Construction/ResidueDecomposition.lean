import Zeta5.Construction.BasisChange
import Zeta5.Arithmetic.QuotientMinors

/-! The actual monomial pencil is a quotient matrix plus rank-one
residue atoms. No estimate or analytic identity is used in this equality. -/

noncomputable section
namespace Zeta5.Construction
open Polynomial Zeta5.Arithmetic

def monomialAtomWeight (N m i : ℕ) : ℚ[X] :=
  C (((commonFactor m).eval (pole i)) ^ 2 /
    (denominator N).derivative.eval (pole i)) * stieltjes i

def monomialAtom (N m r i : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun k l => monomialAtomWeight N m i * C ((pole i) ^ (k.val + l.val))

theorem monomialPencil_residue_decomposition (N m r : ℕ) :
    monomialPencil N m r = quotientPencil N m r +
      ∑ i ∈ Finset.range N, monomialAtom N m r (i + 1) := by
  funext k l
  simp only [monomialPencil, monomialGram, weightedNumeratorFunctional,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, numeratorFunctional_apply,
    Matrix.add_apply, Matrix.sum_apply, quotientPencil, monomialAtom,
    quotientMoment_eq_manuscript, commonFactor, monomialAtomWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eval_mul, eval_pow, eval_X, div_eq_mul_inv, map_mul]
  ring

theorem monomialAtom_rank_one (N m r i : ℕ) (k l : Fin r) :
    monomialAtom N m r i k l =
      C ((pole i) ^ k.val) * monomialAtomWeight N m i * C ((pole i) ^ l.val) := by
  simp only [monomialAtom, pow_add, map_mul]
  ring

theorem monomialAtom_eq_zero_of_lt {N m r i : ℕ} (hi : i < m) :
    monomialAtom N m r i = 0 := by
  funext k l
  have hroot : (commonFactor m).eval (pole i) = 0 := by
    simpa [commonFactor, eval_comp, pole] using rootPolynomial_eval_square_eq_zero hi
  simp [monomialAtom, monomialAtomWeight, hroot]

#print axioms monomialPencil_residue_decomposition

end Zeta5.Construction
