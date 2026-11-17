import Zeta5.Construction.Polynomials
import Mathlib.NumberTheory.Bernoulli
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Zeta5.Analysis.PolynomialGram

/-!
# Concrete rational determinant for the ζ(5) candidate

This file defines the actual rational polynomial in the manuscript, not an
uninterpreted substitute for it.  The correspondence with the positive
measure requires the analytic moment and Stieltjes identities, which are
separate proof obligations.  No such correspondence is assumed here.

Using a stage index `n` makes divisibility constraints exact:
`N=20n`, `m=n`, `R=25n`, and matrix size `r=24n`.
-/

noncomputable section
namespace Zeta5.Construction

open Polynomial

/-- Rational moments from the displayed Bernoulli formula. -/
def rationalMoment (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k / 24 * (2 * k + 3) * (2 * k + 4) * (2 * k + 5) *
    bernoulli (2 * k + 2)

def polynomialMoment (q : ℚ[X]) : ℚ :=
  q.sum (fun k a => a * rationalMoment k)

def harmonicFive (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℚ) ^ 5)

def stieltjesConstant (i : ℕ) : ℚ :=
  -(i : ℚ) ^ 4 * harmonicFive (i - 1) - 1 / (2 * (i : ℚ)) - 1 / 4

/-- The affine Stieltjes expression; applications use `i≥1`. -/
def stieltjes (i : ℕ) : ℚ[X] :=
  C (stieltjesConstant i) + X * C ((i : ℚ) ^ 4)

def numerator (j k : ℕ) : ℚ[X] := windowBasis j * windowBasis k

def pole (i : ℕ) : ℚ := -((i : ℚ) ^ 2)

def residueWeight (N j k i : ℕ) : ℚ :=
  (numerator j k).eval (pole i) / (denominator N).derivative.eval (pole i)

def entryConstant (N j k : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ 2 *
    (polynomialMoment (numerator j k / denominator N) +
      ∑ i ∈ Finset.range N, residueWeight N j k (i + 1) * stieltjesConstant (i + 1))

def entryLinear (N j k : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ 2 *
    ∑ i ∈ Finset.range N, residueWeight N j k (i + 1) * ((i + 1 : ℕ) : ℚ) ^ 4

def entry (N j k : ℕ) : ℚ[X] :=
  C (entryConstant N j k) + X * C (entryLinear N j k)

def windowPencil (n : ℕ) : Matrix (Fin (24 * n)) (Fin (24 * n)) ℚ[X] :=
  fun j k => entry (20 * n) (n + j.val) (n + k.val)

def windowConstant (n : ℕ) : Matrix (Fin (24 * n)) (Fin (24 * n)) ℚ :=
  fun j k => entryConstant (20 * n) (n + j.val) (n + k.val)

def windowLinear (n : ℕ) : Matrix (Fin (24 * n)) (Fin (24 * n)) ℚ :=
  fun j k => entryLinear (20 * n) (n + j.val) (n + k.val)

/-- `F_{20n}` in the manuscript. -/
def windowDeterminant (n : ℕ) : ℚ[X] := (windowPencil n).det

theorem rationalMoment_zero : rationalMoment 0 = 5 / 12 := by
  norm_num [rationalMoment, bernoulli]

theorem harmonicFive_zero : harmonicFive 0 = 0 := by simp [harmonicFive]

theorem stieltjes_one : stieltjes 1 = X - C (3 / 4) := by
  have hs : stieltjesConstant 1 = -(3 / 4 : ℚ) := by
    norm_num [stieltjesConstant, harmonicFive]
  simp only [stieltjes, hs, Nat.cast_one, one_pow, C_1, mul_one, C_neg]
  ring

theorem residueWeight_eq_zero_of_lt {N j k i : ℕ} (hij : i < j) :
    residueWeight N j k i = 0 := by
  simp [residueWeight, numerator, pole, windowBasis_eval_neg_square_eq_zero hij]

theorem entry_eval (N j k : ℕ) (x : ℚ) :
    (entry N j k).eval x = entryConstant N j k + x * entryLinear N j k := by
  simp only [entry, eval_add, eval_C, eval_mul, eval_X]

theorem windowDeterminant_eq_affineDet (n : ℕ) :
    windowDeterminant n = Zeta5.Analysis.affineDet (windowConstant n) (windowLinear n) := rfl

/-- The matrix-size degree bound suffices for the irrationality endpoint.
The sharper manuscript bound is unnecessary here. -/
theorem windowDeterminant_natDegree_le (n : ℕ) :
    (windowDeterminant n).natDegree ≤ 24 * n := by
  rw [windowDeterminant_eq_affineDet]
  simpa using Zeta5.Analysis.affineDet_natDegree_le (windowConstant n) (windowLinear n)

theorem windowDeterminant_eval_real (n : ℕ) (x : ℝ) :
    (windowDeterminant n).eval₂ (Rat.castHom ℝ) x =
      ((windowConstant n).map (Rat.castHom ℝ) + x •
        (windowLinear n).map (Rat.castHom ℝ)).det := by
  rw [windowDeterminant_eq_affineDet, Zeta5.Analysis.eval₂_affineDet]

end Zeta5.Construction
