import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Generic positive-integer endpoint for polynomial irrationality arguments

This module proves only the algebraic and order-theoretic closing criterion.
It neither defines nor assumes any particular zeta determinant.  The missing
application-specific estimates are explicit hypotheses of the last theorem.

The four-value project uses the same eventual-order comparison, but its
endpoint concerns nonzero selected minors and is not imported here.
-/

noncomputable section
namespace Zeta5.Endpoint
open scoped BigOperators Topology
open Filter Polynomial

/-- The integer obtained by homogenizing an integer polynomial to degree `N`
and evaluating at the integer pair `(a,b)`. -/
def scaledEvalInt (P : ℤ[X]) (a b : ℤ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), P.coeff i * a ^ i * b ^ (N - i)

/-- Clearing a rational argument uses the polynomial degree, not the matrix
size or an arbitrarily chosen denominator exponent. -/
theorem scaledEvalInt_cast (P : ℤ[X]) (a b : ℤ) (N : ℕ)
    (hb : b ≠ 0) (hdeg : P.natDegree ≤ N) :
    (scaledEvalInt P a b N : ℝ) =
      (b : ℝ) ^ N * P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (b : ℝ)) := by
  rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℝ)
    (Nat.lt_succ_iff.mpr hdeg)]
  simp only [scaledEvalInt, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.coe_castRingHom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have he : (b : ℝ) ^ N = (b : ℝ) ^ i * (b : ℝ) ^ (N - i) := by
    rw [← pow_add, Nat.add_sub_of_le hiN]
  rw [he, div_pow]
  field_simp

/-- The elementary obstruction underlying the final irrationality step. -/
theorem positive_integer_values_not_tendsto_zero (u : ℕ → ℝ)
    (hinteger : ∀ᶠ n in atTop, ∃ z : ℤ, u n = z)
    (hpositive : ∀ᶠ n in atTop, 0 < u n)
    (hzero : Tendsto u atTop (𝓝 0)) : False := by
  have hsmall := hzero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, ⟨z, hz⟩, hp, hs⟩ := (hinteger.and (hpositive.and hsmall)).exists
  rw [hz] at hp hs
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hp
  have hzge : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  linarith

/-- A sufficient criterion for irrationality from positive integer polynomials.
The denominator-dependent convergence hypothesis is a real mathematical input;
this theorem does not supply it for any chosen polynomial family. -/
theorem irrational_of_integer_polynomial_decay (x : ℝ) (P : ℕ → ℤ[X])
    (d : ℕ → ℕ) (hdeg : ∀ n, (P n).natDegree ≤ d n)
    (hpositive : ∀ᶠ n in atTop, 0 < (P n).eval₂ (Int.castRingHom ℝ) x)
    (hdecay : ∀ b : ℕ, 0 < b →
      Tendsto (fun n => (b : ℝ) ^ d n * (P n).eval₂ (Int.castRingHom ℝ) x)
        atTop (𝓝 0)) : Irrational x := by
  rintro ⟨q, hq⟩
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hbZ : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hx : x = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← hq]
    exact Rat.cast_def q
  apply positive_integer_values_not_tendsto_zero
    (fun n => (q.den : ℝ) ^ d n * (P n).eval₂ (Int.castRingHom ℝ) x)
  · filter_upwards [] with n
    refine ⟨scaledEvalInt (P n) q.num q.den (d n), ?_⟩
    rw [scaledEvalInt_cast (P n) q.num q.den (d n) hbZ (hdeg n)]
    simp [hx]
  · filter_upwards [hpositive] with n hn
    exact mul_pos (pow_pos hb _) hn
  · exact hdecay q.den q.den_pos

#print axioms scaledEvalInt_cast
#print axioms positive_integer_values_not_tendsto_zero
#print axioms irrational_of_integer_polynomial_decay

end Zeta5.Endpoint
