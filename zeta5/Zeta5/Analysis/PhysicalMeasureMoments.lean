import Zeta5.Analysis.PhysicalMeasure
import Zeta5.Construction.Determinant

/-!
# Exact Bernoulli moments of the physical density

The positive density in `PhysicalMeasure` has precisely the rational moments
used by `Construction.rationalMoment`.  This is an unconditional analytical
bridge for the polynomial part of the matrix entries.  The Stieltjes part of
the entries requires a separate identity and is not asserted here.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

/-- Euler's even-zeta formula, with the zero term omitted and factors arranged
for the physical moment calculation. -/
theorem evenZeta_series (k : ℕ) :
    (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2)) =
      (-1 : ℝ) ^ k * (2 * Real.pi) ^ (2 * k + 2) *
        (bernoulli (2 * k + 2) : ℝ) / (2 * (Nat.factorial (2 * k + 2) : ℝ)) := by
  have hz := hasSum_zeta_nat (k := k + 1) (by omega)
  have ht : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * (k + 1)))
      ((-1 : ℝ) ^ (k + 1 + 1) * 2 ^ (2 * (k + 1) - 1) * Real.pi ^ (2 * (k + 1)) *
        (bernoulli (2 * (k + 1)) : ℝ) / (Nat.factorial (2 * (k + 1)) : ℝ)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 * (k + 1))) 1).mpr
    simpa using hz
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    show k + 1 + 1 = k + 2 by omega,
    show 2 * k + 2 - 1 = 2 * k + 1 by omega] at ht
  rw [ht.tsum_eq, pow_add (-1 : ℝ) k 2]
  norm_num only [neg_one_sq, mul_one]
  rw [mul_pow, show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ (2 : ℝ)]
  ring

/-- The exact moment formula of the manuscript, now as an equality with a
convergent integral of the actual density. -/
theorem density_moment (k : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (2 * k) * density x) =
      (Zeta5.Construction.rationalMoment k : ℝ) := by
  rw [density_moment_zeta, evenZeta_series]
  have hp : (2 * Real.pi) ^ (2 * k + 2) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k + 2) : ℝ) ≠ 0 := by positivity
  have hfac : (Nat.factorial (2 * k + 5) : ℝ) =
      (2 * (k : ℝ) + 5) * (2 * k + 4) * (2 * k + 3) *
        (Nat.factorial (2 * k + 2) : ℝ) := by
    rw [show 2 * k + 5 = ((2 * k + 2) + 1) + 1 + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  unfold momentFactor Zeta5.Construction.rationalMoment
  push_cast
  rw [hfac]
  field_simp
  <;> ring

theorem density_mass : (∫ x : ℝ in Ioi 0, density x) = 5 / 12 := by
  simpa [Zeta5.Construction.rationalMoment_zero] using density_moment 0

end Zeta5.Analysis.PhysicalMeasure
