import Zeta5.Arithmetic.BernoulliFunctional
import Zeta5.Arithmetic.LocalNewton

/-!
# Bernoulli distribution over residue classes

The distribution relation follows from telescoping finite differences and
the uniqueness theorem for the Bernoulli functional. It holds for every
positive integer modulus, with no primality assumption.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue

def bernoulliDistribution (q : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (q : ℚ)⁻¹ • ∑ c ∈ range q,
    bernoulliFunctional.comp ((Polynomial.aeval (localAffine q (c : ℤ))).toLinearMap)

theorem bernoulliDistribution_apply (q : ℕ) (P : ℚ[X]) :
    bernoulliDistribution q P =
      (q : ℚ)⁻¹ * ∑ c ∈ range q,
        bernoulliFunctional (P.comp (localAffine q (c : ℤ))) := by
  simp only [bernoulliDistribution, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← comp_eq_aeval, smul_eq_mul]

theorem localAffine_shift (q c : ℕ) :
    (X + 1 : ℚ[X]).comp (localAffine q (c : ℤ)) = localAffine q ((c + 1 : ℕ) : ℤ) := by
  simp only [localAffine, add_comp, X_comp, one_comp, Nat.cast_add, Nat.cast_one,
    Int.cast_add, Int.cast_one, Int.cast_natCast]
  simp only [map_add, map_one]
  ring

theorem bernoulliDistribution_difference (q : ℕ) (hq : 0 < q) (P : ℚ[X]) :
    bernoulliDistribution q (P.comp (X + 1) - P) = P.derivative.eval 0 := by
  rw [bernoulliDistribution_apply]
  simp only [sub_comp, comp_assoc, localAffine_shift, map_sub]
  have htel := Finset.sum_range_sub
    (fun c : ℕ => bernoulliFunctional (P.comp (localAffine q (c : ℤ)))) q
  rw [htel]
  have he : (P.comp (C (q : ℚ) * X)).comp (X + 1) =
      P.comp (localAffine q (q : ℤ)) := by
    rw [comp_assoc]
    congr 1
    simp only [mul_comp, C_comp, X_comp, localAffine, Int.cast_natCast]
    ring
  have he0 : localAffine q (0 : ℤ) = C (q : ℚ) * X := by simp [localAffine]
  simp only [Nat.cast_zero]
  rw [he0, ← he, ← map_sub, bernoulliFunctional_difference]
  rw [derivative_comp]
  simp only [eval_mul, eval_comp, eval_C, eval_X, mul_zero, derivative_mul,
    derivative_C, derivative_X, zero_mul, mul_one, zero_add]
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

theorem bernoulliDistribution_eq (q : ℕ) (hq : 0 < q) :
    bernoulliDistribution q = bernoulliFunctional :=
  bernoulliFunctional_unique _ (bernoulliDistribution_difference q hq)

/-- Exact distribution identity over q residue classes. -/
theorem bernoulliFunctional_distribution (q : ℕ) (hq : 0 < q) (P : ℚ[X]) :
    bernoulliFunctional P = (1 / (q : ℚ)) * ∑ c ∈ range q,
      bernoulliFunctional (P.comp (localAffine q (c : ℤ))) := by
  calc
    _ = bernoulliDistribution q P := congrArg (fun L : ℚ[X] →ₗ[ℚ] ℚ => L P)
      (bernoulliDistribution_eq q hq).symm
    _ = _ := by rw [bernoulliDistribution_apply, one_div]

end Zeta5.Arithmetic
