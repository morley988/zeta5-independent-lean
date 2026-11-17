import Zeta5.Construction.Determinant
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FieldSimp

/-!
# Exact partial fractions at the square nodes

The rational expressions used to define the pencil are justified by
polynomial division and Lagrange interpolation. These lemmas are algebraic;
the positive-measure integral identities remain separate analytic results.
-/

noncomputable section
namespace Zeta5.Construction
open Polynomial
open scoped BigOperators

section General
variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

theorem partialFraction_polynomial_identity (s : Finset ι) (v : ι → K)
    (hv : Set.InjOn v s) (f : K[X]) :
    f = (f / Lagrange.nodal s v) * Lagrange.nodal s v +
      ∑ i ∈ s, C (f.eval (v i) / (Lagrange.nodal s v).derivative.eval (v i)) *
        (Lagrange.nodal s v / (X - C (v i))) := by
  let D := Lagrange.nodal s v
  have hrem : f %ₘ D = Lagrange.interpolate s v (fun i => f.eval (v i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq (s := s) (v := v)
      (f := f %ₘ D) (r := fun i => f.eval (v i)) hv
    · simpa only [Lagrange.degree_nodal] using
        degree_modByMonic_lt f (Lagrange.nodal_monic (s := s) (v := v))
    · intro i hi
      have hvD : D.eval (v i) = 0 := Lagrange.eval_nodal_at_node hi
      have hev := congrArg (Polynomial.eval (v i)) (modByMonic_add_div f D)
      simpa only [eval_add, eval_mul, hvD, zero_mul, add_zero] using hev
  have hinterp := Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C
    (s := s) (v := v) (fun i => f.eval (v i))
  have hsum : Lagrange.interpolate s v (fun i => f.eval (v i)) =
      ∑ i ∈ s, C (f.eval (v i) / D.derivative.eval (v i)) * (D / (X - C (v i))) := by
    rw [hinterp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi]
    simp only [div_eq_mul_inv, map_mul]
    dsimp [D]
    ring
  calc
    f = f %ₘ D + D * (f /ₘ D) := (modByMonic_add_div f D).symm
    _ = Lagrange.interpolate s v (fun i => f.eval (v i)) + D * (f / D) := by
      rw [hrem, divByMonic_eq_div f (Lagrange.nodal_monic (s := s) (v := v))]
    _ = (f / D) * D +
        ∑ i ∈ s, C (f.eval (v i) / D.derivative.eval (v i)) * (D / (X - C (v i))) := by
      rw [hsum]
      ring

theorem partialFraction_evaluation (s : Finset ι) (v : ι → K)
    (hv : Set.InjOn v s) (f : K[X]) (x : K) (hx : ∀ i ∈ s, x ≠ v i) :
    f.eval x / (Lagrange.nodal s v).eval x = (f / Lagrange.nodal s v).eval x +
      ∑ i ∈ s, (f.eval (v i) / (Lagrange.nodal s v).derivative.eval (v i)) / (x - v i) := by
  let D := Lagrange.nodal s v
  have hD : D.eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  have hprod (i : ι) (hi : i ∈ s) :
      (D / (X - C (v i))).eval x = D.eval x / (x - v i) := by
    rw [← Lagrange.nodal_erase_eq_nodal_div hi]
    apply (eq_div_iff (sub_ne_zero.mpr (hx i hi))).mpr
    change _ = (Lagrange.nodal s v).eval x
    rw [Lagrange.nodal_eq_mul_nodal_erase (s := s) hi]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    ring
  have he := congrArg (Polynomial.eval x) (partialFraction_polynomial_identity s v hv f)
  simp only [eval_add, eval_mul, eval_C, eval_finsetSum] at he
  change f.eval x = (f / D).eval x * D.eval x + _ at he
  rw [he, add_div, mul_div_cancel_right₀ _ hD, Finset.sum_div]
  apply congrArg ((f / D).eval x + ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [hprod i hi]
  change (_ * (D.eval x / (x - v i))) / D.eval x = _
  simp only [div_eq_mul_inv]
  calc
    _ = (f.eval (v i) * (D.derivative.eval (v i))⁻¹ * (x - v i)⁻¹) *
        (D.eval x * (D.eval x)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hD, mul_one]

end General

theorem squarePole_injective : Function.Injective (fun i : ℕ => pole (i + 1)) := by
  intro i j h
  have hs : (((i + 1 : ℕ) : ℚ) ^ 2) = (((j + 1 : ℕ) : ℚ) ^ 2) := by
    simpa [pole] using h
  have he : ((i + 1 : ℕ) : ℚ) = ((j + 1 : ℕ) : ℚ) :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hs
  exact Nat.succ.inj (by exact_mod_cast he)

theorem denominator_eq_nodal (N : ℕ) :
    denominator N = Lagrange.nodal (Finset.range N) (fun i => pole (i + 1)) := by
  unfold denominator Lagrange.nodal
  apply Finset.prod_congr rfl
  intro i hi
  simp [pole]

theorem denominator_derivative_at_pole_ne_zero {N i : ℕ} (hi : i < N) :
    (denominator N).derivative.eval (pole (i + 1)) ≠ 0 := by
  rw [denominator_eq_nodal]
  have hw := Lagrange.nodalWeight_ne_zero squarePole_injective.injOn (Finset.mem_range.mpr hi)
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_range.mpr hi)] at hw
  intro hz
  rw [hz, inv_zero] at hw
  exact hw rfl

theorem squareNode_partialFraction_identity (N : ℕ) (f : ℚ[X]) :
    f = (f / denominator N) * denominator N +
      ∑ i ∈ Finset.range N,
        C (f.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
          (denominator N / (X - C (pole (i + 1)))) := by
  simpa only [← denominator_eq_nodal] using
    partialFraction_polynomial_identity (Finset.range N) (fun i => pole (i + 1))
      squarePole_injective.injOn f

#print axioms squareNode_partialFraction_identity

end Zeta5.Construction
