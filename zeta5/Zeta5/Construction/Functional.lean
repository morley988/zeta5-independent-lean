import Zeta5.Construction.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# The fixed-denominator functional

The partial-fraction prescription is a genuine rational-linear map on the
numerator polynomial.  Its target is the polynomial ring in the candidate
value of zeta(5).  This permits algebraic changes of polynomial basis before
any analytic identities are used.
-/

noncomputable section
namespace Zeta5.Construction
open Polynomial

def polynomialMomentMap : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun k => LinearMap.mulRight ℚ (rationalMoment k))

@[simp] theorem polynomialMomentMap_apply (P : ℚ[X]) :
    polynomialMomentMap P = polynomialMoment P := rfl

def monicQuotientMap (D : ℚ[X]) (hD : D.Monic) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun P := P /ₘ D
  map_add' P Q :=
    (div_modByMonic_unique (P /ₘ D + Q /ₘ D) _ hD
      ⟨by rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div,
          ← add_assoc, add_comm (D * _), modByMonic_add_div],
        (degree_add_le _ _).trans_lt
          (max_lt (degree_modByMonic_lt _ hD) (degree_modByMonic_lt _ hD))⟩).1
  map_smul' c P :=
    (div_modByMonic_unique (c • (P /ₘ D)) (c • (P %ₘ D)) hD
      ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
        (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hD)⟩).1

@[simp] theorem monicQuotientMap_apply (D : ℚ[X]) (hD : D.Monic) (P : ℚ[X]) :
    monicQuotientMap D hD P = P / D := divByMonic_eq_div P hD

def residueMap (N i : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  ((denominator N).derivative.eval (pole i))⁻¹ • (Polynomial.leval (pole i))

@[simp] theorem residueMap_apply (N i : ℕ) (P : ℚ[X]) :
    residueMap N i P = P.eval (pole i) / (denominator N).derivative.eval (pole i) := by
  simp [residueMap, div_eq_mul_inv, mul_comm]

/-- `J_X(P/D_N)`, with the denominator fixed by `N`. -/
def numeratorFunctional (N : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (Polynomial.CAlgHom : ℚ →ₐ[ℚ] ℚ[X]).toLinearMap.comp
      (polynomialMomentMap.comp (monicQuotientMap (denominator N) (denominator_monic N))) +
    ∑ i ∈ Finset.range N,
      (LinearMap.toSpanSingleton ℚ ℚ[X] (stieltjes (i + 1))).comp (residueMap N (i + 1))

theorem numeratorFunctional_apply (N : ℕ) (P : ℚ[X]) :
    numeratorFunctional N P = C (polynomialMoment (P / denominator N)) +
      ∑ i ∈ Finset.range N,
        C (P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1))) *
          stieltjes (i + 1) := by
  simp [numeratorFunctional, Polynomial.smul_eq_C_mul]

theorem entry_eq_numeratorFunctional (N j k : ℕ) :
    entry N j k = C ((Nat.factorial N : ℚ) ^ 2) *
      numeratorFunctional N (windowBasis j * windowBasis k) := by
  rw [numeratorFunctional_apply]
  simp only [entry, entryConstant, entryLinear, residueWeight, numerator,
    stieltjes, map_add, map_mul, map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  ring

end Zeta5.Construction
