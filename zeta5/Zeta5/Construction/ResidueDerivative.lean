import Zeta5.Construction.PartialFractions
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Exact derivative of the squared-node denominator at every physical
pole. This identity controls both small-prime and large-prime residues. -/

noncomputable section
namespace Zeta5.Construction
open Polynomial

theorem denominator_succ (N : ℕ) :
    denominator (N + 1) = denominator N * (X + C (((N + 1 : ℕ) : ℚ) ^ 2)) := by
  exact Finset.prod_range_succ _ N

theorem denominator_next_eval (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * (denominator n).eval (pole (n + 1)) =
      (-1 : ℚ) ^ n * (Nat.factorial (2 * n + 1) : ℚ) := by
  have he : (denominator n).eval (pole (n + 1)) =
      (-1 : ℚ) ^ n * (Nat.factorial n : ℚ) * ((n + 2).ascFactorial n : ℚ) := by
    rw [denominator, eval_prod]
    have hf : ∀ i ∈ Finset.range n,
        (X + C (((i + 1 : ℕ) : ℚ) ^ 2)).eval (pole (n + 1)) =
          (-1 : ℚ) * ((n : ℚ) - i) * ((n : ℚ) + 2 + i) := by
      intro i hi
      simp only [eval_add, eval_X, eval_C, pole, Nat.cast_add, Nat.cast_one]
      ring
    rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_range, Finset.prod_range_natCast_sub,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
    congr 1
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    push_cast
    ring
  rw [he]
  have hfac : ((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ) *
      ((n + 2).ascFactorial n : ℚ) = (Nat.factorial (2 * n + 1) : ℚ) := by
    have h := Nat.factorial_mul_ascFactorial (n + 1) n
    rw [Nat.factorial_succ] at h
    have heq : n + 1 + n = 2 * n + 1 := by omega
    rw [heq] at h
    exact_mod_cast h
  calc
    _ = (-1 : ℚ) ^ n * (((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ) *
        ((n + 2).ascFactorial n : ℚ)) := by ring
    _ = _ := by rw [hfac]

theorem denominator_derivative_pole_mul (N i : ℕ) (hi : 0 < i) (hiN : i ≤ N) :
    2 * (i : ℚ) ^ 2 * (denominator N).derivative.eval (pole i) =
      (-1 : ℚ) ^ (i - 1) * (Nat.factorial (N - i) : ℚ) * (Nat.factorial (N + i) : ℚ) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [denominator_succ, derivative_mul, eval_add, eval_mul, eval_mul,
      derivative_X_add_C, eval_one, mul_one]
    by_cases hilast : i = N + 1
    · subst i
      have hz : (X + C (((N + 1 : ℕ) : ℚ) ^ 2)).eval (pole (N + 1)) = 0 := by
        simp [pole]
      rw [hz, mul_zero, zero_add]
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      have h := denominator_next_eval N
      have hfac : (Nat.factorial (N + 1 + (N + 1)) : ℚ) =
          (2 * ((N + 1 : ℕ) : ℚ)) * (Nat.factorial (2 * N + 1) : ℚ) := by
        rw [show N + 1 + (N + 1) = (2 * N + 1) + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      calc
        _ = 2 * ((N + 1 : ℕ) : ℚ) *
            (((N + 1 : ℕ) : ℚ) * (denominator N).eval (pole (N + 1))) := by ring
        _ = _ := by rw [h]; ring
    · have hiN' : i ≤ N := by omega
      have hz : (denominator N).eval (pole i) = 0 := by
        simpa only [pole] using denominator_eval_neg_square_eq_zero hi hiN'
      rw [hz, add_zero]
      have h := ih hiN'
      have hfactor : (X + C (((N + 1 : ℕ) : ℚ) ^ 2)).eval (pole i) =
          ((N + 1 - i : ℕ) : ℚ) * ((N + i + 1 : ℕ) : ℚ) := by
        simp only [eval_add, eval_X, eval_C, pole]
        rw [Nat.cast_sub (by omega : i ≤ N + 1)]
        push_cast
        ring
      rw [hfactor, ← mul_assoc, h]
      have hsub : N + 1 - i = (N - i) + 1 := by omega
      rw [hsub, show N + 1 + i = (N + i) + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring

theorem denominator_derivative_pole (N i : ℕ) (hi : 0 < i) (hiN : i ≤ N) :
    (denominator N).derivative.eval (pole i) =
      (-1 : ℚ) ^ (i - 1) * (Nat.factorial (N - i) : ℚ) * (Nat.factorial (N + i) : ℚ) /
        (2 * (i : ℚ) ^ 2) := by
  apply (eq_div_iff (by positivity : (2 : ℚ) * (i : ℚ) ^ 2 ≠ 0)).mpr
  simpa only [mul_comm] using denominator_derivative_pole_mul N i hi hiN

#print axioms denominator_derivative_pole

end Zeta5.Construction
