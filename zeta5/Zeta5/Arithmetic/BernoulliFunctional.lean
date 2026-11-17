import Zeta5.Arithmetic.Newton
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Bernoulli evaluation and the Newton basis

The functional is defined coefficientwise. Its finite difference identity
follows from Mathlib's Bernoulli recurrence. This provides an algebraic proof
of its value on every binomial polynomial, without formal power series.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue

def bernoulliFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun n => LinearMap.mulRight ℚ (_root_.bernoulli n))

@[simp] theorem bernoulliFunctional_monomial (n : ℕ) (a : ℚ) :
    bernoulliFunctional (monomial n a) = a * _root_.bernoulli n := by
  simp [bernoulliFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

@[simp] theorem bernoulliFunctional_X_pow (n : ℕ) :
    bernoulliFunctional ((X : ℚ[X]) ^ n) = _root_.bernoulli n := by
  simpa only [monomial_one_right_eq_X_pow, one_mul] using bernoulliFunctional_monomial n 1

@[simp] theorem bernoulliFunctional_C (a : ℚ) : bernoulliFunctional (C a) = a := by
  simpa only [monomial_zero_left, bernoulli_zero, mul_one] using bernoulliFunctional_monomial 0 a

@[simp] theorem bernoulliFunctional_C_mul (a : ℚ) (P : ℚ[X]) :
    bernoulliFunctional (C a * P) = a * bernoulliFunctional P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem bernoulliFunctional_shift_pow (n : ℕ) :
    bernoulliFunctional ((X + 1 : ℚ[X]) ^ n) =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * _root_.bernoulli k := by
  rw [add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  rw [mul_comm, ← C_eq_natCast, bernoulliFunctional_C_mul, bernoulliFunctional_X_pow]

/-- Bernoulli evaluation of a finite difference is the derivative at zero. -/
theorem bernoulliFunctional_difference (P : ℚ[X]) :
    bernoulliFunctional (P.comp (X + 1) - P) = P.derivative.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, add_sub_add_comm, map_add, hP, hQ, derivative_add, eval_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp,
      map_sub, bernoulliFunctional_C_mul, bernoulliFunctional_C_mul,
      bernoulliFunctional_shift_pow, bernoulliFunctional_X_pow, sum_range_succ,
      Nat.choose_self, Nat.cast_one, one_mul, _root_.sum_bernoulli]
    rw [derivative_C_mul_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    by_cases hn : n = 1
    · subst n; norm_num; ring
    · rw [if_neg hn]
      cases n with
      | zero => simp
      | succ n =>
        have hn0 : n ≠ 0 := by omega
        simp [Nat.add_sub_cancel, zero_pow hn0]

theorem binomialPolynomial_shift (n : ℕ) :
    (binomialPolynomial (n + 1)).comp (X + 1) =
      binomialPolynomial (n + 1) + binomialPolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨k, rfl⟩
  simp only [Set.mem_setOf_eq, eval_comp, eval_add, eval_X, eval_one]
  rw [← Nat.cast_add_one, binomialPolynomial_eval_nat, binomialPolynomial_eval_nat,
    binomialPolynomial_eval_nat]
  rw [Nat.choose_succ_succ]
  push_cast
  ring

theorem binomialPolynomial_mul_X (n : ℕ) :
    X * binomialPolynomial n =
      C (n + 1 : ℚ) * binomialPolynomial (n + 1) + C (n : ℚ) * binomialPolynomial n := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : (n + 1 : ℚ) ≠ 0 := by positivity
  unfold binomialPolynomial
  rw [descPochhammer_succ_right, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev, map_mul]
  rw [show (n : ℚ[X]) = C (n : ℚ) by simp]
  calc
    _ = (C (n + 1 : ℚ) * C ((n + 1 : ℚ)⁻¹)) *
          (C ((n.factorial : ℚ)⁻¹) * descPochhammer ℚ n * (X - C (n : ℚ))) +
        C (n : ℚ) * (C ((n.factorial : ℚ)⁻¹) * descPochhammer ℚ n) := by
      rw [← map_mul, mul_inv_cancel₀ hn1, map_one]
      ring
    _ = _ := by ring

theorem binomialPolynomial_X_difference (n : ℕ) :
    (X * binomialPolynomial (n + 1)).comp (X + 1) - X * binomialPolynomial (n + 1) =
      C (n + 1 : ℚ) * binomialPolynomial n + C (n + 2 : ℚ) * binomialPolynomial (n + 1) := by
  rw [mul_comp, X_comp, binomialPolynomial_shift]
  have h := binomialPolynomial_mul_X n
  have hC : C (n + 2 : ℚ) = C (n + 1 : ℚ) + 1 := by
    rw [← map_one C, ← map_add]
    congr 1
    ring
  rw [hC]
  simp only [map_add, map_one] at h ⊢
  linear_combination h

/-- Exact Bernoulli evaluation on the Newton basis. -/
theorem bernoulliFunctional_binomialPolynomial (n : ℕ) :
    bernoulliFunctional (binomialPolynomial n) = (-1 : ℚ) ^ n / (n + 1) := by
  induction n with
  | zero =>
    simp only [binomialPolynomial, Nat.factorial_zero, Nat.cast_one, inv_one, map_one,
      descPochhammer_zero, mul_one, pow_zero, Nat.cast_zero, zero_add, div_one]
    exact bernoulliFunctional_C 1
  | succ n ih =>
    have h := bernoulliFunctional_difference (X * binomialPolynomial (n + 1))
    rw [binomialPolynomial_X_difference, map_add, bernoulliFunctional_C_mul,
      bernoulliFunctional_C_mul, derivative_mul, derivative_X, eval_add,
      eval_mul, eval_one, eval_mul, eval_X, zero_mul, add_zero, one_mul] at h
    have hz : (binomialPolynomial (n + 1)).eval (0 : ℚ) = 0 := by
      simpa using binomialPolynomial_eval_nat (n + 1) 0
    rw [hz, ih] at h
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℚ) ≠ 0 := by positivity
    have he : (n + 1 : ℚ) * ((-1 : ℚ) ^ n / (n + 1)) = (-1 : ℚ) ^ n := by
      field_simp
    rw [he] at h
    rw [Nat.cast_add, Nat.cast_one, show (n : ℚ) + 1 + 1 = n + 2 by ring, pow_succ]
    apply (eq_div_iff hn2).mpr
    linarith

/-- The finite difference identity uniquely determines the functional. -/
theorem bernoulliFunctional_unique (L : ℚ[X] →ₗ[ℚ] ℚ)
    (hL : ∀ P : ℚ[X], L (P.comp (X + 1) - P) = P.derivative.eval 0) :
    L = bernoulliFunctional := by
  have hb (n : ℕ) : L (binomialPolynomial n) = bernoulliFunctional (binomialPolynomial n) := by
    have h := (hL (binomialPolynomial (n + 1))).trans
      (bernoulliFunctional_difference (binomialPolynomial (n + 1))).symm
    simpa only [binomialPolynomial_shift, add_sub_cancel_left] using h
  apply LinearMap.ext
  intro P
  rw [← newtonExpansion_eq P le_rfl, newtonExpansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← smul_eq_C_mul, map_smul, map_smul, hb]

variable {p : ℕ} [Fact p.Prime]

/-- Evaluation on an integer-valued polynomial of degree at most L loses at
most log_p(L+1) powers of p. -/
theorem bernoulliFunctional_integerValuedAt_padicLower {P : ℚ[X]} {L : ℕ}
    (hP : IntegerValuedAt p P) (hL : P.natDegree ≤ L) :
    PadicLower p (-((Nat.log p (L + 1) : ℕ) : ℤ)) (bernoulliFunctional P) := by
  rw [← newtonExpansion_eq P hL, newtonExpansion, map_sum]
  apply padicLower_sum
  intro n hn
  rw [bernoulliFunctional_C_mul, bernoulliFunctional_binomialPolynomial, div_eq_mul_inv]
  have hr : PadicLower p (-((Nat.log p (L + 1) : ℕ) : ℤ)) ((n + 1 : ℚ)⁻¹) := by
    right
    rw [padicValRat.inv, ← Nat.cast_add_one, padicValRat.of_nat]
    have hv := (padicValNat_le_nat_log (p := p) (n + 1)).trans
      (Nat.log_mono_right (show n + 1 ≤ L + 1 by have := mem_range.mp hn; omega))
    exact neg_le_neg (by exact_mod_cast hv)
  have hs : PadicLower p 0 ((-1 : ℚ) ^ n) := by
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ n)
  simpa using (newtonCoefficient_padicLower hP n).mul (hs.mul hr)

end Zeta5.Arithmetic
