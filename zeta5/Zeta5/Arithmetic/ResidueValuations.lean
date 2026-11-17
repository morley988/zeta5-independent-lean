import Zeta5.Construction.ResidueDerivative
import Zeta5.Construction.ResidueDecomposition
import Zeta5.Arithmetic.LocalNewton
import Zeta5.Arithmetic.StieltjesValuations
import Zeta5.Arithmetic.EvaluationMinors

/-! Exact factorial valuations of the denominator derivative and the
actual common-root gains in every residue weight. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem denominator_derivative_valuation (N i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hiN : i ≤ N) (hsmall : N + i < p ^ 2) :
    padicValRat p ((denominator N).derivative.eval (pole i)) =
      ((N - i) / p : ℕ) + ((N + i) / p : ℕ) - 2 * (padicValNat p i : ℤ) := by
  have h1 : (Nat.factorial (N - i) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - i)
  have h2 : (Nat.factorial (N + i) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + i)
  have hsign : (-1 : ℚ) ^ (i - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hiQ : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
  have htwo : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd
    (fun h => (not_le_of_gt hp) (Nat.le_of_dvd (by omega) h))
  have htwoQ : padicValRat p (2 : ℚ) = 0 :=
    (padicValRat.of_nat (p := p) (n := 2)).trans (by exact_mod_cast htwo)
  rw [denominator_derivative_pole N i hi hiN,
    padicValRat.div (mul_ne_zero (mul_ne_zero hsign h1) h2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hiQ)),
    padicValRat.mul (mul_ne_zero hsign h1) h2, padicValRat.mul hsign h1,
    padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (pow_ne_zero 2 hiQ)]
  simp only [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero,
    zero_add, padicValRat.of_nat, htwoQ, Nat.cast_zero]
  rw [factorial_padicVal_of_lt_sq (by omega : N - i < p ^ 2),
    factorial_padicVal_of_lt_sq hsmall]
  ring

theorem commonFactor_eval_sq_eq_integer (m i : ℕ) :
    ((commonFactor m).eval (pole i)) ^ 2 =
      (((commonRootInt m).eval (-((i : ℤ) ^ 2)) : ℤ) : ℚ) ^ 2 := by
  have h := congrArg (fun P : ℚ[X] => P.eval (pole i)) (commonRootInt_map_square m)
  rw [eval_pow, eval_pow] at h
  change _ = ((commonFactor m).eval (pole i)) ^ 2 at h
  rw [← h]
  congr 1
  have he : pole i = (Int.castRingHom ℚ) (-((i : ℤ) ^ 2)) := by simp [pole]
  rw [he, eval_map_apply]
  rfl

theorem commonFactor_eval_sq_integral (m i : ℕ) :
    PadicLower p 0 (((commonFactor m).eval (pole i)) ^ 2) := by
  rw [commonFactor_eval_sq_eq_integer]
  have h := padicLower_int (p := p) ((commonRootInt m).eval (-((i : ℤ) ^ 2)))
  simpa only [pow_two, zero_add] using h.mul h

theorem commonRootInt_eval_dvd {m c i : ℕ} (hc : c < m)
    (hcongr : (p : ℤ) ∣ (c : ℤ) ^ 2 - (i : ℤ) ^ 2) :
    (p : ℤ) ∣ (commonRootInt m).eval (-((i : ℤ) ^ 2)) := by
  rw [commonRootInt, eval_prod]
  apply hcongr.trans
  have h := Finset.dvd_prod_of_mem (fun a : ℕ =>
    (X + C ((a : ℤ) ^ 2) : ℤ[X]).eval (-((i : ℤ) ^ 2))) (Finset.mem_range.mpr hc)
  simpa only [eval_add, eval_X, eval_C, sub_eq_add_neg, add_comm] using h

theorem commonFactor_eval_sq_gain {m c i : ℕ} (hc : c < m)
    (hcongr : (p : ℤ) ∣ (c : ℤ) ^ 2 - (i : ℤ) ^ 2) :
    PadicLower p 2 (((commonFactor m).eval (pole i)) ^ 2) := by
  rw [commonFactor_eval_sq_eq_integer]
  have h := padicLower_int_of_dvd (p := p) _ (commonRootInt_eval_dvd hc hcongr)
  simpa only [pow_two, show (1 : ℤ) + 1 = 2 from rfl] using h.mul h

theorem monomialAtomWeight_bound (N m i : ℕ) (gain cost v : ℤ)
    (hroot : PadicLower p gain (((commonFactor m).eval (pole i)) ^ 2))
    (hkernel : PolynomialPadicLower p cost (stieltjes i))
    (hden : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ v) :
    PolynomialPadicLower p (gain - v + cost) (monomialAtomWeight N m i) := by
  have hinv : PadicLower p (-v) (((denominator N).derivative.eval (pole i))⁻¹) := by
    right
    rw [padicValRat.inv]
    exact neg_le_neg hden
  have hscalar := hroot.mul hinv
  simpa only [monomialAtomWeight, div_eq_mul_inv, sub_eq_add_neg] using
    (PolynomialPadicLower.constant hscalar).mul hkernel

#print axioms denominator_derivative_valuation
#print axioms commonFactor_eval_sq_gain
#print axioms monomialAtomWeight_bound

end Zeta5.Arithmetic
