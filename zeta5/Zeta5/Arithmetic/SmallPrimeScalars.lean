import Zeta5.Arithmetic.BernoulliMoments
import Zeta5.Arithmetic.CentralIntegerValued
import Zeta5.Construction.ResidueDerivative

/-!
# Logarithmic all-prime losses for binomial and factorial scalars

Kummer's theorem bounds a binomial valuation by the number of available
base-p digits.  The exact factorial ratios used by the small-prime argument
therefore cost only logarithmically many powers of p.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

theorem padicValNat_choose_le_log {a b : ℕ} (hba : b ≤ a) :
    padicValNat p (a.choose b) ≤ Nat.log p a := by
  rw [padicValNat_choose hba (Nat.lt_succ_self (Nat.log p a))]
  apply (card_filter_le _ _).trans
  simp

theorem inverse_nat_padicLower_log {a D : ℕ} (haD : a ≤ D) :
    PadicLower p (-(Nat.log p D : ℤ)) ((a : ℚ)⁻¹) := by
  right
  rw [padicValRat.inv, padicValRat.of_nat]
  exact neg_le_neg (by exact_mod_cast
    (padicValNat_le_nat_log a).trans (Nat.log_mono_right haD))

theorem inverse_choose_padicLower_log {a b D : ℕ} (hba : b ≤ a) (haD : a ≤ D) :
    PadicLower p (-(Nat.log p D : ℤ)) ((a.choose b : ℚ)⁻¹) := by
  right
  rw [padicValRat.inv, padicValRat.of_nat]
  exact neg_le_neg (by exact_mod_cast
    (padicValNat_choose_le_log (p := p) hba).trans (Nat.log_mono_right haD))

lemma factorialRatio_eq_choose (N i : ℕ) (hiN : i ≤ N) :
    (Nat.factorial N : ℚ)^2/
      ((Nat.factorial (N-i) : ℚ)*(Nat.factorial (N+i) : ℚ)) =
        ((2*N).choose (N-i) : ℚ)/((2*N).choose N : ℚ) := by
  have h1 : ((2*N).choose (N-i) : ℚ)*(Nat.factorial (N-i) : ℚ)*
      (Nat.factorial (N+i) : ℚ) = (Nat.factorial (2*N) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show N-i ≤ 2*N by omega)
    rw [show 2*N-(N-i) = N+i by omega] at h
    exact_mod_cast h
  have h2 : ((2*N).choose N : ℚ)*(Nat.factorial N : ℚ)*(Nat.factorial N : ℚ) =
      (Nat.factorial (2*N) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2*N by omega)
    rw [show 2*N-N = N by omega] at h
    exact_mod_cast h
  have hc : ((2*N).choose N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show N ≤ 2*N by omega)
  apply (div_eq_div_iff (by positivity) hc).mpr
  nlinarith [h1, h2]

theorem factorialRatio_padicLower_log (N i D : ℕ) (hiN : i ≤ N) (hND : 2*N ≤ D) :
    PadicLower p (-(Nat.log p D : ℤ))
      ((Nat.factorial N : ℚ)^2/
        ((Nat.factorial (N-i) : ℚ)*(Nat.factorial (N+i) : ℚ))) := by
  rw [factorialRatio_eq_choose N i hiN, div_eq_mul_inv]
  simpa using (padicLower_nat (p := p) ((2*N).choose (N-i))).mul
    (inverse_choose_padicLower_log (p := p) (by omega : N ≤ 2*N) hND)

def centralQuotientScalar (N k : ℕ) : ℚ :=
  (Nat.factorial N : ℚ)^2*(Nat.factorial k : ℚ)^2/
    (Nat.factorial (2*(N+k+1)) : ℚ)

lemma centralQuotientScalar_identity (N k : ℕ) :
    centralQuotientScalar N k =
      1/(((N+k+1 : ℕ) : ℚ)^2*((2*(N+k+1)).choose (N+k+1) : ℚ)*
        ((N+k).choose N : ℚ)^2) := by
  have h1 : ((2*(N+k+1)).choose (N+k+1) : ℚ)*
      (Nat.factorial (N+k+1) : ℚ)*(Nat.factorial (N+k+1) : ℚ) =
        (Nat.factorial (2*(N+k+1)) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (show N+k+1 ≤ 2*(N+k+1) by omega)
    rw [show 2*(N+k+1)-(N+k+1) = N+k+1 by omega] at h
    exact_mod_cast h
  have h2 : ((N+k).choose N : ℚ)*(Nat.factorial N : ℚ)*(Nat.factorial k : ℚ) =
      (Nat.factorial (N+k) : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show N ≤ N+k by omega)
    rw [show N+k-N = k by omega] at h
    exact_mod_cast h
  have h3 : (Nat.factorial (N+k+1) : ℚ) =
      ((N+k+1 : ℕ) : ℚ)*(Nat.factorial (N+k) : ℚ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  rw [centralQuotientScalar, ← h1, h3, ← h2]
  have hc1 : ((2*(N+k+1)).choose (N+k+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show N+k+1 ≤ 2*(N+k+1) by omega)
  have hc2 : ((N+k).choose N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show N ≤ N+k by omega)
  have hN : (Nat.factorial N : ℚ) ≠ 0 := by positivity
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have hl : ((N+k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

theorem centralQuotientScalar_padicLower_log (N k D : ℕ) (hD : 2*(N+k+1) ≤ D) :
    PadicLower p (-5*(Nat.log p D : ℤ)) (centralQuotientScalar N k) := by
  have hl := inverse_nat_padicLower_log (p := p) (by omega : N+k+1 ≤ D)
  have hc1 := inverse_choose_padicLower_log (p := p)
    (by omega : N+k+1 ≤ 2*(N+k+1)) hD
  have hc2 := inverse_choose_padicLower_log (p := p) (by omega : N ≤ N+k)
    (by omega : N+k ≤ D)
  have h := ((hl.mul hl).mul hc1).mul (hc2.mul hc2)
  convert! h using 1
  · ring
  · rw [centralQuotientScalar_identity]
    simp only [one_div, mul_inv_rev, inv_pow]
    ring

end Zeta5.Arithmetic
