import Zeta5.Arithmetic.PadicCongruences
import Mathlib.Algebra.BigOperators.Intervals

/-! Reflection of the actual Stieltjes polynomial modulo a good prime.
The odd reciprocal-power cancellation is proved by finite reflection of
the middle interval, with no appeal to a computational certificate. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Finset
variable {p : ℕ} [Fact p.Prime]

theorem reciprocal_reflection (i : ℕ) (hi : 0 < i) (hip : i < p) :
    PadicLower p 1 ((i : ℚ)⁻¹ + ((p - i : ℕ) : ℚ)⁻¹) := by
  have hj : 0 < p - i := by omega
  have hjp : p - i < p := by omega
  have hpi : PadicLower p 1 ((i : ℚ) + ((p - i : ℕ) : ℚ)) := by
    rw [Nat.cast_sub hip.le]
    have hp' : PadicLower p 1 (p : ℚ) := by
      right
      rw [padicValRat.self (Fact.out : p.Prime).one_lt]
    convert hp' using 1 <;> ring
  apply padicLower_inv_add_inv (by exact_mod_cast (Nat.ne_of_gt hi))
    (by exact_mod_cast (Nat.ne_of_gt hj))
  · simpa using reciprocalPower_integral (p := p) i 1 hip
  · simpa using reciprocalPower_integral (p := p) (p - i) 1 hjp
  · exact hpi

theorem reciprocalFive_reflection (i : ℕ) (hi : 0 < i) (hip : i < p) :
    PadicLower p 1 (1 / (i : ℚ) ^ 5 + 1 / ((p - i : ℕ) : ℚ) ^ 5) := by
  have hxi : PadicLower p 0 (i : ℚ)⁻¹ := by
    simpa using reciprocalPower_integral (p := p) i 1 hip
  have hyi : PadicLower p 0 (((p - i : ℕ) : ℚ)⁻¹) := by
    simpa using reciprocalPower_integral (p := p) (p - i) 1 (by omega)
  have h := padicLower_pow_sub_pow hxi hyi.neg
    (by simpa using reciprocal_reflection (p := p) i hi hip) 5
  simpa only [neg_pow, show (-1 : ℚ) ^ 5 = -1 by norm_num, neg_one_mul,
    sub_neg_eq_add, one_div, inv_pow] using h

theorem harmonicFive_Ico (n : ℕ) :
    harmonicFive n = ∑ i ∈ Ico 1 (n + 1), 1 / (i : ℚ) ^ 5 := by
  rw [sum_Ico_eq_sum_range]
  simp [harmonicFive, Nat.add_comm]

theorem harmonicFive_succ (n : ℕ) :
    harmonicFive (n + 1) = harmonicFive n + 1 / ((n + 1 : ℕ) : ℚ) ^ 5 := by
  simp only [harmonicFive, sum_range_succ]

theorem middle_harmonic_reflection (i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hip : 2 * i < p) :
    PadicLower p 1 (∑ j ∈ Ico (i + 1) (p - i), 1 / (j : ℚ) ^ 5) := by
  let f : ℕ → ℚ := fun j => 1 / (j : ℚ) ^ 5
  let T : ℚ := ∑ j ∈ Ico (i + 1) (p - i), f j
  have hr : (∑ j ∈ Ico (i + 1) (p - i), f (p - j)) = T := by
    rw [sum_Ico_reflect f (i + 1) (m := p - i) (n := p) (by omega)]
    have h1 : p + 1 - (p - i) = i + 1 := by omega
    have h2 : p + 1 - (i + 1) = p - i := by omega
    rw [h1, h2]
  have hs : PadicLower p 1 (T + T) := by
    have he : T + T = ∑ j ∈ Ico (i + 1) (p - i), (f j + f (p - j)) := by
      rw [sum_add_distrib, hr]
    rw [he]
    apply padicLower_sum
    intro j hj
    have hj' := mem_Ico.mp hj
    exact reciprocalFive_reflection j (by omega) (by omega)
  have h := hs.mul (half_integral (p := p) hp)
  have he : (T + T) * (1 / 2 : ℚ) = T := by ring
  simpa only [add_zero, he] using h

theorem harmonicFive_reflection (i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hip : 2 * i < p) :
    PadicLower p 1
      (harmonicFive (p - i - 1) - (harmonicFive (i - 1) + 1 / (i : ℚ) ^ 5)) := by
  have hs := sum_Ico_consecutive (fun j : ℕ => 1 / (j : ℚ) ^ 5)
    (m := 1) (n := i + 1) (k := p - i) (by omega) (by omega)
  have hj : p - i - 1 + 1 = p - i := by omega
  have hi' : i - 1 + 1 = i := by omega
  rw [← harmonicFive_Ico i, ← hj, ← harmonicFive_Ico (p - i - 1)] at hs
  rw [hj] at hs
  have hrec := harmonicFive_succ (i - 1)
  rw [hi'] at hrec
  have he : harmonicFive (p - i - 1) -
      (harmonicFive (i - 1) + 1 / (i : ℚ) ^ 5) =
      ∑ j ∈ Ico (i + 1) (p - i), 1 / (j : ℚ) ^ 5 := by linarith
  rw [he]
  exact middle_harmonic_reflection i hp hi hip

theorem reflected_fourth_power (i : ℕ) (hi : 0 < i) (hip : i < p) :
    PadicLower p 1 ((((p - i : ℕ) : ℚ) ^ 4) - (i : ℚ) ^ 4) := by
  have hxi : PadicLower p 0 ((p - i : ℕ) : ℚ) := by
    simpa using padicLower_int (p := p) ((p - i : ℕ) : ℤ)
  have hyi : PadicLower p 0 (i : ℚ) := by
    simpa using padicLower_int (p := p) (i : ℤ)
  have hbase : PadicLower p 1 (((p - i : ℕ) : ℚ) - (-(i : ℚ))) := by
    rw [Nat.cast_sub hip.le]
    have hp' : PadicLower p 1 (p : ℚ) := by
      right
      rw [padicValRat.self (Fact.out : p.Prime).one_lt]
    convert hp' using 1 <;> ring
  have h := padicLower_pow_sub_pow hxi hyi.neg hbase 4
  simpa only [neg_pow, show (-1 : ℚ) ^ 4 = 1 by norm_num, one_mul] using h

theorem stieltjesConstant_reflection (i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hip : 2 * i < p) :
    PadicLower p 1 (stieltjesConstant (p - i) - stieltjesConstant i) := by
  have hip' : i < p := by omega
  have hj : 0 < p - i := by omega
  have hjp : p - i < p := by omega
  have hiQ : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
  have hjQ : ((p - i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hji : PadicLower p 0 ((p - i : ℕ) : ℚ) := by
    simpa using padicLower_int (p := p) ((p - i : ℕ) : ℤ)
  have hH : PadicLower p 0 (harmonicFive (i - 1) + 1 / (i : ℚ) ^ 5) :=
    (harmonicFive_integral (p := p) (i - 1) (by omega)).add
      (reciprocalPower_integral (p := p) i 5 hip')
  have hprod := padicLower_mul_sub_mul (padicIntegral_pow hji 4) hH
    (reflected_fourth_power (p := p) i hi hip') (harmonicFive_reflection i hp hi hip)
  have hhalf := (reciprocal_reflection (p := p) i hi hip').mul (half_integral (p := p) hp)
  have h := hprod.neg.add hhalf.neg
  have he : stieltjesConstant (p - i) - stieltjesConstant i =
      -((((p - i : ℕ) : ℚ) ^ 4) * harmonicFive (p - i - 1) -
        (i : ℚ) ^ 4 * (harmonicFive (i - 1) + 1 / (i : ℚ) ^ 5)) +
      -(((i : ℚ)⁻¹ + ((p - i : ℕ) : ℚ)⁻¹) * (1 / 2)) := by
    unfold stieltjesConstant
    field_simp
    ring
  rw [he]
  simpa using h

theorem stieltjes_reflection (i : ℕ) (hp : 2 < p)
    (hi : 0 < i) (hip : 2 * i < p) :
    PolynomialPadicLower p 1 (stieltjes (p - i) - stieltjes i) := by
  have hconst := PolynomialPadicLower.constant (stieltjesConstant_reflection i hp hi hip)
  have hlinear := (polynomialPadicLower_X (p := p)).mul
    (PolynomialPadicLower.constant (reflected_fourth_power (p := p) i hi (by omega)))
  have h := hconst.add hlinear
  convert h using 1 <;> simp only [stieltjes, map_sub] <;> ring

#print axioms reciprocalFive_reflection
#print axioms harmonicFive_reflection
#print axioms stieltjes_reflection

end Zeta5.Arithmetic
