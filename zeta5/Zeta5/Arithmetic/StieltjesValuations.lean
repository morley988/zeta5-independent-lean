import Zeta5.Reuse.PolynomialValuations

/-!
# Valuations of the actual affine Stieltjes terms

The elementary reciprocal-power estimates are reused from
`FourValueConcreteValuations.lean` (MIT, reference commit documented in
`Reuse/PadicMinors`). They are applied here to the actual fifth harmonic
sum and the actual polynomial `stieltjes i`.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem padicValNat_lt_square_le_one (m : ℕ) (hm : 0 < m) (hs : m < p ^ 2) :
    padicValNat p m ≤ 1 := by
  by_contra h
  have hd := pow_padicValNat_dvd (p := p) (n := m)
  have hd' : p ^ 2 ∣ m := (pow_dvd_pow p (by omega : 2 ≤ padicValNat p m)).trans hd
  exact (not_le_of_gt hs) (Nat.le_of_dvd hm hd')

theorem reciprocalPower_padicLower (m s : ℕ) (hm : 0 < m) (hs : m < p ^ 2) :
    PadicLower p (-(s : ℤ)) (1 / (m : ℚ) ^ s) := by
  right
  simp only [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have h := padicValNat_lt_square_le_one (p := p) m hm hs
  have hc : (padicValNat p m : ℤ) ≤ 1 := by exact_mod_cast h
  nlinarith

theorem reciprocalPower_integral (m s : ℕ) (hs : m < p) :
    PadicLower p 0 (1 / (m : ℚ) ^ s) := by
  by_cases hm : m = 0
  · subst m
    cases s <;> simp [PadicLower]
  · right
    have hv : padicValNat p m = 0 := padicValNat.eq_zero_of_not_dvd
      (fun h => (not_le_of_gt hs) (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h))
    simp [hv]

theorem harmonicFive_padicLower (n : ℕ) (hn : n < p ^ 2) :
    PadicLower p (-5) (harmonicFive n) := by
  unfold harmonicFive
  apply padicLower_sum
  intro k hk
  exact reciprocalPower_padicLower (k + 1) 5 (by omega)
    (lt_of_le_of_lt (by simpa using Finset.mem_range.mp hk) hn)

theorem harmonicFive_integral (n : ℕ) (hn : n < p) :
    PadicLower p 0 (harmonicFive n) := by
  unfold harmonicFive
  apply padicLower_sum
  intro k hk
  exact reciprocalPower_integral (k + 1) 5
    (lt_of_le_of_lt (by simpa using Finset.mem_range.mp hk) hn)

theorem half_integral (hp : 2 < p) : PadicLower p 0 (1 / 2 : ℚ) := by
  simpa using reciprocalPower_integral (p := p) 2 1 hp

theorem quarter_integral (hp : 2 < p) : PadicLower p 0 (1 / 4 : ℚ) := by
  have h := (half_integral (p := p) hp).mul (half_integral (p := p) hp)
  norm_num at h ⊢
  exact h

theorem reciprocalTwiceNat_padicLower (i : ℕ) (hp : 2 < p) (hi : 0 < i) (hi2 : i < p ^ 2) :
    PadicLower p (-1) (1 / (2 * (i : ℚ))) := by
  have h := (half_integral (p := p) hp).mul (reciprocalPower_padicLower i 1 hi hi2)
  convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem reciprocalTwiceNat_integral (i : ℕ) (hp : 2 < p) (hip : i < p) :
    PadicLower p 0 (1 / (2 * (i : ℚ))) := by
  have h := (half_integral (p := p) hp).mul (reciprocalPower_integral i 1 hip)
  convert h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem stieltjesConstant_padicLower (i : ℕ) (hp : 5 < p) (hi : 0 < i) (hi2 : i < p ^ 2) :
    PadicLower p (-5) (stieltjesConstant i) := by
  have hi4 : PadicLower p 0 ((i : ℚ) ^ 4) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := (hi4.neg).mul (harmonicFive_padicLower (i - 1) (by omega : i - 1 < p ^ 2))
  have hrecip := (reciprocalTwiceNat_padicLower i (by omega) hi hi2).mono (by omega : (-5 : ℤ) ≤ -1)
  have hquarter := (quarter_integral (p := p) (by omega)).mono (by omega : (-5 : ℤ) ≤ 0)
  simpa only [stieltjesConstant, sub_eq_add_neg, zero_add] using (hprod.add hrecip.neg).add hquarter.neg

theorem stieltjesConstant_integral (i : ℕ) (hp : 5 < p) (hip : i < p) :
    PadicLower p 0 (stieltjesConstant i) := by
  have hi4 : PadicLower p 0 ((i : ℚ) ^ 4) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    positivity
  have hprod := (hi4.neg).mul (harmonicFive_integral (i - 1) (by omega : i - 1 < p))
  have hrecip := reciprocalTwiceNat_integral i (by omega) hip
  have hquarter := quarter_integral (p := p) (by omega)
  simpa only [stieltjesConstant, sub_eq_add_neg, zero_add] using (hprod.add hrecip.neg).add hquarter.neg

theorem stieltjesConstant_multiple_p (i : ℕ) (hp : 5 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) (hpi : p ∣ i) :
    PadicLower p (-1) (stieltjesConstant i) := by
  have hi4 : PadicLower p 4 ((i : ℚ) ^ 4) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat]
    have h := one_le_padicValNat_of_dvd (Nat.ne_of_gt hi) hpi
    omega
  have hprod := (hi4.neg).mul (harmonicFive_padicLower (i - 1) (by omega : i - 1 < p ^ 2))
  have hrecip := reciprocalTwiceNat_padicLower i (by omega) hi hi2
  have hquarter := (quarter_integral (p := p) (by omega)).mono (by omega : (-1 : ℤ) ≤ 0)
  simpa only [stieltjesConstant, sub_eq_add_neg, show (4 : ℤ) + -5 = -1 from rfl] using
    (hprod.add hrecip.neg).add hquarter.neg

theorem stieltjes_linear_integral (i : ℕ) :
    PolynomialPadicLower p 0 (X * C ((i : ℚ) ^ 4)) := by
  simpa using (polynomialPadicLower_X (p := p)).mul
    (PolynomialPadicLower.constant (show PadicLower p 0 ((i : ℚ) ^ 4) by
      right
      rw [padicValRat.pow, padicValRat.of_nat]
      positivity))

theorem stieltjes_polynomial_padicLower (i : ℕ) (hp : 5 < p) (hi : 0 < i) (hi2 : i < p ^ 2) :
    PolynomialPadicLower p (-5) (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_padicLower i hp hi hi2)).add
    ((stieltjes_linear_integral i).mono (by omega))

theorem stieltjes_polynomial_integral (i : ℕ) (hp : 5 < p) (hip : i < p) :
    PolynomialPadicLower p 0 (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_integral i hp hip)).add
    (stieltjes_linear_integral i)

theorem stieltjes_polynomial_multiple_p (i : ℕ) (hp : 5 < p) (hi : 0 < i)
    (hi2 : i < p ^ 2) (hpi : p ∣ i) :
    PolynomialPadicLower p (-1) (stieltjes i) :=
  (PolynomialPadicLower.constant (stieltjesConstant_multiple_p i hp hi hi2 hpi)).add
    ((stieltjes_linear_integral i).mono (by omega))

#print axioms stieltjes_polynomial_padicLower
#print axioms stieltjes_polynomial_integral
#print axioms stieltjes_polynomial_multiple_p

end Zeta5.Arithmetic
