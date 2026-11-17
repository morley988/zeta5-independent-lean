import Zeta5.Construction.Determinant
import Zeta5.Reuse.PadicMinors
import Mathlib.Tactic.Linarith

/-!
# Local integrality of the actual rational moments

The manuscript's moment lemma is obtained from Mathlib's proved
von Staudt--Clausen theorem. This route gives the `-1` valuation bound
without a restriction on the Bernoulli index. For primes greater than five,
the first three potential denominator poles are canceled by the three
consecutive factors in the moment numerator.
-/

noncomputable section
namespace Zeta5.Arithmetic
open OddZeta.FourValue Zeta5.Construction
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem padicLower_nat (a : ℕ) : PadicLower p 0 (a : ℚ) := by
  right
  simp only [padicValRat.of_nat]
  exact Int.natCast_nonneg _

theorem padicLower_int (a : ℤ) : PadicLower p 0 (a : ℚ) := by
  right
  simp only [padicValRat.of_int]
  exact Int.natCast_nonneg _

theorem padicLower_nat_of_dvd (a : ℕ) (hpa : p ∣ a) :
    PadicLower p 1 (a : ℚ) := by
  obtain ⟨b, rfl⟩ := hpa
  have hp : PadicLower p 1 (p : ℚ) := by
    right
    rw [padicValRat.self (Fact.out : p.Prime).one_lt]
  simpa using hp.mul (padicLower_nat (p := p) b)

theorem prime_reciprocal_padicLower (q : ℕ) (hq : q.Prime) :
    PadicLower p (-1) (1 / (q : ℚ)) := by
  right
  by_cases hpq : p = q
  · subst q
    simp [one_div, padicValRat.self (Fact.out : p.Prime).one_lt]
  · letI : Fact q.Prime := ⟨hq⟩
    simp [one_div, padicValRat.of_nat, padicValNat_primes hpq]

theorem other_prime_reciprocal_integral (q : ℕ) (hq : q.Prime) (hpq : p ≠ q) :
    PadicLower p 0 (1 / (q : ℚ)) := by
  letI : Fact q.Prime := ⟨hq⟩
  right
  simp [one_div, padicValRat.of_nat, padicValNat_primes hpq]

theorem bernoulli_even_padicLower (k : ℕ) :
    PadicLower p (-1) (bernoulli (2 * k)) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  let S : Finset ℕ := (Finset.range (2 * k + 2)).filter
    (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)
  have hS : PadicLower p (-1) (∑ q ∈ S, 1 / (q : ℚ)) := by
    apply padicLower_sum
    intro q hq
    exact prime_reciprocal_padicLower q (Finset.mem_filter.mp hq).2.1
  have he : bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ S, 1 / (q : ℚ) := by
    dsimp [S]
    linarith
  rw [he, sub_eq_add_neg]
  exact ((padicLower_int (p := p) z).mono (by norm_num)).add hS.neg

theorem bernoulli_even_integral_of_not_dvd (k : ℕ) (h : ¬ (p - 1) ∣ 2 * k) :
    PadicLower p 0 (bernoulli (2 * k)) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  let S : Finset ℕ := (Finset.range (2 * k + 2)).filter
    (fun q => q.Prime ∧ (q - 1) ∣ 2 * k)
  have hS : PadicLower p 0 (∑ q ∈ S, 1 / (q : ℚ)) := by
    apply padicLower_sum
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    apply other_prime_reciprocal_integral q hq'.1
    intro hpq
    exact h (hpq ▸ hq'.2)
  have he : bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ S, 1 / (q : ℚ) := by
    dsimp [S]
    linarith
  rw [he, sub_eq_add_neg]
  exact (padicLower_int (p := p) z).add hS.neg

def momentNumerator (k : ℕ) : ℕ := (2 * k + 3) * (2 * k + 4) * (2 * k + 5)

theorem rationalMoment_factorization (k : ℕ) :
    rationalMoment k = (-1 : ℚ) ^ k * (1 / 24) * (momentNumerator k : ℚ) *
      bernoulli (2 * (k + 1)) := by
  have he : 2 * (k + 1) = 2 * k + 2 := by omega
  simp only [rationalMoment, momentNumerator, he]
  push_cast
  ring

theorem twentyFour_prime_integral (hp : 5 < p) : PadicLower p 0 (1 / 24 : ℚ) := by
  have hprime : p.Prime := Fact.out
  have h24 : ¬ p ∣ 24 := by
    intro hd
    have hd' : p ∣ 2 ^ 3 * 3 := by norm_num; exact hd
    rcases hprime.dvd_mul.mp hd' with h2 | h3
    · have h2' : p ∣ 2 := hprime.dvd_of_dvd_pow h2
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
      omega
    · have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
      omega
  right
  have hv : padicValNat p 24 = 0 := padicValNat.eq_zero_of_not_dvd h24
  have hvRat : padicValRat p (24 : ℚ) = 0 := by
    simpa [hv] using (padicValRat.of_nat (p := p) (n := 24))
  simp [one_div, hvRat]

theorem sign_prime_integral (k : ℕ) : PadicLower p 0 ((-1 : ℚ) ^ k) := by
  simpa using padicLower_int (p := p) ((-1 : ℤ) ^ k)

/-- Every rational moment has at most a single p in its denominator. -/
theorem rationalMoment_padicLower (k : ℕ) (hp : 5 < p) :
    PadicLower p (-1) (rationalMoment k) := by
  rw [rationalMoment_factorization]
  have h := (((sign_prime_integral (p := p) k).mul (twentyFour_prime_integral hp)).mul
    (padicLower_nat (p := p) (momentNumerator k))).mul (bernoulli_even_padicLower (p := p) (k + 1))
  simpa using h

/-- For indices below `2p-3`, the Bernoulli denominator candidate is
canceled by one of the three consecutive numerator factors. -/
theorem prime_dvd_momentNumerator (k : ℕ) (hp : 5 < p) (hk : k < 2 * p - 3)
    (hd : (p - 1) ∣ 2 * (k + 1)) : p ∣ momentNumerator k := by
  obtain ⟨a, ha⟩ := hd
  have ha1 : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    simp [this] at ha
  have ha4 : a < 4 := by
    by_contra h
    have ham : (p - 1) * 4 ≤ (p - 1) * a := Nat.mul_le_mul_left _ (by omega)
    omega
  interval_cases a
  · have he : 2 * k + 3 = p := by omega
    unfold momentNumerator
    rw [he]
    exact dvd_mul_of_dvd_left (dvd_mul_right p _) _
  · have he : p ∣ 2 * k + 4 := ⟨2, by omega⟩
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right he _) _
  · have he : p ∣ 2 * k + 5 := ⟨3, by omega⟩
    exact dvd_mul_of_dvd_right he _

/-- This is the initial-integrality assertion in the manuscript's
quotient-support lemma, for the actual moment formula. -/
theorem rationalMoment_integral_of_lt (k : ℕ) (hp : 5 < p) (hk : k < 2 * p - 3) :
    PadicLower p 0 (rationalMoment k) := by
  rw [rationalMoment_factorization]
  have hsign := (sign_prime_integral (p := p) k).mul (twentyFour_prime_integral hp)
  by_cases hd : (p - 1) ∣ 2 * (k + 1)
  · have hn := padicLower_nat_of_dvd (p := p) (momentNumerator k)
      (prime_dvd_momentNumerator k hp hk hd)
    simpa using (hsign.mul hn).mul (bernoulli_even_padicLower (p := p) (k + 1))
  · simpa using (hsign.mul (padicLower_nat (p := p) (momentNumerator k))).mul
      (bernoulli_even_integral_of_not_dvd (p := p) (k + 1) hd)

#print axioms rationalMoment_padicLower
#print axioms rationalMoment_integral_of_lt

end Zeta5.Arithmetic
