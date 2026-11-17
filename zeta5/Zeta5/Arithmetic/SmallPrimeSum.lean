import Zeta5.Arithmetic.SmallPrimeEntries
import Zeta5.Arithmetic.NormalizerBounds
import Zeta5.Analysis.PhysicalMeasureStieltjes
import Zeta5.Endpoint.ConcreteCriterion
import Mathlib.Data.Nat.Sqrt

/-!
# A square-root cutoff and the actual small-prime logarithmic charge

The cutoff is deliberately elementary. Above it every prime meets the local
square threshold. Below it the all-prime determinant estimate has total cost
at most the number of integers in the interval times one logarithmic bound.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction Zeta5.Endpoint
open Filter
open scoped Topology

def smallPrimeCutoff (n : ℕ) : ℕ := 100*(Nat.sqrt n+1)

lemma smallPrimeCutoff_ge (n : ℕ) : 100 ≤ smallPrimeCutoff n := by
  unfold smallPrimeCutoff
  omega

theorem prime_above_smallPrimeCutoff_good {n p : ℕ} (hp : smallPrimeCutoff n < p) :
    5 < p ∧ 100*n+6 < p^2 := by
  have h1 := Nat.lt_succ_sqrt' n
  have h2 := smallPrimeCutoff_ge n
  constructor
  · omega
  · unfold smallPrimeCutoff at hp
    have hk : 0 ≤ Nat.sqrt n := Nat.zero_le _
    nlinarith

theorem smallPrimeCutoff_lt_middle_of_large {n : ℕ} (hn : 100000000 ≤ n) :
    smallPrimeCutoff n < (20*n)/512 := by
  have hk : 10000 ≤ Nat.sqrt n := (Nat.le_sqrt').mpr (by norm_num; exact hn)
  have hsq := Nat.sqrt_le' n
  have hmul : 512*(smallPrimeCutoff n+1) ≤ 20*n := by
    unfold smallPrimeCutoff
    nlinarith
  have h : smallPrimeCutoff n+1 ≤ (20*n)/512 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 512)).mpr (by nlinarith [hmul])
  omega

theorem smallPrimeCutoff_eventually_lt_middle :
    ∀ᶠ n : ℕ in atTop, smallPrimeCutoff n < (20*n)/512 :=
  (eventually_ge_atTop 100000000).mono (fun _ hn => smallPrimeCutoff_lt_middle_of_large hn)

def smallPrimeSet (Y : ℕ) : Finset ℕ := (Icc 1 Y).filter Nat.Prime

lemma mem_smallPrimeSet {p Y : ℕ} : p ∈ smallPrimeSet Y ↔ p.Prime ∧ p ≤ Y := by
  simp only [smallPrimeSet, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hpY⟩, hp⟩
    exact ⟨hp, hpY⟩
  · rintro ⟨hp, hpY⟩
    exact ⟨⟨hp.one_le, hpY⟩, hp⟩

lemma smallPrimeSet_card_le (Y : ℕ) : (smallPrimeSet Y).card ≤ Y := by
  apply (card_filter_le _ _).trans
  simp

lemma natLog_mul_log_le {p D : ℕ} (hp : p.Prime) (hD : 0 < D) :
    (Nat.log p D : ℝ)*Real.log (p : ℝ) ≤ Real.log (D : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (p : ℝ)^(Nat.log p D) ≤ (D : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self p hD.ne'
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hpR _) hpow

lemma padicValNat_mul_log_le {p D : ℕ} (hp : p.Prime) (hD : 0 < D) :
    (padicValNat p D : ℝ)*Real.log (p : ℝ) ≤ Real.log (D : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hl : (padicValNat p D : ℝ) ≤ Nat.log p D := by
    exact_mod_cast padicValNat_le_nat_log (p := p) D
  apply (mul_le_mul_of_nonneg_right hl
    (Real.log_natCast_nonneg p)).trans
  exact natLog_mul_log_le hp hD

def smallPrimeCostInt (n p : ℕ) : ℤ :=
  ((24*n : ℕ) : ℤ)*(9*(Nat.log p (100*n+4) : ℤ)+(padicValNat p 96 : ℤ))

noncomputable def smallPrimeCharge (n Y : ℕ) : ℝ :=
  ∑ p ∈ smallPrimeSet Y, (smallPrimeCostInt n p : ℝ)*Real.log (p : ℝ)

noncomputable def smallPrimeError (n : ℕ) : ℝ :=
  (24*(n : ℝ))*(smallPrimeCutoff n : ℝ)*
    (9*Real.log (100*(n : ℝ)+4)+Real.log 96)

theorem smallPrimeCostInt_log_le (n p : ℕ) (hp : p.Prime) :
    (smallPrimeCostInt n p : ℝ)*Real.log (p : ℝ) ≤
      (24*(n : ℝ))*(9*Real.log (100*(n : ℝ)+4)+Real.log 96) := by
  have h1 := natLog_mul_log_le hp (by omega : 0 < 100*n+4)
  have h2 := padicValNat_mul_log_le hp (by norm_num : 0 < 96)
  norm_num only [Nat.cast_ofNat] at h2
  have h : 9*((Nat.log p (100*n+4) : ℝ)*Real.log p)+
      (padicValNat p 96 : ℝ)*Real.log p ≤ 9*Real.log (100*(n : ℝ)+4)+Real.log 96 := by
    push_cast at h1
    linarith
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 24*(n : ℝ) by positivity)
  convert! hm using 1 <;> simp only [smallPrimeCostInt, Int.cast_mul, Int.cast_add,
    Int.cast_natCast, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat] <;> ring

theorem smallPrimeCharge_le (n Y : ℕ) :
    smallPrimeCharge n Y ≤ (24*(n : ℝ))*(Y : ℝ)*
      (9*Real.log (100*(n : ℝ)+4)+Real.log 96) := by
  have hb : 0 ≤ (24*(n : ℝ))*(9*Real.log (100*(n : ℝ)+4)+Real.log 96) := by
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (Real.log_nonneg
        (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    · exact Real.log_nonneg (by norm_num)
  unfold smallPrimeCharge
  calc
    _ ≤ ∑ _p ∈ smallPrimeSet Y,
        (24*(n : ℝ))*(9*Real.log (100*(n : ℝ)+4)+Real.log 96) := by
      apply sum_le_sum
      intro p hp
      exact smallPrimeCostInt_log_le n p (mem_smallPrimeSet.mp hp).1
    _ ≤ (Y : ℝ)*((24*(n : ℝ))*(9*Real.log (100*(n : ℝ)+4)+Real.log 96)) := by
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast smallPrimeSet_card_le Y) hb
    _ = _ := by ring

theorem smallPrimeCharge_cutoff_le (n : ℕ) :
    smallPrimeCharge n (smallPrimeCutoff n) ≤ smallPrimeError n :=
  smallPrimeCharge_le n (smallPrimeCutoff n)

/-- The actual primitive normalizer's signed contribution from all primes
below the cutoff is bounded by the explicit small-prime error. -/
theorem smallPrime_normalizer_sum_le (n : ℕ) :
    (∑ p ∈ smallPrimeSet (smallPrimeCutoff n),
      (padicValRat p (windowNormalizer n) : ℝ)*Real.log p) ≤ smallPrimeError n := by
  apply le_trans _ (smallPrimeCharge_cutoff_le n)
  apply sum_le_sum
  intro p hp
  letI : Fact p.Prime := ⟨(mem_smallPrimeSet.mp hp).1⟩
  have hval := windowDeterminant_smallPrime_padicLower (p := p) n
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p (-(smallPrimeCostInt n p))
    (by simpa [smallPrimeCostInt] using hval)
  have h' : padicValRat p (windowNormalizer n) ≤ smallPrimeCostInt n p := by
    simpa only [windowNormalizer, neg_neg] using h
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h') (Real.log_natCast_nonneg p)

end Zeta5.Arithmetic
