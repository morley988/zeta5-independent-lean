import Zeta5.Arithmetic.RankProfileComparison
import Zeta5.Arithmetic.NormalizerBounds
import Zeta5.Arithmetic.LargePrimes
import Zeta5.Arithmetic.SmallPrimeEntries
import Zeta5.Arithmetic.UpperProfileComparison
import Zeta5.Endpoint.PhysicalCriterion

/-!
# Actual local bounds for the primitive window normalizer

The determinant is nonzero by its verified physical Gram representation.
All estimates in this module therefore concern the concrete positive
rational normalizer used at the irrationality endpoint.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Zeta5.Endpoint
open Zeta5.Certificate

variable {p : ℕ} [Fact p.Prime]

theorem stageRankCost_le_six_dimension (n : ℕ) : stageRankCost n p ≤ 6 * (24 * n) := by
  have heps : 2 * ((20 * n) % p) / p ≤ 1 := by
    rw [reflected_epsilon (20 * n) p (Fact.out : p.Prime).pos]
    split_ifs <;> omega
  have hmin : min (24 * n) (((50 * n - 2) / p + 1) *
      (maximalReflectedClasses (20 * n) p).card) ≤ 24 * n := min_le_left _ _
  unfold stageRankCost
  nlinarith

theorem windowNormalizer_rankCost_bound (n : ℕ) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ (stageRankCost n p : ℤ) := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p
    (-(stageRankCost n p : ℤ)) (windowDeterminant_stageRankCost n hp hsmall)
  simpa only [windowNormalizer, neg_neg] using h

/-- A uniform good-prime estimate, including primes above the physical
node range. This is the bound used for the short initial arithmetic tail. -/
theorem windowNormalizer_goodPrime_bound (n : ℕ) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ (144 * n : ℕ) := by
  have h := windowNormalizer_rankCost_bound (p := p) n hp hsmall
  have hcost : (stageRankCost n p : ℤ) ≤ (144 * n : ℕ) := by
    exact_mod_cast (by simpa only [show 6 * (24 * n) = 144 * n by omega] using stageRankCost_le_six_dimension (p := p) n)
  exact h.trans hcost

theorem windowNormalizer_goodPrime_bound_real (n : ℕ) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤ (36 / 5 : ℝ) * (20 * n : ℕ) := by
  have h : (padicValRat p (windowNormalizer n) : ℝ) ≤ (144 * n : ℕ) := by
    exact_mod_cast windowNormalizer_goodPrime_bound (p := p) n hp hsmall
  convert h using 1 <;> push_cast <;> ring

theorem windowNormalizer_nonpos_above_window (n : ℕ) (hn : 0 < n) (hp : 50 * n < p) :
    padicValRat p (windowNormalizer n) ≤ 0 := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p 0
    (windowDeterminant_integral_above_window (p := p) n hn hp)
  simpa only [windowNormalizer, neg_zero] using h

theorem windowNormalizer_middleProfile_bound {n : ℕ} (hn : 0 < n) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2)
    (hcut : (1 / 512 : ℝ) ≤ (p : ℝ) / (20 * n)) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤
      ((20 * n : ℕ) : ℝ) * middleRankProfile ((p : ℝ) / (20 * n)) + 641 := by
  have h : (padicValRat p (windowNormalizer n) : ℝ) ≤ (stageRankCost n p : ℝ) := by
    exact_mod_cast windowNormalizer_rankCost_bound (p := p) n hp hsmall
  exact h.trans (stageRankCost_le_profile_add_641 hn (by omega) hcut)

def smallPrimeEntryCost (n p : ℕ) : ℕ :=
  (24 * n) * (9 * Nat.log p (100 * n + 4) + padicValNat p 96)

theorem windowNormalizer_smallPrime_bound (n : ℕ) :
    padicValRat p (windowNormalizer n) ≤ (smallPrimeEntryCost n p : ℤ) := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p _
    (windowDeterminant_smallPrime_padicLower (p := p) n)
  change padicValRat p (primitiveNormalizer (windowDeterminant n)) ≤ _
  convert h using 1
  simp only [smallPrimeEntryCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem windowNormalizer_smallPrime_bound_real (n : ℕ) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤
      (24 * n : ℕ) * (9 * (Nat.log p (100 * n + 4) : ℝ) + (padicValNat p 96 : ℝ)) := by
  have h : (padicValRat p (windowNormalizer n) : ℝ) ≤ (smallPrimeEntryCost n p : ℝ) := by
    exact_mod_cast windowNormalizer_smallPrime_bound (p := p) n
  simpa only [smallPrimeEntryCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

theorem windowNormalizer_upperCharge_bound (n : ℕ) (hn : 0 < n) (hp : 5 < p)
    (hmp : 2 * n < p) (hpN : p ≤ 20 * n) (hN : 20 * n < 3 * p)
    (hlarge : 50 * n < p ^ 2) :
    padicValRat p (windowNormalizer n) ≤ upperCharge n p := by
  have hF : PolynomialPadicLower p (-upperCharge n p) (windowDeterminant n) := by
    have h := windowDeterminant_upperBand_bound (p := p) n hn hp hmp hpN hN hlarge
    convert h using 1
    unfold upperCharge
    ring
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p _ hF
  simpa only [windowNormalizer, neg_neg] using h

theorem upperRows_endpoints {row : AffineRow} (hrow : row ∈ upperRows) :
    (9 / 20 : ℝ) ≤ (row.lo : ℝ) ∧ (row.hi : ℝ) ≤ 1 := by
  simp only [upperRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem windowNormalizer_upperProfile_bound {n : ℕ} (row : AffineRow)
    (hn : 0 < n) (hp : 5 < p) (hsmall : 100 * n + 6 < p ^ 2)
    (hrow : row ∈ upperRows)
    (hl : (row.lo : ℝ) < (p : ℝ) / (20 * n))
    (hr : (p : ℝ) / (20 * n) < (row.hi : ℝ)) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤
      20 * n * ((row.intercept : ℝ) + (row.slope : ℝ) * ((p : ℝ) / (20 * n))) + 8 := by
  have hNreal : (0 : ℝ) < 20 * n := by positivity
  obtain ⟨hlo, hhi⟩ := upperRows_endpoints hrow
  have hl' := (lt_div_iff₀ hNreal).mp (hlo.trans_lt hl)
  have hr' := (div_lt_iff₀ hNreal).mp (hr.trans_le hhi)
  have hpl : 9 * n < p := by
    exact_mod_cast (show 9 * (n : ℝ) < (p : ℝ) by nlinarith)
  have hpr : p < 20 * n := by
    exact_mod_cast (show (p : ℝ) < 20 * (n : ℝ) by nlinarith)
  have h : (padicValRat p (windowNormalizer n) : ℝ) ≤ (upperCharge n p : ℝ) := by
    exact_mod_cast windowNormalizer_upperCharge_bound (p := p) n hn hp (by omega)
      hpr.le (by omega) (by omega)
  exact h.trans (upperCharge_affine n p row hn hrow hl hr)

theorem windowNormalizer_largeCharge_bound (n : ℕ) (hn : 0 < n) (hNp : 20 * n < p) :
    padicValRat p (windowNormalizer n) ≤ factorialCharge (20 * n) n (24 * n) p := by
  have h := primitiveNormalizer_padicVal_le (windowDeterminant n)
    (Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero n) p _
    (windowDeterminant_largePrime_bound (p := p) n hn hNp)
  simpa only [windowNormalizer, neg_neg] using h

theorem largeRows_lo_ge_one {row : AffineRow} (hrow : row ∈ largeRows) :
    (1 : ℝ) ≤ (row.lo : ℝ) := by
  simp only [largeRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> norm_num

theorem windowNormalizer_largeProfile_bound {n : ℕ} (row : AffineRow)
    (hn : 0 < n) (hrow : row ∈ largeRows)
    (hl : (row.lo : ℝ) < (p : ℝ) / (20 * n))
    (hr : (p : ℝ) / (20 * n) < (row.hi : ℝ)) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤
      20 * n * ((row.intercept : ℝ) + (row.slope : ℝ) * ((p : ℝ) / (20 * n))) := by
  have hNreal : (0 : ℝ) < 20 * n := by positivity
  have hl' := (lt_div_iff₀ hNreal).mp ((largeRows_lo_ge_one hrow).trans_lt hl)
  have hNp : 20 * n < p := by
    exact_mod_cast (show 20 * (n : ℝ) < (p : ℝ) by nlinarith)
  have h : (padicValRat p (windowNormalizer n) : ℝ) ≤
      (factorialCharge (20 * n) n (24 * n) p : ℝ) := by
    exact_mod_cast windowNormalizer_largeCharge_bound (p := p) n hn hNp
  exact h.trans (largeCharge_affine n p row hn hrow hl hr)

end Zeta5.Arithmetic
