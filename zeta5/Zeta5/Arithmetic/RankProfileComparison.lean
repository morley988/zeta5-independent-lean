import Zeta5.Arithmetic.LocalDeterminant
import Zeta5.Certificate.ArithmeticProfile

/-!
# The discrete restriction cost and the certified real rank profile

The half-integer endpoint in the number of maximal reflected classes is
the only additive rounding discrepancy. On the fixed range `p/N≥1/512`
it costs at most 641 per prime, uniformly in the stage.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Zeta5.Certificate

theorem floor_nat_div_real (N p : ℕ) :
    ⌊(N : ℝ) / (p : ℝ)⌋ = ((N / p : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_ediv]

theorem floor_inverse_prime_ratio (N p : ℕ) :
    ⌊1 / ((p : ℝ) / N)⌋ = ((N / p : ℕ) : ℤ) := by
  rw [one_div_div, floor_nat_div_real]

theorem profileEpsilon_prime_ratio {N p : ℕ} (hN : 0 < N) (hp : 0 < p) :
    profileEpsilon ((p : ℝ) / N) = ((2 * (N % p) / p : ℕ) : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdecomp : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N p
  have hc : (p : ℝ) / N ≤ 2 * (1 - ((N / p : ℕ) : ℝ) * ((p : ℝ) / N)) ↔ p ≤ 2 * (N % p) := by
    rw [div_le_iff₀ hNreal]
    have he : 2 * (1 - ((N / p : ℕ) : ℝ) * ((p : ℝ) / N)) * N = 2 * ((N % p : ℕ) : ℝ) := by
      field_simp
      nlinarith
    rw [he]
    norm_cast
  unfold profileEpsilon
  rw [floor_inverse_prime_ratio]
  simp only [Int.cast_natCast]
  rw [if_congr hc rfl rfl, reflected_epsilon N p hp]
  split_ifs <;> norm_num at * <;> omega

theorem maximalReflectedClasses_card_real {N p : ℕ} (hp : 0 < p) (hodd : p % 2 = 1) :
    ((maximalReflectedClasses N p).card : ℝ) =
      (N : ℝ) - ((N / p : ℕ) : ℝ) * p -
        ((2 * (N % p) / p : ℕ) : ℝ) * (p : ℝ) / 2 +
        ((2 * (N % p) / p : ℕ) : ℝ) / 2 := by
  have hdecomp : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N p
  have hhalf : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hhalfreal : 2 * (((p - 1) / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hhalf
  rw [maximalReflectedClasses_card N p hodd, reflected_epsilon N p hp]
  by_cases hs : 2 * (N % p) < p
  · rw [if_pos hs, if_pos hs]
    norm_num
    nlinarith
  · rw [if_neg hs, if_neg hs]
    have hle : (p - 1) / 2 ≤ N % p := by omega
    rw [Nat.cast_sub hle]
    norm_num
    nlinarith

def stageRankCost (n p : ℕ) : ℕ :=
  (4 + 2 * ((20 * n) % p) / p) * (24 * n) +
    min (24 * n) (((50 * n - 2) / p + 1) * (maximalReflectedClasses (20 * n) p).card)

variable {p : ℕ} [Fact p.Prime]

theorem windowDeterminant_stageRankCost (n : ℕ) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2) :
    PolynomialPadicLower p (-(stageRankCost n p : ℤ)) (windowDeterminant n) := by
  have h := unscaledCentralPencil_restriction_bound (p := p) (20 * n) n (24 * n) hp
    (by omega) (by omega)
  rw [unscaledCentralPencil_window, ← windowDeterminant] at h
  convert h using 1
  simp only [stageRankCost, restrictionDepth, show 2 * (n + 24 * n) = 50 * n by omega,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem floor_degree_stage_ratio {n : ℕ} (hn : 0 < n) (hp : 0 < p) :
    ⌊(5 / 2 : ℝ) / ((p : ℝ) / (20 * n))⌋ = ((50 * n / p : ℕ) : ℤ) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (5 / 2 : ℝ) / ((p : ℝ) / (20 * n)) = ((50 * n : ℕ) : ℝ) / p := by
    push_cast
    field_simp
    ring
  rw [he, floor_nat_div_real]

theorem middleRankProfile_stage_identity {n : ℕ} (hn : 0 < n) (hp2 : p ≠ 2) :
    ((20 * n : ℕ) : ℝ) * middleRankProfile ((p : ℝ) / (20 * n)) =
      (4 + ((2 * ((20 * n) % p) / p : ℕ) : ℝ)) * (24 * n : ℕ) +
      min ((24 * n : ℕ) : ℝ)
        ((((50 * n / p : ℕ) : ℝ) + 1) *
          (((maximalReflectedClasses (20 * n) p).card : ℝ) -
            ((2 * ((20 * n) % p) / p : ℕ) : ℝ) / 2)) := by
  have hp := (Fact.out : p.Prime).pos
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN : 0 < 20 * n := by omega
  have hcard := maximalReflectedClasses_card_real (N := 20 * n) hp
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2)
  have hdegree : ⌊(5 / 2 : ℝ) / ((p : ℝ) / ((20 * n : ℕ) : ℝ))⌋ =
      ((50 * n / p : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using floor_degree_stage_ratio hn hp
  unfold middleRankProfile
  rw [show (20 * n : ℝ) = ((20 * n : ℕ) : ℝ) by push_cast; rfl,
    profileEpsilon_prime_ratio hN hp, hdegree, floor_inverse_prime_ratio]
  simp only [Int.cast_natCast]
  rw [mul_add, mul_min_of_nonneg _ _ (by positivity)]
  congr 1
  · push_cast
    ring
  · congr 1
    · push_cast
      ring
    · rw [hcard]
      push_cast
      field_simp
      ring

theorem min_add_error_le (a b e : ℝ) (he : 0 ≤ e) :
    min a (b + e) ≤ min a b + e := by
  calc
    min a (b + e) ≤ min (a + e) (b + e) := min_le_min (by linarith) le_rfl
    _ = min a b + e := min_add_add_right _ _ _

theorem stageRankCost_le_profile_error {n : ℕ} (hn : 0 < n) (hp2 : p ≠ 2) :
    (stageRankCost n p : ℝ) ≤
      ((20 * n : ℕ) : ℝ) * middleRankProfile ((p : ℝ) / (20 * n)) +
        (((50 * n / p : ℕ) : ℝ) + 1) / 2 := by
  let e : ℝ := ((2 * ((20 * n) % p) / p : ℕ) : ℝ)
  let d : ℝ := ((50 * n / p : ℕ) : ℝ) + 1
  let w : ℝ := (maximalReflectedClasses (20 * n) p).card
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have he1 : e ≤ 1 := by
    dsimp [e]
    rw [reflected_epsilon (20 * n) p (Fact.out : p.Prime).pos]
    split_ifs <;> norm_num
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hD : (50 * n - 2) / p ≤ 50 * n / p := Nat.div_le_div_right (Nat.sub_le _ _)
  have hD' : (((50 * n - 2) / p : ℕ) : ℝ) + 1 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.add_le_add_right hD 1
  have hraw : (stageRankCost n p : ℝ) ≤ (4 + e) * (24 * n : ℕ) + min ((24 * n : ℕ) : ℝ) (d * w) := by
    simp only [stageRankCost, Nat.cast_add, Nat.cast_mul, Nat.cast_min, Nat.cast_ofNat, Nat.cast_one]
    apply add_le_add le_rfl
    exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hD' hw0)
  have hmin := min_add_error_le ((24 * n : ℕ) : ℝ) (d * (w - e / 2)) (d * e / 2) (by positivity)
  have hsplit : d * (w - e / 2) + d * e / 2 = d * w := by ring
  rw [hsplit] at hmin
  have herr : d * e / 2 ≤ d / 2 := by nlinarith
  rw [middleRankProfile_stage_identity hn hp2]
  change (stageRankCost n p : ℝ) ≤ (4 + e) * (24 * n : ℕ) +
    min ((24 * n : ℕ) : ℝ) (d * (w - e / 2)) + d / 2
  linarith

theorem stageRankCost_le_profile_add_641 {n : ℕ} (hn : 0 < n) (hp2 : p ≠ 2)
    (hcut : (1 / 512 : ℝ) ≤ (p : ℝ) / (20 * n)) :
    (stageRankCost n p : ℝ) ≤
      ((20 * n : ℕ) : ℝ) * middleRankProfile ((p : ℝ) / (20 * n)) + 641 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp := (Fact.out : p.Prime).pos
  have hratio : (50 * n : ℕ) ≤ 1280 * p := by
    have h := (le_div_iff₀ (show 0 < (20 * n : ℝ) by positivity)).mp hcut
    have hreal : (50 : ℝ) * n ≤ 1280 * p := by nlinarith
    exact_mod_cast hreal
  have hD : 50 * n / p ≤ 1280 := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hratio)
  have hDR : ((50 * n / p : ℕ) : ℝ) ≤ 1280 := by exact_mod_cast hD
  exact (stageRankCost_le_profile_error hn hp2).trans (by linarith)

end Zeta5.Arithmetic
