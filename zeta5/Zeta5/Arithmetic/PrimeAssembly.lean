import Zeta5.Arithmetic.NormalizerPrimeTail
import Zeta5.Arithmetic.PrimeRowBound
import Zeta5.Certificate.AllPrimePieces
import Zeta5.Certificate.PrimePiecesTelescope
import Zeta5.Analysis.ArithmeticRate

/-! The actual signed normalizer charge is bounded by the complete
finite affine profile, with negligible endpoint and per-prime errors. -/

noncomputable section
namespace Zeta5.Arithmetic
open Zeta5.Certificate Zeta5.Certificate.ExtendedArithmetic
open Zeta5.Reuse.PrimePiecewise Zeta5.Endpoint
open Filter
open scoped Topology Chebyshev

theorem prime_good_of_fixed_cutoff {n p : ℕ} (hn : 0 < n)
    (hcut : smallPrimeCutoff n ≤ (20 * n) / 512)
    (hβ : (1 / 512 : ℝ) < (p : ℝ) / (20 * n)) :
    5 < p ∧ 100 * n + 6 < p ^ 2 := by
  have hN : (0 : ℝ) < 20 * n := by positivity
  have hi := (lt_div_iff₀ hN).mp hβ
  have hNat : 20 * n < 512 * p := by
    exact_mod_cast (show 20 * (n : ℝ) < 512 * p by nlinarith)
  have hp : (20 * n) / 512 < p :=
    (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 512)).mpr (by omega)
  exact prime_above_smallPrimeCutoff_good (hcut.trans_lt hp)

theorem allPrimePieces_local_bound {n p : ℕ} (c : AffinePiece)
    (hn : 0 < n) (hcut : smallPrimeCutoff n ≤ (20 * n) / 512)
    (hp : p.Prime) (hc : c ∈ allPrimePieces)
    (hl : c.lo < (p : ℝ) / (20 * n : ℕ))
    (hr : (p : ℝ) / (20 * n : ℕ) < c.hi) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤
      ((20 * n : ℕ) : ℝ) * (c.intercept + c.slope * ((p : ℝ) / (20 * n : ℕ))) + 641 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hβ : (1 / 512 : ℝ) < (p : ℝ) / (20 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (allPrimePieces_bounds hc).1.trans_lt hl
  obtain ⟨hp5, hpsq⟩ := prime_good_of_fixed_cutoff hn hcut hβ
  rcases allPrimePieces_mem hc with ⟨x, hx, rfl⟩ | ⟨row, hrow, rfl⟩ | ⟨row, hrow, rfl⟩
  · have h := windowNormalizer_middleProfile_bound hn hp5 hpsq hβ.le
    have he := ArithmeticCell.profile_affine (allCells_valid x hx) hl hr
    simp only [Nat.cast_mul, Nat.cast_ofNat] at he
    rw [he] at h
    simpa only [cellPrimePiece, Nat.cast_mul, Nat.cast_ofNat] using h
  · have h := windowNormalizer_upperProfile_bound row hn hp5 hpsq hrow
      (by simpa only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat] using hl)
      (by simpa only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat] using hr)
    simp only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · have h := windowNormalizer_largeProfile_bound row hn hrow
      (by simpa only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat] using hl)
      (by simpa only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat] using hr)
    simp only [rowPrimePiece, Nat.cast_mul, Nat.cast_ofNat]
    linarith

theorem allPrimePieces_uniform_bound {n p : ℕ} (c : AffinePiece)
    (hn : 0 < n) (hcut : smallPrimeCutoff n ≤ (20 * n) / 512)
    (hp : p.Prime) (hc : c ∈ allPrimePieces)
    (hl : c.lo < (p : ℝ) / (20 * n : ℕ)) :
    (padicValRat p (windowNormalizer n) : ℝ) ≤ (36 / 5 : ℝ) * (20 * n : ℕ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hβ : (1 / 512 : ℝ) < (p : ℝ) / (20 * n) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (allPrimePieces_bounds hc).1.trans_lt hl
  obtain ⟨hp5, hpsq⟩ := prime_good_of_fixed_cutoff hn hcut hβ
  exact windowNormalizer_goodPrime_bound_real n hp5 hpsq

def primeErrorCoefficient : ℝ := 641 * allPrimePieces.length

def endpointErrorCoefficient : ℝ :=
  (allPrimePieces.map (fun c => rightEndpointPenalty c (36 / 5))).sum

theorem allPrimePieces_charge_bound (n : ℕ) (hn : 0 < n)
    (hcut : smallPrimeCutoff n ≤ (20 * n) / 512) :
    (allPrimePieces.map (fun c : AffinePiece =>
      primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ))
        ⌊c.lo * ((20 * n : ℕ) : ℝ)⌋₊ ⌊c.hi * ((20 * n : ℕ) : ℝ)⌋₊)).sum ≤
      primeProfileMajorant allPrimePieces primeErrorCoefficient endpointErrorCoefficient (5 / 2) (20 * n) := by
  apply sum_prime_row_bounds allPrimePieces (20 * n) (5 / 2) (36 / 5) 641
  intro c hc
  apply prime_row_charge_le c (allPrimePieces_valid c hc) (20 * n) (by omega)
    (5 / 2) (36 / 5) 641 (allPrimePieces_bounds hc).2
    (by have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        norm_num; nlinarith)
    (by norm_num) (by norm_num)
  · intro p hp hl hr
    exact allPrimePieces_local_bound c hn hcut hp hc hl hr
  · intro p hp hl hr
    exact allPrimePieces_uniform_bound c hn hcut hp hc hl

#print axioms allPrimePieces_charge_bound

theorem windowNormalizer_finiteProfile_bound (n : ℕ) (hn : 0 < n)
    (hcut : smallPrimeCutoff n ≤ (20 * n) / 512) :
    primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ))
      ((20 * n) / 512) (50 * n) ≤
      primeProfileMajorant allPrimePieces primeErrorCoefficient endpointErrorCoefficient (5 / 2) (20 * n) := by
  have h := allPrimePieces_charge_bound n hn hcut
  change pieceWeightedSum allPrimePieces
    (fun p => (padicValRat p (windowNormalizer n) : ℝ)) (20 * n) ≤ _ at h
  rw [allPrimePieces_weightedSum] at h
  have hlo : ⌊(1 / 512 : ℝ) * ((20 * n : ℕ) : ℝ)⌋₊ = (20 * n) / 512 := by
    have hf (a d : ℕ) : ⌊(a : ℝ) / d⌋₊ = a / d := by
      rw [Nat.floor_div_natCast, Nat.floor_natCast]
    rw [show (1 / 512 : ℝ) * ((20 * n : ℕ) : ℝ) = ((20 * n : ℕ) : ℝ) / 512 by ring]
    simpa only [Nat.cast_ofNat] using hf (20 * n) 512
  have hhi : ⌊(5 / 2 : ℝ) * ((20 * n : ℕ) : ℝ)⌋₊ = 50 * n := by
    rw [show (5 / 2 : ℝ) * ((20 * n : ℕ) : ℝ) = ((50 * n : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast]
  simpa only [hlo, hhi] using h

theorem windowNormalizer_log_le_arithmeticMajorant_eventually :
    ∀ᶠ n : ℕ in atTop, Real.log (windowNormalizer n : ℝ) ≤
      Zeta5.Analysis.arithmeticMajorant allPrimePieces primeErrorCoefficient endpointErrorCoefficient n := by
  filter_upwards [windowNormalizer_log_le_tail_and_primeSum_eventually,
    smallPrimeCutoff_eventually_lt_middle, eventually_gt_atTop (0 : ℕ)] with n htail hcut hn
  have hfinite := windowNormalizer_finiteProfile_bound n hn hcut.le
  calc
    _ ≤ smallPrimeError n + ((144 * n : ℕ) : ℝ) * θ (((20 * n : ℕ) : ℝ) / 512) +
        primeWeightedSum (fun p => (padicValRat p (windowNormalizer n) : ℝ))
          ((20 * n) / 512) (50 * n) := htail
    _ ≤ smallPrimeError n + ((144 * n : ℕ) : ℝ) * θ (((20 * n : ℕ) : ℝ) / 512) +
        primeProfileMajorant allPrimePieces primeErrorCoefficient endpointErrorCoefficient (5 / 2) (20 * n) :=
      add_le_add le_rfl hfinite
    _ = _ := by
      simp only [Zeta5.Analysis.arithmeticMajorant, Zeta5.Analysis.arithmeticTailMajorant,
        Nat.cast_mul, Nat.cast_ofNat]

theorem windowNormalizer_arithmetic_rate :
    ∀ᶠ n : ℕ in atTop, Real.log (windowNormalizer n : ℝ) ≤
      (5412 / 1000 : ℝ) * windowScale n :=
  Zeta5.Analysis.arithmeticRate_5412_of_majorant allPrimePieces allPrimePieces_valid
    primeErrorCoefficient endpointErrorCoefficient allPrimePieces_area_le
    windowNormalizer_log_le_arithmeticMajorant_eventually

#print axioms windowNormalizer_log_le_arithmeticMajorant_eventually
#print axioms windowNormalizer_arithmetic_rate

end Zeta5.Arithmetic
