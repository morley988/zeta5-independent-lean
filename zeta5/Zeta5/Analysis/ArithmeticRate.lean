import Zeta5.Analysis.SmallPrimeError
import Zeta5.Reuse.PrimePiecewise
import Zeta5.Certificate.ExtendedArithmetic
import Zeta5.Certificate.AllPrimePieces
import Zeta5.Endpoint.AnalyticCriterion

/-!
# Quadratic arithmetic rates from the actual prime profile majorant

The small-prime error is negligible. The crude tail between the moving
square-root cutoff and the fixed profile cutoff costs `36/(5*512)`.
The remaining finite affine cells are summed using the proved prime number
theorem. A fixed positive gap then supplies an eventual rate without an
additional error term.
-/

noncomputable section
namespace Zeta5.Analysis
open Filter Zeta5.Endpoint Zeta5.Reuse Zeta5.Reuse.PrimePiecewise
open scoped Topology Chebyshev

/-- The elementary bound `6r` at primes below `N/512`, with `r=24n`. -/
def arithmeticTailMajorant (n : ℕ) : ℝ :=
  (144*(n : ℝ))*θ ((20*(n : ℝ))/512)

/-- The complete majorant after pointwise valuation bounds are summed. -/
def arithmeticMajorant (cells : List AffinePiece) (K L : ℝ) (n : ℕ) : ℝ :=
  Zeta5.Arithmetic.smallPrimeError n+arithmeticTailMajorant n+
    primeProfileMajorant cells K L (5/2) (20*n)

lemma windowIndex_tendsto : Tendsto (fun n : ℕ => 20*n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact (eventually_ge_atTop b).mono (fun n hn => by omega)

theorem arithmeticTailMajorant_limit :
    Tendsto (fun n : ℕ => arithmeticTailMajorant n/windowScale n)
      atTop (𝓝 (36/(5*512) : ℝ)) := by
  have h := (ThetaAsymptotic.scaled_limit θ PrimeNumberTheorem.theta_ratio_limit
    (20/512) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hm := h.const_mul (144/400 : ℝ)
  have hvalue : (144/400 : ℝ)*(20/512)=36/(5*512) := by norm_num
  rw [hvalue] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold arithmeticTailMajorant windowScale
  dsimp only [Function.comp_apply]
  have harg : (20/512 : ℝ)*(n : ℝ)=20*(n : ℝ)/512 := by ring
  rw [harg]
  field_simp
  ring

theorem windowPrimeProfileMajorant_limit (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L : ℝ) :
    Tendsto (fun n : ℕ => primeProfileMajorant cells K L (5/2) (20*n)/windowScale n)
      atTop (𝓝 (finiteArea cells)) := by
  have h := (primeProfileMajorant_limit cells hcells K L (5/2) (by norm_num)).comp
    windowIndex_tendsto
  convert! h using 1
  ext n
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat, windowScale]

theorem arithmeticMajorant_limit (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L : ℝ) :
    Tendsto (fun n : ℕ => arithmeticMajorant cells K L n/windowScale n)
      atTop (𝓝 (36/(5*512)+finiteArea cells)) := by
  have h := (smallPrimeError_over_windowScale_limit.add arithmeticTailMajorant_limit).add
    (windowPrimeProfileMajorant_limit cells hcells K L)
  simpa only [arithmeticMajorant, add_div, zero_add] using h

/-- A strict gap above the finite area yields a pure eventual quadratic
bound. This theorem has no arithmetic hypothesis beyond the displayed
majorization of the actual primitive normalizer. -/
theorem arithmeticRate_of_majorant (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L A : ℝ)
    (ha : 36/(5*512)+finiteArea cells < A)
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ arithmeticMajorant cells K L n) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ A*windowScale n := by
  have hlt := (arithmeticMajorant_limit cells hcells K L).eventually (gt_mem_nhds ha)
  filter_upwards [hbound, hlt, eventually_gt_atTop (0 : ℕ)] with n hn hlt hnpos
  have hs : 0 < windowScale n := by unfold windowScale; positivity
  exact hn.trans (le_of_lt ((div_lt_iff₀ hs).mp hlt))

/-- The exact certificate leaves enough room for the rational rate `5.412`. -/
theorem certified_arithmetic_area_lt (cells : List AffinePiece)
    (harea : finiteArea cells ≤
      (Zeta5.Certificate.ExtendedArithmetic.areaUpper : ℝ)+901/600+19/16) :
    36/(5*512)+finiteArea cells < (5412 : ℝ)/1000 := by
  have hsum : (Zeta5.Certificate.ExtendedArithmetic.areaUpper : ℝ)+
      36/(5*512)+901/600+19/16=
      (Zeta5.Certificate.ExtendedArithmetic.totalUpper : ℝ) := by
    norm_num [Zeta5.Certificate.ExtendedArithmetic.areaUpper,
      Zeta5.Certificate.ExtendedArithmetic.totalUpper]
  have hstrict : (Zeta5.Certificate.ExtendedArithmetic.totalUpper : ℝ)<5412/1000 := by
    norm_num [Zeta5.Certificate.ExtendedArithmetic.totalUpper]
  linarith

theorem arithmeticRate_5412_of_majorant (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L : ℝ)
    (harea : finiteArea cells ≤
      (Zeta5.Certificate.ExtendedArithmetic.areaUpper : ℝ)+901/600+19/16)
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ arithmeticMajorant cells K L n) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ (5412/1000)*windowScale n :=
  arithmeticRate_of_majorant cells hcells K L (5412/1000)
    (certified_arithmetic_area_lt cells harea) hbound

/-- Final endpoint adapter: once the actual prime sum is dominated by the
finite profile with its certified area, all analytic and asymptotic
obligations are discharged. -/
theorem irrational_zeta5_of_certified_prime_majorant (cells : List AffinePiece)
    (hcells : ∀ c ∈ cells, c.Valid) (K L : ℝ)
    (harea : finiteArea cells ≤
      (Zeta5.Certificate.ExtendedArithmetic.areaUpper : ℝ)+901/600+19/16)
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ arithmeticMajorant cells K L n) :
    Irrational (riemannZeta 5).re := by
  apply irrational_zeta5_of_arithmetic_rate_lt_certified (5412/1000) (by norm_num)
    (fun _ => 0)
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · simpa only [add_zero] using arithmeticRate_5412_of_majorant cells hcells K L harea hbound

/-- The concrete certified data have now discharged the finite-cell validity
and area hypotheses. Only the actual summed valuation bound remains. -/
theorem irrational_zeta5_of_allPrimePieces_majorant (K L : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (windowNormalizer n : ℝ) ≤
        arithmeticMajorant Zeta5.Certificate.allPrimePieces K L n) :
    Irrational (riemannZeta 5).re :=
  irrational_zeta5_of_certified_prime_majorant Zeta5.Certificate.allPrimePieces
    Zeta5.Certificate.allPrimePieces_valid K L
    Zeta5.Certificate.allPrimePieces_area_le hbound

end Zeta5.Analysis
