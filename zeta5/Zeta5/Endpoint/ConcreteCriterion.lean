import Zeta5.Construction.Determinant
import Zeta5.Endpoint.IntegerPolynomial
import Zeta5.Endpoint.PrimitiveNormalization
import Zeta5.Endpoint.ZetaBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Closing criteria for the actual factorial-window determinant

These theorems refer to `Construction.windowDeterminant`, the explicitly
defined Bernoulli-moment/Stieltjes polynomial of the manuscript, and to
Mathlib's actual Riemann zeta value. They are conditional reductions: none
of the positivity or asymptotic hypotheses is supplied by this module.

The universally valid degree bound `24*n` is used to clear a hypothetical
rational argument. This changes only the linear denominator term, and hence
does not affect a strictly positive gap on the `(20*n)^2` scale.
-/

noncomputable section
namespace Zeta5.Endpoint
open Filter Polynomial
open scoped Topology

def windowValue (n : ℕ) : ℝ :=
  (Construction.windowDeterminant n).eval₂ (Rat.castHom ℝ) (realZeta 5)

def windowNormalizer (n : ℕ) : ℚ := primitiveNormalizer (Construction.windowDeterminant n)

def windowIntegerPolynomial (n : ℕ) : ℤ[X] :=
  normalizedPolynomial (Construction.windowDeterminant n)

def windowScale (n : ℕ) : ℝ := (20 * (n : ℝ)) ^ 2

theorem windowNormalizer_pos (n : ℕ) : 0 < windowNormalizer n :=
  primitiveNormalizer_pos _

theorem windowIntegerPolynomial_degree (n : ℕ) :
    (windowIntegerPolynomial n).natDegree ≤ 24 * n := by
  rw [windowIntegerPolynomial, normalizedPolynomial_natDegree]
  exact Construction.windowDeterminant_natDegree_le n

theorem windowIntegerPolynomial_eval (n : ℕ) :
    (windowIntegerPolynomial n).eval₂ (Int.castRingHom ℝ) (realZeta 5) =
      (windowNormalizer n : ℝ) * windowValue n := by
  exact normalizedPolynomial_eval_real _ _

/-- The concrete determinant endpoint, assuming positivity and the required
denominator-scaled decay for every fixed hypothetical denominator. -/
theorem irrational_zeta5_of_normalized_decay
    (hpositive : ∀ᶠ n in atTop, 0 < windowValue n)
    (hdecay : ∀ b : ℕ, 0 < b →
      Tendsto (fun n => (b : ℝ) ^ (24 * n) *
        ((windowNormalizer n : ℝ) * windowValue n)) atTop (𝓝 0)) :
    Irrational (riemannZeta 5).re := by
  apply irrational_realZeta_five_iff.mp
  apply irrational_of_integer_polynomial_decay (realZeta 5)
    windowIntegerPolynomial (fun n => 24 * n) windowIntegerPolynomial_degree
  · filter_upwards [hpositive] with n hn
    rw [windowIntegerPolynomial_eval]
    exact mul_pos (by exact_mod_cast windowNormalizer_pos n) hn
  · intro b hb
    simpa only [windowIntegerPolynomial_eval] using hdecay b hb

theorem linear_over_windowScale_limit (c : ℝ) :
    Tendsto (fun n : ℕ => (c * (n : ℝ)) / windowScale n) atTop (𝓝 0) := by
  have ht := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (c / 400)
  convert ht using 1
  · ext n
    by_cases hn : n = 0
    · simp [hn, windowScale]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      dsimp [windowScale]
      field_simp
      ring
  · simp

/-- Concrete closing theorem with the two manuscript rate estimates and
explicit `o(N^2)` error hypotheses. This does not establish those estimates. -/
theorem irrational_zeta5_of_log_rate_bounds (A B : ℝ) (hgap : A < B)
    (errorArithmetic errorAnalytic : ℕ → ℝ)
    (herrorArithmetic : Tendsto (fun n => errorArithmetic n / windowScale n) atTop (𝓝 0))
    (herrorAnalytic : Tendsto (fun n => errorAnalytic n / windowScale n) atTop (𝓝 0))
    (hpositive : ∀ᶠ n in atTop, 0 < windowValue n)
    (harithmetic : ∀ᶠ n in atTop,
      Real.log (windowNormalizer n : ℝ) ≤ A * windowScale n + errorArithmetic n)
    (hanalytic : ∀ᶠ n in atTop,
      Real.log (windowValue n) ≤ -B * windowScale n + errorAnalytic n) :
    Irrational (riemannZeta 5).re := by
  apply irrational_realZeta_five_iff.mp
  rintro ⟨q, hq⟩
  have hb : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hbZ : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hx : realZeta 5 = (q.num : ℝ) / (q.den : ℝ) := by
    rw [← hq]
    exact Rat.cast_def q
  have hlinear := linear_over_windowScale_limit (24 * Real.log (q.den : ℝ))
  have herr := (herrorArithmetic.add herrorAnalytic).add hlinear
  simp only [add_zero] at herr
  have hsmall := herr.eventually (eventually_lt_nhds (sub_pos.mpr hgap))
  obtain ⟨n, hn, hp, hA, hB, hE⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and
      (hpositive.and (harithmetic.and (hanalytic.and hsmall)))).exists
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 0 < windowScale n := by dsimp [windowScale]; positivity
  have hQ : (0 : ℝ) < windowNormalizer n := by exact_mod_cast windowNormalizer_pos n
  let u : ℝ := (q.den : ℝ) ^ (24 * n) * ((windowNormalizer n : ℝ) * windowValue n)
  have huinteger : ∃ z : ℤ, u = z := by
    refine ⟨scaledEvalInt (windowIntegerPolynomial n) q.num q.den (24 * n), ?_⟩
    rw [scaledEvalInt_cast _ _ _ _ hbZ (windowIntegerPolynomial_degree n)]
    simp only [Int.cast_natCast]
    rw [← hx, windowIntegerPolynomial_eval]
  have hupos : 0 < u := mul_pos (pow_pos hb _) (mul_pos hQ hp)
  obtain ⟨z, hz⟩ := huinteger
  have hzpos : (0 : ℤ) < z := by rw [hz] at hupos; exact_mod_cast hupos
  have huge : 1 ≤ u := by rw [hz]; exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  have hlognonneg : 0 ≤ Real.log u := Real.log_nonneg huge
  have hlog : Real.log u =
      (24 * (n : ℝ)) * Real.log (q.den : ℝ) +
        Real.log (windowNormalizer n : ℝ) + Real.log (windowValue n) := by
    dsimp [u]
    rw [Real.log_mul (pow_ne_zero _ hb.ne') (mul_ne_zero hQ.ne' hp.ne'),
      Real.log_mul hQ.ne' hp.ne', Real.log_pow]
    push_cast
    ring
  have hE' : errorArithmetic n + errorAnalytic n +
      (24 * Real.log (q.den : ℝ)) * (n : ℝ) < (B - A) * windowScale n := by
    apply (div_lt_iff₀ hscale).mp
    simpa only [add_div] using hE
  rw [hlog] at hlognonneg
  nlinarith

#print axioms irrational_zeta5_of_normalized_decay
#print axioms linear_over_windowScale_limit
#print axioms irrational_zeta5_of_log_rate_bounds

end Zeta5.Endpoint
