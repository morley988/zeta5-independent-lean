import Zeta5.Reuse.ThetaAsymptotic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed affine prime summation on fixed intervals

The prime number theorem is supplied as the explicit hypothesis
`Tendsto (fun x => Chebyshev.theta x / x) atTop (nhds 1)`.
All subsequent summation and integration steps are proved here for the actual
Chebyshev function and actual prime sums. The old four-value project proved
only the finite step-weight interface; the affine bridge is new.
-/

noncomputable section
namespace Zeta5.Reuse.PrimeAffine
open Filter MeasureTheory Finset
open scoped Topology Chebyshev

theorem theta_scaled_integral_limit
    (htheta : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ t in a..b, θ (t * n) / (n : ℝ))
      atTop (𝓝 ((b ^ 2 - a ^ 2) / 2)) := by
  have hi : Tendsto (fun n : ℕ => ∫ t in a..b, θ (t * n) / (n : ℝ))
      atTop (𝓝 (∫ t in a..b, t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => Real.log 4 * b)
    · filter_upwards [] with n
      exact ((Chebyshev.theta_mono.measurable.comp
        (measurable_id.mul_const (n : ℝ))).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      filter_upwards [] with t ht
      have ht' : t ∈ Set.Ioc a b := by simpa [Set.uIoc_of_le hab] using ht
      have htpos : 0 < t := ha.trans ht'.1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Chebyshev.theta_nonneg _) hnpos.le)]
      calc
        θ (t * n) / (n : ℝ) ≤ Real.log 4 * t := by
          apply (div_le_iff₀ hnpos).mpr
          simpa only [mul_assoc] using
            Chebyshev.theta_le_log4_mul_x (mul_nonneg htpos.le hnpos.le)
        _ ≤ Real.log 4 * b := mul_le_mul_of_nonneg_left ht'.2 hlog
    · exact intervalIntegrable_const
    · filter_upwards [] with t ht
      have ht' : t ∈ Set.Ioc a b := by simpa [Set.uIoc_of_le hab] using ht
      exact (ThetaAsymptotic.scaled_limit θ htheta t (ha.trans ht'.1)).comp
        tendsto_natCast_atTop_atTop
  simpa only [integral_id] using hi

/-- The actual logarithmically weighted prime sum on `(a*n,b*n]`, divided
by `n`. The coefficients `c` and `d` are unrestricted real numbers. -/
def primeAffineSum (a b c d : ℝ) (n : ℕ) : ℝ :=
  (∑ p ∈ (Finset.Ioc ⌊a * n⌋₊ ⌊b * n⌋₊).filter Nat.Prime,
    (c + d * ((p : ℝ) / (n : ℝ))) * Real.log p) / (n : ℝ)

theorem primeAffineSum_identity (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (n : ℕ) (hn : 0 < n) :
    primeAffineSum a b c d n =
      (c + d * b) * (θ (b * n) / (n : ℝ)) -
        (c + d * a) * (θ (a * n) / (n : ℝ)) -
        d * (∫ t in a..b, θ (t * n) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have han : 0 ≤ a * (n : ℝ) := mul_nonneg ha hnR.le
  have habn : a * (n : ℝ) ≤ b * (n : ℝ) := mul_le_mul_of_nonneg_right hab hnR.le
  let primeLog : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  let f : ℝ → ℝ := fun t => c + d * (t / (n : ℝ))
  have hf (t : ℝ) : HasDerivAt f (d / (n : ℝ)) t := by
    simpa [f, div_eq_mul_inv, mul_assoc] using
      (((hasDerivAt_id t).div_const (n : ℝ)).const_mul d).const_add c
  have hd : deriv f = fun _ => d / (n : ℝ) := funext (fun t => (hf t).deriv)
  have hs (x : ℝ) : (∑ k ∈ Icc 0 ⌊x⌋₊, primeLog k) = θ x := by
    simp [primeLog, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have habel := sum_mul_eq_sub_sub_integral_mul primeLog (f := f) han habn
    (fun t _ => (hf t).differentiableAt) (by
      rw [hd]
      exact continuous_const.integrableOn_Icc)
  simp_rw [hs, hd] at habel
  rw [← intervalIntegral.integral_of_le habn, intervalIntegral.integral_const_mul] at habel
  have hsum :
      (∑ p ∈ (Finset.Ioc ⌊a * n⌋₊ ⌊b * n⌋₊).filter Nat.Prime,
        (c + d * ((p : ℝ) / (n : ℝ))) * Real.log p) =
      (c + d * b) * θ (b * n) - (c + d * a) * θ (a * n) -
        d / (n : ℝ) * (∫ t in a * n..b * n, θ t) := by
    simpa [f, primeLog, Finset.sum_filter, mul_ite, hnR.ne'] using habel
  unfold primeAffineSum
  rw [hsum, ← intervalIntegral.smul_integral_comp_mul_right θ (n : ℝ),
    smul_eq_mul, intervalIntegral.integral_div]
  field_simp

theorem primeAffineSum_limit_of_theta
    (htheta : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
    (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (primeAffineSum a b c d) atTop
      (𝓝 (c * (b - a) + d * (b ^ 2 - a ^ 2) / 2)) := by
  have hb : 0 < b := ha.trans_le hab
  have htA := (ThetaAsymptotic.scaled_limit θ htheta a ha).comp tendsto_natCast_atTop_atTop
  have htB := (ThetaAsymptotic.scaled_limit θ htheta b hb).comp tendsto_natCast_atTop_atTop
  have hI := theta_scaled_integral_limit htheta a b ha hab
  have ht := ((htB.const_mul (c + d * b)).sub (htA.const_mul (c + d * a))).sub
    (hI.const_mul d)
  have he : (c + d * b) * b - (c + d * a) * a - d * ((b ^ 2 - a ^ 2) / 2) =
      c * (b - a) + d * (b ^ 2 - a ^ 2) / 2 := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (primeAffineSum_identity a b c d ha.le hab n hn).symm

theorem prime_interval_membership (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (n p : ℕ) :
    p ∈ (Finset.Ioc ⌊a * n⌋₊ ⌊b * n⌋₊).filter Nat.Prime ↔
      p.Prime ∧ a * (n : ℝ) < p ∧ (p : ℝ) ≤ b * n := by
  have han : 0 ≤ a * (n : ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
  have hbn : 0 ≤ b * (n : ℝ) := mul_nonneg (ha.trans hab) (Nat.cast_nonneg _)
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt han, Nat.le_floor_iff hbn]
  tauto

theorem integral_affine (a b c d : ℝ) :
    (∫ t in a..b, c + d * t) = c * (b - a) + d * (b ^ 2 - a ^ 2) / 2 := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume a b := intervalIntegrable_const
  have hd : IntervalIntegrable (fun t : ℝ => d * t) volume a b :=
    ((continuous_const : Continuous (fun _ : ℝ => d)).mul continuous_id).intervalIntegrable a b
  rw [intervalIntegral.integral_add hc hd,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

theorem primeAffineSum_integral_limit_of_theta
    (htheta : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
    (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (primeAffineSum a b c d) atTop (𝓝 (∫ t in a..b, c + d * t)) := by
  rw [integral_affine]
  exact primeAffineSum_limit_of_theta htheta a b c d ha hab

/-- A finite collection of signed affine pieces. Disjointness is needed only
when identifying this sum with a separately defined piecewise profile. -/
theorem finite_primeAffineSum_limit_of_theta
    (htheta : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1))
    {ι : Type*} [Fintype ι] (a b c d : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun n : ℕ => ∑ i : ι, primeAffineSum (a i) (b i) (c i) (d i) n) atTop
      (𝓝 (∑ i : ι, (c i * (b i - a i) + d i * (b i ^ 2 - a i ^ 2) / 2))) := by
  apply tendsto_finsetSum
  intro i _
  exact primeAffineSum_limit_of_theta htheta (a i) (b i) (c i) (d i) (ha i) (hab i)

#print axioms theta_scaled_integral_limit
#print axioms primeAffineSum_identity
#print axioms primeAffineSum_limit_of_theta
#print axioms prime_interval_membership
#print axioms primeAffineSum_integral_limit_of_theta
#print axioms finite_primeAffineSum_limit_of_theta

end Zeta5.Reuse.PrimeAffine
