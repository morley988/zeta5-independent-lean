import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
# The logarithmic potential of the arcsine distribution

The arcsine distribution is the real-part image of the uniform unit circle.
Factoring a quadratic on that circle reduces its logarithmic potential to the
already established circle average of `log ‖z-r‖`.  Equalities at logarithmic
zeros are handled as null exceptional sets, rather than by assigning a finite
value to the singular logarithm.
-/

open MeasureTheory Set Filter Metric Complex Real
open scoped ComplexConjugate

namespace Zeta5.Analysis

noncomputable def arcsinePotential (b y : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ => Real.log |y-b*z.re|) 0 1

lemma circle_quadratic_factor_identity {b y : ℝ} (hb : b ≠ 0)
    {r₁ r₂ z : ℂ} (hprod : r₁*r₂ = 1) (hsum : r₁+r₂ = (2*y/b : ℝ))
    (hz : ‖z‖ = 1) :
    (b/2 : ℝ) * ((z-r₁)*(z-r₂)) = ((b*z.re-y : ℝ) : ℂ)*z := by
  have hzconj : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzre : (z.re : ℂ)*2 = z+conj z := by
    apply Complex.ext <;> simp <;> ring
  calc
    (b/2 : ℝ) * ((z-r₁)*(z-r₂)) =
        (b : ℂ)/2*(z^2-(r₁+r₂)*z+r₁*r₂) := by push_cast; ring
    _ = (b : ℂ)/2*(z^2-(2*(y : ℂ)/(b : ℂ))*z+1) := by
      rw [hprod, hsum]
      push_cast
      rfl
    _ = ((b : ℂ)*(z+conj z)/2-y)*z := by
      rw [← hzconj]
      field_simp [Complex.ofReal_ne_zero.mpr hb]
      ring
    _ = ((b*z.re-y : ℝ) : ℂ)*z := by
      rw [← hzre]
      push_cast
      ring

lemma circle_log_real_part_factorization {b y : ℝ} (hb : 0 < b)
    {r₁ r₂ z : ℂ} (hprod : r₁*r₂ = 1) (hsum : r₁+r₂ = (2*y/b : ℝ))
    (hz : ‖z‖ = 1) (hz₁ : z ≠ r₁) (hz₂ : z ≠ r₂) :
    Real.log |y-b*z.re| = Real.log (b/2) + Real.log ‖z-r₁‖ + Real.log ‖z-r₂‖ := by
  have hid := congrArg norm (circle_quadratic_factor_identity hb.ne' hprod hsum hz)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one] at hid
  rw [abs_of_pos (div_pos hb (by norm_num))] at hid
  have hn₁ : ‖z-r₁‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₁)
  have hn₂ : ‖z-r₂‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₂)
  rw [abs_sub_comm y, ← hid]
  rw [Real.log_mul (ne_of_gt (div_pos hb (by norm_num))) (mul_ne_zero hn₁ hn₂),
    Real.log_mul hn₁ hn₂]
  ring

/-- General quadratic factorization formula for the real-part logarithm. -/
theorem arcsinePotential_factorization {b y : ℝ} (hb : 0 < b)
    {r₁ r₂ : ℂ} (hprod : r₁*r₂ = 1) (hsum : r₁+r₂ = (2*y/b : ℝ)) :
    CircleIntegrable (fun z : ℂ => Real.log |y-b*z.re|) 0 1 ∧
      arcsinePotential b y = Real.log (b/2) + Real.posLog ‖r₁‖ + Real.posLog ‖r₂‖ := by
  let g : ℂ → ℝ := fun z => Real.log (b/2) + Real.log ‖z-r₁‖ + Real.log ‖z-r₂‖
  have hg1 : CircleIntegrable
      (fun z : ℂ => Real.log (b/2) + Real.log ‖z-r₁‖) 0 1 :=
    (circleIntegrable_const _ _ _).add (circleIntegrable_log_norm_sub_const 1)
  have hg : CircleIntegrable g 0 1 :=
    hg1.add (circleIntegrable_log_norm_sub_const 1)
  have heq : (fun z : ℂ => Real.log |y-b*z.re|) =ᶠ[
      codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|)] g := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      compl_singleton_mem_codiscreteWithin r₁, compl_singleton_mem_codiscreteWithin r₂]
      with z hz hz₁ hz₂
    have hzn : ‖z‖ = 1 := by simpa only [abs_one, mem_sphere_iff_norm, sub_zero] using hz
    exact circle_log_real_part_factorization hb hprod hsum hzn hz₁ hz₂
  refine ⟨hg.congr_codiscreteWithin heq.symm, ?_⟩
  unfold arcsinePotential
  rw [circleAverage_congr_codiscreteWithin heq (by norm_num)]
  dsimp only [g]
  rw [circleAverage_fun_add hg1 (circleIntegrable_log_norm_sub_const 1),
    circleAverage_fun_add (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const 1),
    circleAverage_const, circleAverage_log_norm_sub_const_eq_posLog,
    circleAverage_log_norm_sub_const_eq_posLog]

/-- The arcsine potential is constant on its support. -/
theorem arcsinePotential_of_abs_le {b y : ℝ} (hb : 0 < b) (hy : |y| ≤ b) :
    CircleIntegrable (fun z : ℂ => Real.log |y-b*z.re|) 0 1 ∧
      arcsinePotential b y = Real.log (b/2) := by
  let x : ℝ := y/b
  let r : ℂ := ⟨x, Real.sqrt (1-x^2)⟩
  have hx : |x| ≤ 1 := by
    dsimp [x]
    rw [abs_div, abs_of_pos hb]
    exact (div_le_one hb).mpr hy
  have hx2 : x^2 ≤ 1 := by have hh := abs_le.mp hx; nlinarith
  have hsqrt : (Real.sqrt (1-x^2))^2 = 1-x^2 := Real.sq_sqrt (sub_nonneg.mpr hx2)
  have hrSq : Complex.normSq r = 1 := by
    dsimp [r, Complex.normSq]
    nlinarith
  have hr : ‖r‖ = 1 := by
    rw [Complex.norm_def, hrSq]
    norm_num
  have hprod : r*conj r = 1 := by rw [Complex.mul_conj, hrSq]; norm_num
  have hsum : r+conj r = (2*y/b : ℝ) := by
    apply Complex.ext <;> simp [r, x] <;> ring
  obtain ⟨hi, hv⟩ := arcsinePotential_factorization hb hprod hsum
  refine ⟨hi, ?_⟩
  simpa [hr, Complex.norm_conj] using hv

/-- Outside its support the arcsine potential has the elementary square-root
formula. -/
theorem arcsinePotential_of_le {b y : ℝ} (hb : 0 < b) (hy : b ≤ y) :
    CircleIntegrable (fun z : ℂ => Real.log |y-b*z.re|) 0 1 ∧
      arcsinePotential b y = Real.log ((y+Real.sqrt (y^2-b^2))/2) := by
  let d : ℝ := Real.sqrt (y^2-b^2)
  let r : ℝ := (y+d)/b
  have hypos : 0 < y := lt_of_lt_of_le hb hy
  have hdnonneg : 0 ≤ d := Real.sqrt_nonneg _
  have hdsq : d^2 = y^2-b^2 := Real.sq_sqrt (by nlinarith)
  have hr : 1 ≤ r := by
    apply (le_div_iff₀ hb).mpr
    linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsumr : r+r⁻¹ = 2*y/b := by
    dsimp [r]
    field_simp
    nlinarith
  have hprod : (r : ℂ)*(r : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hrpos.ne')
  have hsum : (r : ℂ)+(r : ℂ)⁻¹ = (2*y/b : ℝ) := by
    exact_mod_cast hsumr
  obtain ⟨hi, hv⟩ := arcsinePotential_factorization hb hprod hsum
  refine ⟨hi, ?_⟩
  have hnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hrpos]
  have hpinv : Real.posLog ‖(r : ℂ)⁻¹‖ = 0 := by
    apply (Real.posLog_eq_zero_iff _).mpr
    rw [abs_of_nonneg (norm_nonneg _), norm_inv, hnorm]
    exact inv_le_one_of_one_le₀ hr
  rw [hnorm, Real.posLog_eq_log (by simpa [abs_of_pos hrpos] using hr), hpinv, add_zero] at hv
  rw [hv, ← Real.log_mul (ne_of_gt (div_pos hb (by norm_num))) hrpos.ne']
  congr 1
  dsimp [r, d]
  field_simp

lemma arcsinePotential_zero {b : ℝ} (hb : 0 < b) :
    arcsinePotential b 0 = Real.log (b/2) :=
  (arcsinePotential_of_abs_le hb (by simpa using hb.le)).2

lemma arcsinePotential_circleIntegrable_nonneg {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y) :
    CircleIntegrable (fun z : ℂ => Real.log |y-b*z.re|) 0 1 := by
  by_cases h : y ≤ b
  · exact (arcsinePotential_of_abs_le hb (by simpa [abs_of_nonneg hy] using h)).1
  · exact (arcsinePotential_of_le hb (le_of_not_ge h)).1

/-- A real-part circle average is the corresponding cosine average on one
half-circle. -/
lemma circleAverage_realPart_eq_halfAngle (f : ℝ → ℝ)
    (hf : CircleIntegrable (fun z : ℂ => f z.re) 0 1) :
    IntervalIntegrable (fun θ : ℝ => f (Real.cos θ)) volume 0 Real.pi ∧
      Real.circleAverage (fun z : ℂ => f z.re) 0 1 =
        (1/Real.pi) * (∫ θ in 0..Real.pi, f (Real.cos θ)) := by
  have hfull : IntervalIntegrable (fun θ : ℝ => f (Real.cos θ)) volume 0 (2*Real.pi) := by
    simpa only [CircleIntegrable, circleMap_zero_re, one_mul] using hf
  have hleft := hfull.mono_set (show Set.uIcc (0 : ℝ) Real.pi ⊆ Set.uIcc 0 (2*Real.pi) by
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
    intro θ hθ
    exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
  have hright := hfull.mono_set
    (show Set.uIcc Real.pi (2*Real.pi) ⊆ Set.uIcc 0 (2*Real.pi) by
      rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2*Real.pi),
        uIcc_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
      intro θ hθ
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have href := intervalIntegral.integral_comp_sub_left (fun θ : ℝ => f (Real.cos θ))
    (2*Real.pi) (a := 0) (b := Real.pi)
  simp only [Real.cos_two_pi_sub, sub_zero, show 2*Real.pi-Real.pi = Real.pi by ring] at href
  have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← href] at hsum
  refine ⟨hleft, ?_⟩
  simp only [Real.circleAverage, circleMap_zero_re, one_mul, smul_eq_mul]
  rw [← hsum]
  field_simp
  ring

lemma arcsinePotential_halfAngle {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y) :
    IntervalIntegrable (fun θ : ℝ => Real.log |y-b*Real.cos θ|) volume 0 Real.pi ∧
      arcsinePotential b y =
        (1/Real.pi) * (∫ θ in 0..Real.pi, Real.log |y-b*Real.cos θ|) :=
  circleAverage_realPart_eq_halfAngle (fun x : ℝ => Real.log |y-b*x|)
    (arcsinePotential_circleIntegrable_nonneg hb hy)

/-- Squaring the cosine image doubles its symmetric logarithmic potential. -/
theorem arcsineSquared_halfAngle {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y) :
    IntervalIntegrable (fun θ : ℝ => Real.log |y^2-(b*Real.cos θ)^2|) volume 0 Real.pi ∧
      (1/Real.pi)*(∫ θ in 0..Real.pi, Real.log |y^2-(b*Real.cos θ)^2|) =
        2*arcsinePotential b y := by
  obtain ⟨hm, hW⟩ := arcsinePotential_halfAngle hb hy
  have hp : IntervalIntegrable (fun θ : ℝ => Real.log |y+b*Real.cos θ|) volume 0 Real.pi := by
    simpa [Real.cos_pi_sub] using (hm.comp_sub_left Real.pi).symm
  have hpint : (∫ θ in 0..Real.pi, Real.log |y+b*Real.cos θ|) =
      ∫ θ in 0..Real.pi, Real.log |y-b*Real.cos θ| := by
    simpa [Real.cos_pi_sub] using
      (intervalIntegral.integral_comp_sub_left (fun θ : ℝ => Real.log |y-b*Real.cos θ|)
        Real.pi (a := 0) (b := Real.pi))
  have ham : AnalyticOnNhd ℝ (fun θ : ℝ => y-b*Real.cos θ) univ := fun _ _ => by fun_prop
  have hap : AnalyticOnNhd ℝ (fun θ : ℝ => y+b*Real.cos θ) univ := fun _ _ => by fun_prop
  have hmzero : y-b*Real.cos Real.pi ≠ 0 := by simp; linarith
  have hpzero : y+b*Real.cos 0 ≠ 0 := by simp; linarith
  have heq : (fun θ : ℝ => Real.log |y^2-(b*Real.cos θ)^2|) =ᶠ[
      codiscreteWithin (Set.uIoc (0 : ℝ) Real.pi)]
      (fun θ : ℝ => Real.log |y-b*Real.cos θ| + Real.log |y+b*Real.cos θ|) := by
    apply codiscreteWithin_mono (by tauto : Set.uIoc (0 : ℝ) Real.pi ⊆ univ)
    filter_upwards [ham.preimage_zero_mem_codiscrete hmzero,
      hap.preimage_zero_mem_codiscrete hpzero] with θ hminus hplus
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hminus hplus
    rw [show y^2-(b*Real.cos θ)^2 = (y-b*Real.cos θ)*(y+b*Real.cos θ) by ring,
      abs_mul, Real.log_mul (abs_ne_zero.mpr hminus) (abs_ne_zero.mpr hplus)]
  have hsq : IntervalIntegrable (fun θ : ℝ => Real.log |y^2-(b*Real.cos θ)^2|)
      volume 0 Real.pi :=
    IntervalIntegrable.congr_codiscreteWithin heq.symm (hm.add hp)
  refine ⟨hsq, ?_⟩
  rw [intervalIntegral.integral_congr_codiscreteWithin heq,
    intervalIntegral.integral_add hm hp, hpint, hW]
  ring

end Zeta5.Analysis
