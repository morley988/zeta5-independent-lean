import Zeta5.Analysis.AuxiliaryMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Elementary Abel integrals for the equilibrium measure

The singular endpoint kernels are proved integrable by exhibiting continuous
primitives with nonnegative derivatives.  No improper-integral convergence is
left as a hypothesis.
-/

open MeasureTheory Set

namespace Zeta5.Analysis

noncomputable def abelKernel (t a : ℝ) : ℝ := (Real.sqrt (t^2-a^2))⁻¹

lemma abelKernel_nonneg (t a : ℝ) : 0 ≤ abelKernel t a := by
  unfold abelKernel
  positivity

lemma sqrt_one_sub_div_sq {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ t^2-a^2) :
    Real.sqrt (1-(a/t)^2) = Real.sqrt (t^2-a^2)/t := by
  rw [show 1-(a/t)^2 = (t^2-a^2)/t^2 by field_simp <;> ring,
    Real.sqrt_div ha, Real.sqrt_sq ht.le]

lemma arcsin_scaled_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) t) :
    HasDerivAt (fun x : ℝ => Real.arcsin (x/t)) (abelKernel t a) a := by
  have hlo : -1 < a/t := lt_trans (by norm_num : (-1 : ℝ) < 0) (div_pos ha.1 ht)
  have hhi : a/t < 1 := (div_lt_one ht).mpr ha.2
  have hrad : 0 < t^2-a^2 := by nlinarith [ha.1, ha.2]
  have hh := (Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)).comp a
    ((hasDerivAt_id a).div_const t)
  convert! hh using 1
  rw [sqrt_one_sub_div_sq ht hrad.le]
  dsimp [abelKernel]
  field_simp

lemma integral_of_nonnegative_derivative {a b : ℝ} {F f : ℝ → ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) = F b-F a := by
  have hi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (intervalIntegral.integrableOn_deriv_of_nonneg hF hderiv hf)
  exact ⟨hi, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hderiv hi⟩

/-- The basic Abel integral, including endpoint integrability. -/
theorem integral_abelKernel {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (abelKernel t) volume 0 t ∧
      (∫ a in 0..t, abelKernel t a) = Real.pi/2 := by
  have hc : Continuous (fun a : ℝ => Real.arcsin (a/t)) := by fun_prop
  obtain ⟨hi, hv⟩ := integral_of_nonnegative_derivative ht.le hc.continuousOn
    (fun a ha => arcsin_scaled_hasDerivAt ht ha) (fun a _ => abelKernel_nonneg t a)
  refine ⟨hi, ?_⟩
  simpa [ht.ne'] using hv

lemma arctan_eq_arcsin_scaled {c t : ℝ} (hc : 0 < c) :
    Real.arctan (t/c) = Real.arcsin (t/Real.sqrt (c^2+t^2)) := by
  rw [Real.arctan_eq_arcsin]
  have hroot : Real.sqrt (1+(t/c)^2) = Real.sqrt (c^2+t^2)/c := by
    rw [show 1+(t/c)^2 = (c^2+t^2)/c^2 by field_simp <;> ring,
      Real.sqrt_div (by positivity), Real.sqrt_sq hc.le]
  rw [hroot]
  congr 1
  field_simp

lemma weighted_abel_primitive_hasDerivAt {c t a : ℝ}
    (hc : 0 < c) (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) t) :
    HasDerivAt
      (fun x : ℝ => -Real.arcsin (Real.sqrt (t^2-x^2)/Real.sqrt (c^2+t^2)))
      (a/Real.sqrt (c^2+a^2)*abelKernel t a) a := by
  let D : ℝ := Real.sqrt (c^2+t^2)
  let r : ℝ := Real.sqrt (t^2-a^2)
  let A : ℝ := Real.sqrt (c^2+a^2)
  have hrad : 0 < t^2-a^2 := by nlinarith [ha.1, ha.2]
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : 0 < r := Real.sqrt_pos.mpr hrad
  have hA : 0 < A := by dsimp [A]; positivity
  have hDsq : D^2 = c^2+t^2 := Real.sq_sqrt (by positivity)
  have hrsq : r^2 = t^2-a^2 := Real.sq_sqrt hrad.le
  have hrD : r < D := by nlinarith [sq_pos_of_pos hc]
  have hlo : -1 < r/D := lt_trans (by norm_num : (-1 : ℝ) < 0) (div_pos hr hD)
  have hhi : r/D < 1 := (div_lt_one hD).mpr hrD
  have hroot : Real.sqrt (1-(r/D)^2) = A/D := by
    rw [show 1-(r/D)^2 = (c^2+a^2)/D^2 by
      field_simp
      nlinarith [hDsq, hrsq], Real.sqrt_div (by positivity), Real.sqrt_sq hD.le]
  have hderivroot := ((hasDerivAt_const a (t^2)).sub ((hasDerivAt_id a).pow 2)).sqrt hrad.ne'
  have hh := ((Real.hasDerivAt_arcsin (ne_of_gt hlo) (ne_of_lt hhi)).comp a
    (hderivroot.div_const D)).neg
  convert! hh using 1
  change a/A*r⁻¹ = -(1/Real.sqrt (1-(r/D)^2) * ((0-2*a^(2-1)*1)/(2*r)/D))
  rw [hroot]
  norm_num
  field_simp

/-- The weighted Abel integral that produces the arctangent terms in the
external field. -/
theorem integral_weighted_abelKernel {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    IntervalIntegrable (fun a => a/Real.sqrt (c^2+a^2)*abelKernel t a) volume 0 t ∧
      (∫ a in 0..t, a/Real.sqrt (c^2+a^2)*abelKernel t a) = Real.arctan (t/c) := by
  have hcont : Continuous
      (fun a : ℝ => -Real.arcsin (Real.sqrt (t^2-a^2)/Real.sqrt (c^2+t^2))) := by
    fun_prop
  obtain ⟨hi, hv⟩ := integral_of_nonnegative_derivative ht.le hcont.continuousOn
    (fun a ha => weighted_abel_primitive_hasDerivAt hc ht ha)
    (fun a ha => mul_nonneg (div_nonneg ha.1.le (Real.sqrt_nonneg _))
      (abelKernel_nonneg t a))
  refine ⟨hi, ?_⟩
  rw [arctan_eq_arcsin_scaled hc]
  simpa [Real.sqrt_sq ht.le] using hv

/-- The actual profile mass derivative has the Abel transform required for the
potential equilibrium identity. -/
theorem profileMassSlope_abel_integral {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IntervalIntegrable (fun a => profileMassSlope s a*abelKernel t a) volume 0 t ∧
      (∫ a in 0..t, profileMassSlope s a*abelKernel t a) =
        Real.pi/4-Real.arctan t/2+Real.arctan (t/s) := by
  obtain ⟨h0, h0v⟩ := integral_abelKernel ht
  obtain ⟨h1, h1v⟩ := integral_weighted_abelKernel (by norm_num : (0 : ℝ) < 1) ht
  obtain ⟨hsI, hsv⟩ := integral_weighted_abelKernel hs ht
  have heq : (fun a => profileMassSlope s a*abelKernel t a) =
      (fun a => (1/2 : ℝ)*abelKernel t a -
        (1/2 : ℝ)*(a/Real.sqrt (1^2+a^2)*abelKernel t a) +
        a/Real.sqrt (s^2+a^2)*abelKernel t a) := by
    funext a
    dsimp [profileMassSlope]
    norm_num
    ring
  rw [heq]
  have hi := ((h0.const_mul (1/2)).sub (h1.const_mul (1/2))).add hsI
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_add ((h0.const_mul (1/2)).sub (h1.const_mul (1/2))) hsI,
    intervalIntegral.integral_sub (h0.const_mul (1/2)) (h1.const_mul (1/2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h0v, h1v, hsv]
  norm_num
  ring

end Zeta5.Analysis
