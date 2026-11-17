import Zeta5.Analysis.AbelKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The truncated Abel transform and its Fubini bound

The full Abel transform is the external-field slope.  Truncating the positive
radial mixture can only decrease it.  These estimates also prove the joint
integrability needed to exchange the two integrations in the potential proof.
-/

open MeasureTheory Set Filter

namespace Zeta5.Analysis

noncomputable def equilibriumSlope (s t : ℝ) : ℝ :=
  Real.pi/4-Real.arctan t/2+Real.arctan (t/s)

lemma equilibriumSlope_continuous (s : ℝ) : Continuous (equilibriumSlope s) := by
  unfold equilibriumSlope
  fun_prop

lemma equilibriumSlope_le {s t : ℝ} (ht : 0 ≤ t) :
    equilibriumSlope s t ≤ 3*Real.pi/4 := by
  have h1 := Real.arctan_nonneg.mpr ht
  have h2 := Real.arctan_lt_pi_div_two (t/s)
  dsimp [equilibriumSlope]
  linarith

lemma profileMassSlope_abel_above (s : ℝ) {b t : ℝ} (ht : 0 ≤ t) (htb : t ≤ b) :
    IntervalIntegrable (fun a => profileMassSlope s a*abelKernel t a) volume t b ∧
      (∫ a in t..b, profileMassSlope s a*abelKernel t a) = 0 := by
  have heq : EqOn (fun a => profileMassSlope s a*abelKernel t a)
      (fun _ => (0 : ℝ)) (uIcc t b) := by
    rw [uIcc_of_le htb]
    intro a ha
    have hrad : t^2-a^2 ≤ 0 := by nlinarith [ha.1]
    simp [abelKernel, Real.sqrt_eq_zero_of_nonpos hrad]
  refine ⟨(intervalIntegrable_congr (heq.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const, ?_⟩
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

/-- A positive truncation of the actual Abel transform is bounded by the full
external-field slope; it equals that slope once the truncation passes `t`. -/
theorem profileMassSlope_abel_truncated (s : ℝ) (hs : 0 < s) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 < t) :
    IntervalIntegrable (fun a => profileMassSlope s a*abelKernel t a) volume 0 b ∧
      (∫ a in 0..b, profileMassSlope s a*abelKernel t a) ≤ equilibriumSlope s t ∧
      (t ≤ b → (∫ a in 0..b, profileMassSlope s a*abelKernel t a) = equilibriumSlope s t) := by
  obtain ⟨hi, hv⟩ := profileMassSlope_abel_integral hs ht
  change (∫ a in 0..t, profileMassSlope s a*abelKernel t a) = equilibriumSlope s t at hv
  by_cases hbt : b ≤ t
  · have hsub : uIcc (0 : ℝ) b ⊆ uIcc 0 t := by
      rw [uIcc_of_le hb, uIcc_of_le ht.le]
      exact Icc_subset_Icc le_rfl hbt
    refine ⟨hi.mono_set hsub, ?_, ?_⟩
    · rw [← hv]
      apply intervalIntegral.integral_mono_interval le_rfl hb hbt _ hi
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
      exact mul_nonneg (profileMassSlope_nonneg hs ha.1.le) (abelKernel_nonneg t a)
    · intro htb
      have heq : b = t := le_antisymm hbt htb
      simpa [heq] using hv
  · have htb : t ≤ b := le_of_not_ge hbt
    obtain ⟨htail, htailv⟩ := profileMassSlope_abel_above s ht.le htb
    have hsum := intervalIntegral.integral_add_adjacent_intervals hi htail
    rw [htailv, add_zero, hv] at hsum
    exact ⟨hi.trans htail, hsum.ge, fun _ => hsum.symm⟩

lemma profileMassSlope_abel_norm_integral (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) (t : ℝ) :
    (∫ a in Ioc (0 : ℝ) b, ‖profileMassSlope s a*abelKernel t a‖) =
      ∫ a in 0..b, profileMassSlope s a*abelKernel t a := by
  rw [intervalIntegral.integral_of_le hb]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro a ha
  exact Real.norm_of_nonneg
    (mul_nonneg (profileMassSlope_nonneg hs ha.1.le) (abelKernel_nonneg t a))

/-- The nonnegative two-variable kernel is jointly integrable on every compact
positive rectangle, despite its diagonal square-root singularity. -/
theorem profileMassSlope_abel_prod_integrable (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) :
    Integrable (fun p : ℝ × ℝ => profileMassSlope s p.1*abelKernel p.2 p.1)
      ((volume.restrict (Ioc 0 b)).prod (volume.restrict (Ioc 0 y))) := by
  have hm : Measurable (fun p : ℝ × ℝ => profileMassSlope s p.1*abelKernel p.2 p.1) := by
    unfold abelKernel
    exact ((profileMassSlope_continuous hs).measurable.comp measurable_fst).mul
      (by fun_prop)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact (profileMassSlope_abel_truncated s hs hb ht.1).1.1
  · apply (integrable_const (3*Real.pi/4 : ℝ)).mono'
      (hm.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      profileMassSlope_abel_norm_integral s hs hb]
    exact (profileMassSlope_abel_truncated s hs hb ht.1).2.1.trans (equilibriumSlope_le ht.1.le)

end Zeta5.Analysis
