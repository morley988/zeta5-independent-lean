import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform logarithmic truncation from a small-ball estimate

The fourth power in the hypothesis is a convenient form of a Hölder exponent
`1/4`.  It avoids a minimum length condition on quantile cells: first truncate
the logarithmic kernel, apply bounded-variation quadrature, then use the
estimate here to remove the truncation.
-/

open MeasureTheory Set Filter

namespace Zeta5.Analysis

noncomputable def logTruncationLoss (δ v w : ℝ) : ℝ :=
  max 0 (Real.log δ - Real.log |v - w|)

lemma logTruncationLoss_nonneg (δ v w : ℝ) :
    0 ≤ logTruncationLoss δ v w := le_max_left _ _

lemma logTruncationLoss_measurable (δ v : ℝ) :
    Measurable (logTruncationLoss δ v) := by
  unfold logTruncationLoss
  fun_prop

lemma logTruncationLoss_tail_subset {ε v t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    {w : ℝ | t < logTruncationLoss (ε ^ 4) v w} ⊆
      {w : ℝ | |v - w| < (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4} := by
  intro w hw
  have hδ : 0 < ε ^ 4 := pow_pos hε _
  have hr : 0 < (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4 := by positivity
  by_cases hd : |v - w| = 0
  · simpa [hd] using hr
  have hdpos : 0 < |v - w| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
  have hlog : t < Real.log (ε ^ 4) - Real.log |v - w| := by
    exact (lt_max_iff.mp hw).resolve_left (not_lt_of_ge ht.le)
  have hexp : Real.exp t < ε ^ 4 / |v - w| := by
    have hh := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_sub, Real.exp_log hδ, Real.exp_log hdpos] at hh
    exact hh
  have hdist : |v - w| < ε ^ 4 / Real.exp t := by
    exact (lt_div_iff₀ (Real.exp_pos _)).mpr
      (by simpa [mul_comm] using (lt_div_iff₀ hdpos).mp hexp)
  have hid : (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4 = ε ^ 4 / Real.exp t := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (4 : ℝ) * (-(1 / 4 : ℝ) * t) = -t by ring, Real.exp_neg]
    rfl
  rw [hid]
  exact hdist

/-- The integral of the exponential majorant appearing in the layer-cake proof. -/
lemma integral_logTruncation_majorant (C ε : ℝ) :
    (∫ t in Ioi (0 : ℝ), C * ε * Real.exp (-(1 / 4 : ℝ) * t)) = 4 * C * ε := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0)]
  norm_num
  ring

lemma logTruncation_majorant_integrable (C ε : ℝ) :
    IntegrableOn (fun t : ℝ => C * ε * Real.exp (-(1 / 4 : ℝ) * t)) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0).const_mul _

/-- A Hölder small-ball estimate gives both integrability and a quantitative
bound for the error caused by truncating a logarithmic singularity. -/
theorem logTruncationLoss_integrable_and_integral_le
    (μ : Measure ℝ) {C ε v : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hsmall : ∀ ρ : ℝ, 0 < ρ →
      μ {w : ℝ | |v - w| < ρ ^ 4} ≤ ENNReal.ofReal (C * ρ)) :
    Integrable (logTruncationLoss (ε ^ 4) v) μ ∧
      (∫ w, logTruncationLoss (ε ^ 4) v w ∂μ) ≤ 4 * C * ε := by
  let f := logTruncationLoss (ε ^ 4) v
  let g : ℝ → ℝ := fun t => C * ε * Real.exp (-(1 / 4 : ℝ) * t)
  have hfnonneg : 0 ≤ᵐ[μ] f := Eventually.of_forall (logTruncationLoss_nonneg _ _)
  have hfmeas : Measurable f := logTruncationLoss_measurable _ _
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by dsimp [g]; positivity
  have hgint : Integrable g (volume.restrict (Ioi 0)) :=
    logTruncation_majorant_integrable C ε
  have htail : ∀ t ∈ Ioi (0 : ℝ), μ {w | t < f w} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    calc
      μ {w | t < f w} ≤ μ {w : ℝ | |v - w| <
          (ε * Real.exp (-(1 / 4 : ℝ) * t)) ^ 4} :=
        measure_mono (logTruncationLoss_tail_subset hε ht)
      _ ≤ ENNReal.ofReal (C * (ε * Real.exp (-(1 / 4 : ℝ) * t))) :=
        hsmall _ (mul_pos hε (Real.exp_pos _))
      _ = ENNReal.ofReal (g t) := by congr 1; dsimp [g]; ring
  have hle : (∫⁻ w, ENNReal.ofReal (f w) ∂μ) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (g t) := by
    rw [lintegral_eq_lintegral_meas_lt μ hfnonneg hfmeas.aemeasurable]
    exact lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi htail)
  have hfinite : (∫⁻ w, ENNReal.ofReal (f w) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hgint.lintegral_lt_top.ne hle
  have hfint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfmeas.aestronglyMeasurable hfnonneg).mp hfinite
  refine ⟨hfint, ?_⟩
  have hreal := ENNReal.toReal_mono hgint.lintegral_lt_top.ne hle
  rw [← integral_eq_lintegral_of_nonneg_ae hfnonneg hfmeas.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hgnonneg)
      hgint.aestronglyMeasurable] at hreal
  dsimp only [g] at hreal
  rw [integral_logTruncation_majorant] at hreal
  exact hreal

end Zeta5.Analysis
