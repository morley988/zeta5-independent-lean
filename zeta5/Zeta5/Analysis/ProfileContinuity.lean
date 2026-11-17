import Zeta5.Analysis.ProfileShape
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Continuity of the analytic profile at zero -/

namespace Zeta5.Analysis

noncomputable section

theorem profileMass_rationalized {s b : ℝ} (hs : 0 < s) :
    profileMass s b = b / 2 +
      b ^ 2 / (s + Real.sqrt (s ^ 2 + b ^ 2)) -
      b ^ 2 / (2 * (1 + Real.sqrt (1 + b ^ 2))) := by
  have hc : 0 < s + Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have ha : 0 < 1 + Real.sqrt (1 + b ^ 2) := by positivity
  have hc_sq := Real.sq_sqrt (show 0 ≤ s ^ 2 + b ^ 2 by positivity)
  have ha_sq := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hC : Real.sqrt (s ^ 2 + b ^ 2) - s =
      b ^ 2 / (s + Real.sqrt (s ^ 2 + b ^ 2)) := by
    apply (eq_div_iff hc.ne').2
    nlinarith
  have hA : Real.sqrt (1 + b ^ 2) - 1 =
      b ^ 2 / (1 + Real.sqrt (1 + b ^ 2)) := by
    apply (eq_div_iff ha.ne').2
    nlinarith
  calc
    profileMass s b = b / 2 + (Real.sqrt (s ^ 2 + b ^ 2) - s) -
        (Real.sqrt (1 + b ^ 2) - 1) / 2 := by dsimp [profileMass]; ring
    _ = _ := by rw [hC, hA]; field_simp <;> ring

theorem profileMass_mul_log_formula {s b : ℝ} (hs : 0 < s) :
    profileMass s b * Real.log b =
      (b * Real.log b) / 2 +
      b * (b * Real.log b) / (s + Real.sqrt (s ^ 2 + b ^ 2)) -
      b * (b * Real.log b) / (2 * (1 + Real.sqrt (1 + b ^ 2))) := by
  rw [profileMass_rationalized hs]
  ring

theorem profileMass_mul_log_continuous (s : ℝ) (hs : 0 < s) :
    Continuous (fun b : ℝ => profileMass s b * Real.log b) := by
  have hC : Continuous (fun b : ℝ => s + Real.sqrt (s ^ 2 + b ^ 2)) :=
    continuous_const.add (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
  have hA : Continuous (fun b : ℝ => 2 * (1 + Real.sqrt (1 + b ^ 2))) :=
    (continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.add (continuous_id.pow 2)))).const_mul 2
  have ht := ((Real.continuous_mul_log.div_const 2).add
    ((continuous_id.mul Real.continuous_mul_log).div hC (fun b => by positivity))).sub
    ((continuous_id.mul Real.continuous_mul_log).div hA (fun b => by positivity))
  exact ht.congr fun b => (profileMass_mul_log_formula hs).symm

theorem analyticProfile_continuousOn (s : ℝ) (hs : 0 < s) :
    ContinuousOn (analyticProfile s hs) (Set.Ici 0) := by
  have hb := profileEndpoint_continuous s hs
  have hf₁ : ContinuousOn (fun u : ℝ => 4 * u * Real.log (profileEndpoint s hs u))
      (Set.Ici 0) := by
    have h := ((profileMass_mul_log_continuous s hs).comp hb).const_mul 4
    apply h.continuousOn.congr
    intro u hu
    dsimp only [Function.comp_apply]
    rw [profileMass_endpoint s hs hu]
    ring
  have hf₂ : Continuous (fun u : ℝ => 4 * (s + u) * Real.log (4 * (s + u))) :=
    Real.continuous_mul_log.comp ((continuous_const.add continuous_id).const_mul 4)
  have hc : Continuous (fun u : ℝ => s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2)) :=
    continuous_const.add (Real.continuous_sqrt.comp (continuous_const.add (hb.pow 2)))
  have hf₃ := (hc.log (fun u => by positivity)).const_mul (4 * s)
  have ha : Continuous (fun u : ℝ => (1 + Real.sqrt (1 + (profileEndpoint s hs u) ^ 2)) / 2) :=
    (continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.add (hb.pow 2)))).div_const 2
  have hf₄ := (ha.log (fun u => by positivity)).const_mul 2
  exact ((hf₁.sub hf₂.continuousOn).add hf₃.continuousOn).sub hf₄.continuousOn

theorem analyticSaving_continuousOn (s : ℝ) (hs : 0 < s) :
    ContinuousOn (analyticSaving s hs) (Set.Ici 0) :=
  (analyticProfile_continuousOn s hs).neg

theorem analyticProfile_strictConvexOn_nonneg (s : ℝ) (hs : 0 < s) :
    StrictConvexOn ℝ (Set.Ici 0) (analyticProfile s hs) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0)
    (analyticProfile_continuousOn s hs)
  intro u hu v hv huv
  have hu' : 0 < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
  have hv' : 0 < v := by simpa only [interior_Ici, Set.mem_Ioi] using hv
  rw [(analyticProfile_hasDerivAt s hs hu').deriv,
    (analyticProfile_hasDerivAt s hs hv').deriv]
  exact analyticProfileSlope_strictMonoOn s hs hu' hv' huv

theorem analyticSaving_strictConcaveOn_nonneg (s : ℝ) (hs : 0 < s) :
    StrictConcaveOn ℝ (Set.Ici 0) (analyticSaving s hs) :=
  (analyticProfile_strictConvexOn_nonneg s hs).neg

theorem analyticSaving_nonneg (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ analyticSaving s hs u := by
  rcases hu.eq_or_lt with rfl | hpos
  · rw [analyticSaving_zero]
    positivity
  · exact (analyticSaving_pos s hs hpos).le

end

end Zeta5.Analysis
