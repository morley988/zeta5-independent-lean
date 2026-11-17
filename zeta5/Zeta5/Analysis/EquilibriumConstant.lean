import Zeta5.Analysis.MixtureEquilibrium
import Zeta5.Analysis.ProfileContinuity

/-!
# The equilibrium constant is the certified analytic profile

The integration constant is identified by differentiating the already proved
profile formula and applying the fundamental theorem of calculus at zero.
This avoids treating the explicit logarithmic constant as an assumption.
-/

open MeasureTheory Set

namespace Zeta5.Analysis

noncomputable def profileEquilibrium (s : ℝ) (hs : 0 < s) (u : ℝ) : ℝ :=
  analyticProfile s hs u + 2 - 4*(s+u) + 4*(s+u)*Real.log (2*(s+u))

lemma profileEquilibrium_hasDerivAt (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (profileEquilibrium s hs)
      (4*Real.log (profileEndpoint s hs u/2)) u := by
  have hz : 0 < s+u := by positivity
  have hb := profileEndpoint_pos s hs hu
  have dz := (hasDerivAt_id u).const_add s
  have dl := (dz.const_mul 2).log (show 2*(s+u) ≠ 0 by positivity)
  have d := (((analyticProfile_hasDerivAt s hs hu).add_const 2).sub
    (dz.const_mul 4)).add ((dz.const_mul 4).mul dl)
  convert! d using 1
  dsimp only [analyticProfileSlope, id_eq]
  rw [Real.log_div hb.ne' (show (4 : ℝ)*(s+u) ≠ 0 by positivity),
    Real.log_div hb.ne' (by norm_num),
    Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) hz.ne',
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hz.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4]
  field_simp
  ring

lemma profileEquilibrium_continuousOn (s : ℝ) (hs : 0 < s) :
    ContinuousOn (profileEquilibrium s hs) (Ici 0) := by
  have hm : Continuous (fun u : ℝ => 4*(s+u)*Real.log (2*(s+u))) := by
    have hz : Continuous (fun u : ℝ => 2*(s+u)) := by fun_prop
    have h := (Real.continuous_mul_log.comp
      hz).const_mul 2
    convert! h using 1
    ext u
    dsimp only [Function.comp_apply]
    ring
  exact (((analyticProfile_continuousOn s hs).add continuousOn_const).sub
    ((continuous_const.add continuous_id).const_mul 4).continuousOn).add hm.continuousOn

lemma profileEquilibrium_zero (s : ℝ) (hs : 0 < s) :
    profileEquilibrium s hs 0 = 2+4*s*Real.log s-4*s := by
  dsimp [profileEquilibrium]
  rw [analyticProfile_zero]
  simp only [add_zero]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne']
  ring

lemma profileEquilibrium_at_mass_hasDerivAt (s : ℝ) (hs : 0 < s) {b : ℝ}
    (hb : 0 < b) :
    HasDerivAt (fun a => profileEquilibrium s hs (profileMass s a))
      (4*(profileMassSlope s b*Real.log (b/2))) b := by
  have h := (profileEquilibrium_hasDerivAt s hs (profileMass_pos hs hb)).comp b
    (profileMass_hasDerivAt hs)
  rw [profileEndpoint_mass s hs hb.le] at h
  convert! h using 1 <;> ring

/-- Exact evaluation of the base potential of the actual radial mixture. -/
theorem basePotential_eq_profile (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    4*basePotential s b =
      profileEquilibrium s hs (profileMass s b)-(2+4*s*Real.log s-4*s) := by
  have hc : ContinuousOn (fun a => profileEquilibrium s hs (profileMass s a)) (Icc 0 b) :=
    (profileEquilibrium_continuousOn s hs).comp (profileMass_continuous hs).continuousOn
      (fun a ha => profileMass_nonneg hs ha.1)
  have hi := (basePotential_intervalIntegrable s hs hb).const_mul 4
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hc
    (fun a ha => profileEquilibrium_at_mass_hasDerivAt s hs ha.1) hi
  rw [intervalIntegral.integral_const_mul, profileMass_zero hs.le,
    profileEquilibrium_zero] at h
  exact h

/-- The scalar combination left after factorial normalization is exactly the
analytic profile already bounded by the finite certificate. -/
lemma profileEquilibrium_normalization (s : ℝ) (hs : 0 < s) (u : ℝ) :
    profileEquilibrium s hs u - 2 + 4*(s+u) -
      4*(s+u)*Real.log (2*(s+u)) = analyticProfile s hs u := by
  unfold profileEquilibrium
  ring

end Zeta5.Analysis
