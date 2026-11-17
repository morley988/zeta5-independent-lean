import Zeta5.Analysis.ProfileInverse

/-!
# Shape of the explicit analytic profile

The auxiliary inverse endpoint is the actual inverse constructed in
`ProfileInverse`.  No inverse, derivative, or concavity axiom is assumed.
-/

namespace Zeta5.Analysis

noncomputable section

/-- The explicit profile, expanded into logarithms to expose its derivative. -/
def analyticProfile (s : ℝ) (hs : 0 < s) (u : ℝ) : ℝ :=
  let b := profileEndpoint s hs u
  4 * u * Real.log b - 4 * (s + u) * Real.log (4 * (s + u)) +
    4 * s * Real.log (s + Real.sqrt (s ^ 2 + b ^ 2)) -
    2 * Real.log ((1 + Real.sqrt (1 + b ^ 2)) / 2)

def analyticProfileSlope (s : ℝ) (hs : 0 < s) (u : ℝ) : ℝ :=
  4 * Real.log (profileEndpoint s hs u / (4 * (s + u)))

theorem profile_log_derivative_cancellation {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    4 * profileMass s b / b +
        4 * s * b / (Real.sqrt (s ^ 2 + b ^ 2) * (s + Real.sqrt (s ^ 2 + b ^ 2))) -
        2 * b / (Real.sqrt (1 + b ^ 2) * (1 + Real.sqrt (1 + b ^ 2))) =
      4 * profileMassSlope s b := by
  have ha : 0 < Real.sqrt (1 + b ^ 2) := by positivity
  have hc : 0 < Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have ha_sq := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hc_sq := Real.sq_sqrt (show 0 ≤ s ^ 2 + b ^ 2 by positivity)
  have hsc : 0 < s + Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have h1a : 0 < 1 + Real.sqrt (1 + b ^ 2) := by positivity
  have hC : b / (Real.sqrt (s ^ 2 + b ^ 2) * (s + Real.sqrt (s ^ 2 + b ^ 2))) =
      (1 - s / Real.sqrt (s ^ 2 + b ^ 2)) / b := by
    field_simp
    nlinarith
  have hA : b / (Real.sqrt (1 + b ^ 2) * (1 + Real.sqrt (1 + b ^ 2))) =
      (1 - 1 / Real.sqrt (1 + b ^ 2)) / b := by
    field_simp
    nlinarith
  calc
    _ = 4 * profileMass s b / b +
        4 * s * (b / (Real.sqrt (s ^ 2 + b ^ 2) * (s + Real.sqrt (s ^ 2 + b ^ 2)))) -
        2 * (b / (Real.sqrt (1 + b ^ 2) * (1 + Real.sqrt (1 + b ^ 2)))) := by ring
    _ = (4 * (s + profileMass s b) -
        2 * (1 - 1 / Real.sqrt (1 + b ^ 2) +
          2 * s ^ 2 / Real.sqrt (s ^ 2 + b ^ 2))) / b := by rw [hC, hA]; ring
    _ = _ := by
      rw [← mass_curvature_identity hs hb]
      field_simp
      ring

theorem analyticProfile_hasDerivAt (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (analyticProfile s hs) (analyticProfileSlope s hs u) u := by
  have hb := profileEndpoint_pos s hs hu
  have hd := profileMassSlope_pos hs hb
  have hv : 0 < s + u := by positivity
  have ha : 0 < Real.sqrt (1 + (profileEndpoint s hs u) ^ 2) := by positivity
  have hc : 0 < Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2) := by positivity
  have hsc : 0 < s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2) := by positivity
  have h1a : 0 < 1 + Real.sqrt (1 + (profileEndpoint s hs u) ^ 2) := by positivity
  have db := profileEndpoint_hasDerivAt s hs hu
  have dv := (hasDerivAt_id u).const_add s
  have dB := db.log hb.ne'
  have dV := (dv.const_mul 4).log (show 4 * (s + u) ≠ 0 by positivity)
  have dC := ((db.pow 2).const_add (s ^ 2)).sqrt
    (show s ^ 2 + (profileEndpoint s hs u) ^ 2 ≠ 0 by positivity)
  have dSC := (dC.const_add s).log hsc.ne'
  have dA := ((db.pow 2).const_add 1).sqrt
    (show 1 + (profileEndpoint s hs u) ^ 2 ≠ 0 by positivity)
  have dA1 := ((dA.const_add 1).div_const 2).log (show (1 + Real.sqrt (1 +
    (profileEndpoint s hs u) ^ 2)) / 2 ≠ 0 by positivity)
  have d := (((((hasDerivAt_id u).const_mul 4).mul dB).sub
    ((dv.const_mul 4).mul dV)).add (dSC.const_mul (4 * s))).sub (dA1.const_mul 2)
  have hcancel := profile_log_derivative_cancellation hs hb
  rw [profileMass_endpoint s hs hu.le] at hcancel
  convert! d using 1
  dsimp [analyticProfileSlope]
  rw [Real.log_div hb.ne' (show 4 * (s + u) ≠ 0 by positivity)]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp at hcancel ⊢
  nlinarith [hcancel]

theorem analyticProfile_formula (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    analyticProfile s hs u =
      4 * u * Real.log (profileEndpoint s hs u / (4 * (s + u))) +
      4 * s * Real.log ((s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2)) /
        (4 * (s + u))) -
      2 * Real.log ((1 + Real.sqrt (1 + (profileEndpoint s hs u) ^ 2)) / 2) := by
  have hb := profileEndpoint_pos s hs hu
  have hv : 0 < 4 * (s + u) := by positivity
  have hc : 0 < s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2) := by positivity
  dsimp [analyticProfile]
  rw [Real.log_div hb.ne' hv.ne', Real.log_div hc.ne' hv.ne']
  ring

theorem analyticProfileSlope_neg (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    analyticProfileSlope s hs u < 0 := by
  have hb := profileEndpoint_pos s hs hu
  have hv : 0 < 4 * (s + u) := by positivity
  have hbu := endpoint_lt_shifted_mass hs hb
  rw [profileMass_endpoint s hs hu.le] at hbu
  have hargpos : 0 < profileEndpoint s hs u / (4 * (s + u)) := div_pos hb hv
  have harglt : profileEndpoint s hs u / (4 * (s + u)) < 1 := by
    apply (div_lt_one hv).2
    linarith
  exact mul_neg_of_pos_of_neg (by norm_num) (Real.log_neg hargpos harglt)

theorem analyticProfileSlope_hasDerivAt (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (analyticProfileSlope s hs)
      (4 * (s + u - profileEndpoint s hs u *
          profileMassSlope s (profileEndpoint s hs u)) /
        (profileEndpoint s hs u * profileMassSlope s (profileEndpoint s hs u) * (s + u))) u := by
  have hb := profileEndpoint_pos s hs hu
  have hd := profileMassSlope_pos hs hb
  have hv : 0 < s + u := by positivity
  have dv := ((hasDerivAt_id u).const_add s).const_mul 4
  have db := profileEndpoint_hasDerivAt s hs hu
  have darg := db.div dv (show 4 * (s + u) ≠ 0 by positivity)
  have dlog := darg.log (show profileEndpoint s hs u / (4 * (s + u)) ≠ 0 by positivity)
  convert! dlog.const_mul 4 using 1
  dsimp
  field_simp

theorem analyticProfileSlope_deriv_pos (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    0 < deriv (analyticProfileSlope s hs) u := by
  rw [(analyticProfileSlope_hasDerivAt s hs hu).deriv]
  have hb := profileEndpoint_pos s hs hu
  have hd := profileMassSlope_pos hs hb
  have hcurv := mass_curvature_pos hs hb
  rw [profileMass_endpoint s hs hu.le] at hcurv
  exact div_pos (mul_pos (by norm_num) hcurv) (mul_pos (mul_pos hb hd) (by positivity))

theorem analyticProfileSlope_strictMonoOn (s : ℝ) (hs : 0 < s) :
    StrictMonoOn (analyticProfileSlope s hs) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro u hu
    exact (analyticProfileSlope_hasDerivAt s hs hu).continuousAt.continuousWithinAt
  · intro u hu
    exact analyticProfileSlope_deriv_pos s hs (by simpa only [interior_Ioi, Set.mem_Ioi] using hu)

theorem analyticProfile_strictConvexOn (s : ℝ) (hs : 0 < s) :
    StrictConvexOn ℝ (Set.Ioi 0) (analyticProfile s hs) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
  · intro u hu
    exact (analyticProfile_hasDerivAt s hs hu).continuousAt.continuousWithinAt
  · intro u hu v hv huv
    have hu' : 0 < u := by simpa only [interior_Ioi, Set.mem_Ioi] using hu
    have hv' : 0 < v := by simpa only [interior_Ioi, Set.mem_Ioi] using hv
    rw [(analyticProfile_hasDerivAt s hs hu').deriv,
      (analyticProfile_hasDerivAt s hs hv').deriv]
    exact analyticProfileSlope_strictMonoOn s hs hu' hv' huv

theorem analyticProfile_neg (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    analyticProfile s hs u < 0 := by
  have hb := profileEndpoint_pos s hs hu
  have hv : 0 < 4 * (s + u) := by positivity
  have hbu := endpoint_lt_shifted_mass hs hb
  rw [profileMass_endpoint s hs hu.le] at hbu
  have hcv := sqrt_lt_shifted_mass hs hb
  rw [profileMass_endpoint s hs hu.le] at hcv
  have hsc := sqrt_sum_sq_gt_left hs.le hb
  have ha := sqrt_one_add_sq_gt_one hb
  have hlog₁ : Real.log (profileEndpoint s hs u / (4 * (s + u))) < 0 :=
    Real.log_neg (div_pos hb hv) ((div_lt_one hv).2 (by linarith))
  have hlog₂ : Real.log ((s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2)) /
      (4 * (s + u))) < 0 :=
    Real.log_neg (by positivity) ((div_lt_one hv).2 (by linarith))
  have hlog₃ : 0 < Real.log ((1 + Real.sqrt (1 + (profileEndpoint s hs u) ^ 2)) / 2) :=
    Real.log_pos (by linarith)
  rw [analyticProfile_formula s hs hu]
  have ht₁ := mul_neg_of_pos_of_neg (show 0 < 4 * u by positivity) hlog₁
  have ht₂ := mul_neg_of_pos_of_neg (show 0 < 4 * s by positivity) hlog₂
  linarith

def analyticSaving (s : ℝ) (hs : 0 < s) (u : ℝ) : ℝ :=
  -analyticProfile s hs u

theorem analyticSaving_formula (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    analyticSaving s hs u =
      4 * u * Real.log (4 * (s + u) / profileEndpoint s hs u) +
      4 * s * Real.log (4 * (s + u) /
        (s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2))) +
      2 * Real.log ((1 + Real.sqrt (1 + (profileEndpoint s hs u) ^ 2)) / 2) := by
  have hb := profileEndpoint_pos s hs hu
  have hv : 0 < 4 * (s + u) := by positivity
  have hc : 0 < s + Real.sqrt (s ^ 2 + (profileEndpoint s hs u) ^ 2) := by positivity
  rw [analyticSaving, analyticProfile_formula s hs hu]
  rw [Real.log_div hb.ne' hv.ne', Real.log_div hc.ne' hv.ne',
    Real.log_div hv.ne' hb.ne', Real.log_div hv.ne' hc.ne']
  ring

theorem analyticSaving_at_mass (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 < b) :
    analyticSaving s hs (profileMass s b) =
      4 * profileMass s b * Real.log (4 * (s + profileMass s b) / b) +
      4 * s * Real.log (4 * (s + profileMass s b) /
        (s + Real.sqrt (s ^ 2 + b ^ 2))) +
      2 * Real.log ((1 + Real.sqrt (1 + b ^ 2)) / 2) := by
  rw [analyticSaving_formula s hs (profileMass_pos hs hb), profileEndpoint_mass s hs hb.le]

theorem analyticSaving_pos (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    0 < analyticSaving s hs u :=
  neg_pos.mpr (analyticProfile_neg s hs hu)

theorem analyticSaving_strictConcaveOn (s : ℝ) (hs : 0 < s) :
    StrictConcaveOn ℝ (Set.Ioi 0) (analyticSaving s hs) :=
  (analyticProfile_strictConvexOn s hs).neg

@[simp] theorem analyticProfile_zero (s : ℝ) (hs : 0 < s) :
    analyticProfile s hs 0 = -4 * s * Real.log 2 := by
  dsimp [analyticProfile]
  simp only [profileEndpoint_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq hs.le, Real.sqrt_one, zero_sub]
  norm_num
  rw [show s + s = 2 * s by ring,
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hs.ne',
    Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) hs.ne']
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert! Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  rw [hlog4]
  ring

@[simp] theorem analyticSaving_zero (s : ℝ) (hs : 0 < s) :
    analyticSaving s hs 0 = 4 * s * Real.log 2 := by
  rw [analyticSaving, analyticProfile_zero]
  ring

end

end Zeta5.Analysis
