import Zeta5.Analysis.ExternalEquilibrium

/-!
# A uniform linear tail for the equilibrium defect

Outside the compact auxiliary support, the positive Abel transform is bounded
by its mass divided by the distance to the support.  Comparing it with the
external-field slope and integrating gives a uniform exponential tail for the
same trial polynomials used on the compact interval.
-/

open MeasureTheory Set

namespace Zeta5.Analysis

lemma abelKernel_le_inverse_gap {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b < t) :
    abelKernel t a ≤ (t-b)⁻¹ := by
  have hb : 0 ≤ b := ha.trans hab
  have ht : 0 < t := lt_of_le_of_lt hb hbt
  have hgap : 0 < t-b := sub_pos.mpr hbt
  have hsq : (t-b)^2 ≤ t^2-a^2 := by nlinarith
  have hrad : 0 ≤ t^2-a^2 := (sq_nonneg (t-b)).trans hsq
  have hroot : t-b ≤ Real.sqrt (t^2-a^2) := by
    have heq := Real.sq_sqrt hrad
    have hn := Real.sqrt_nonneg (t^2-a^2)
    nlinarith
  simpa only [abelKernel, one_div] using one_div_le_one_div_of_le hgap hroot

lemma truncatedAbel_le_mass_div (s : ℝ) (hs : 0 < s) {b t : ℝ}
    (hb : 0 ≤ b) (hbt : b < t) :
    truncatedAbel s b t ≤ profileMass s b/(t-b) := by
  have ht : 0 < t := lt_of_le_of_lt hb hbt
  have hi := (profileMassSlope_abel_truncated s hs hb ht).1
  have hc : IntervalIntegrable (fun a => profileMassSlope s a*(t-b)⁻¹) volume 0 b :=
    ((profileMassSlope_continuous hs).mul continuous_const).intervalIntegrable 0 b
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hb hi hc (fun a ha =>
    mul_le_mul_of_nonneg_left (abelKernel_le_inverse_gap ha.1.le ha.2.le hbt)
      (profileMassSlope_nonneg hs ha.1.le))
  rw [intervalIntegral.integral_mul_const, integral_profileMassSlope s hs b] at h
  exact h

lemma equilibriumSlope_ge_pi_div_four (s : ℝ) (hs : 0 < s) {t : ℝ} (hst : s ≤ t) :
    Real.pi/4 ≤ equilibriumSlope s t := by
  have harg : 1 ≤ t/s := (one_le_div hs).mpr hst
  have hat := Real.arctan_le_arctan_iff.mpr harg
  rw [Real.arctan_one] at hat
  have hup := Real.arctan_lt_pi_div_two t
  unfold equilibriumSlope
  linarith

noncomputable def tailThreshold (s δ : ℝ) : ℝ := (s+δ)+s+8*δ/Real.pi+1

lemma tailThreshold_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) :
    0 < tailThreshold s δ := by
  unfold tailThreshold
  positivity

lemma truncatedAbel_sub_slope_tail (s : ℝ) (hs : 0 < s) {δ b t : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hbB : b ≤ s+δ)
    (hmass : profileMass s b ≤ δ) (ht : tailThreshold s δ ≤ t) :
    truncatedAbel s b t-equilibriumSlope s t ≤ -Real.pi/8 := by
  have hπ := Real.pi_pos
  have hδπ : 0 ≤ 8*δ/Real.pi := by positivity
  have hst : s ≤ t := by dsimp [tailThreshold] at ht; linarith
  have hbt : b < t := by dsimp [tailThreshold] at ht; linarith
  have hgap : 8*δ/Real.pi ≤ t-b := by dsimp [tailThreshold] at ht; linarith
  have hgap' : 8*δ ≤ (t-b)*Real.pi := (div_le_iff₀ hπ).mp hgap
  have hdiv : profileMass s b/(t-b) ≤ Real.pi/8 := by
    apply (div_le_iff₀ (sub_pos.mpr hbt)).mpr
    nlinarith
  have hA := (truncatedAbel_le_mass_div s hs hb hbt).trans hdiv
  have hH := equilibriumSlope_ge_pi_div_four s hs hst
  linarith

lemma potential_defect_increment (s : ℝ) (hs : 0 < s) {b T y : ℝ}
    (hb : 0 ≤ b) (hT : 0 ≤ T) (hTy : T ≤ y) :
    (4*auxiliaryPotential s hs b y-externalField s y)-
      (4*auxiliaryPotential s hs b T-externalField s T) =
        4*∫ t in T..y, truncatedAbel s b t-equilibriumSlope s t := by
  have hy : 0 ≤ y := hT.trans hTy
  have hA0y := truncatedAbel_intervalIntegrable s hs hb hy
  have hA0T := truncatedAbel_intervalIntegrable s hs hb hT
  have hATy : IntervalIntegrable (truncatedAbel s b) volume T y := by
    apply hA0y.mono_set
    rw [uIcc_of_le hTy, uIcc_of_le hy]
    exact Icc_subset_Icc hT le_rfl
  have hH0T : IntervalIntegrable (equilibriumSlope s) volume 0 T :=
    (equilibriumSlope_continuous s).intervalIntegrable 0 T
  have hHTy : IntervalIntegrable (equilibriumSlope s) volume T y :=
    (equilibriumSlope_continuous s).intervalIntegrable T y
  have hA := intervalIntegral.integral_add_adjacent_intervals hA0T hATy
  have hH := intervalIntegral.integral_add_adjacent_intervals hH0T hHTy
  have hUy := mixturePotential_growth s hs hb hy
  have hUT := mixturePotential_growth s hs hb hT
  rw [← auxiliaryPotential_eq_mixture s hs hb hy] at hUy
  rw [← auxiliaryPotential_eq_mixture s hs hb hT] at hUT
  have hVy := externalField_sub_zero hs hy
  have hVT := externalField_sub_zero hs hT
  rw [intervalIntegral.integral_sub hATy hHTy]
  linarith

/-- A uniform linear loss in the potential defect beyond a fixed threshold. -/
theorem auxiliaryPotential_equilibrium_tail (s : ℝ) (hs : 0 < s) {δ b y : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hbB : b ≤ s+δ)
    (hmass : profileMass s b ≤ δ) (hy : tailThreshold s δ ≤ y) :
    4*auxiliaryPotential s hs b y-externalField s y ≤
      profileEquilibrium s hs (profileMass s b)-
        (Real.pi/2)*(y-tailThreshold s δ) := by
  have hT := (tailThreshold_pos hs hδ).le
  have hy0 : 0 ≤ y := hT.trans hy
  have hA0y := truncatedAbel_intervalIntegrable s hs hb hy0
  have hATy : IntervalIntegrable (truncatedAbel s b) volume (tailThreshold s δ) y := by
    apply hA0y.mono_set
    rw [uIcc_of_le hy, uIcc_of_le hy0]
    exact Icc_subset_Icc hT le_rfl
  have hH : IntervalIntegrable (equilibriumSlope s) volume (tailThreshold s δ) y :=
    (equilibriumSlope_continuous s).intervalIntegrable (tailThreshold s δ) y
  have hi := intervalIntegral.integral_mono_on hy (hATy.sub hH)
    (intervalIntegrable_const (c := -Real.pi/8)) (fun t ht =>
      truncatedAbel_sub_slope_tail s hs hδ hb hbB hmass ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hd := potential_defect_increment s hs hb hT hy
  have he := auxiliaryPotential_equilibrium_le s hs hb hT
  nlinarith

/-- Equilibrium and its linear tail combined in one bound valid for every
nonnegative argument. -/
theorem auxiliaryPotential_equilibrium_decay (s : ℝ) (hs : 0 < s) {δ b y : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hbB : b ≤ s+δ)
    (hmass : profileMass s b ≤ δ) (hy : 0 ≤ y) :
    4*auxiliaryPotential s hs b y-externalField s y ≤
      profileEquilibrium s hs (profileMass s b)-
        (Real.pi/2)*max 0 (y-tailThreshold s δ) := by
  by_cases hyt : y ≤ tailThreshold s δ
  · rw [max_eq_left (sub_nonpos.mpr hyt), mul_zero, sub_zero]
    exact auxiliaryPotential_equilibrium_le s hs hb hy
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hyt))]
    exact auxiliaryPotential_equilibrium_tail s hs hδ hb hbB hmass (le_of_not_ge hyt)

/-- One family of monic trial polynomials satisfies both the compact
equilibrium bound and an explicit uniform exponential tail. -/
theorem uniform_weighted_trial_polynomial_decay (s : ℝ) (hs : 0 < s) {δ N : ℝ}
    (hδ : 0 ≤ δ) (hN : 1 ≤ N) (n : ℕ) (hnδ : (n : ℝ)/N ≤ δ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ, 0 ≤ y →
      |p.eval (N^2*y^2)|^2*Real.exp (-N*externalField s y) ≤
        trialPrefactor (s+δ)*N^(4*n+16)*Real.exp (N*profileEquilibrium s hs ((n : ℝ)/N))*
          Real.exp (-(Real.pi/2)*N*max 0 (y-tailThreshold s δ)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu : 0 ≤ (n : ℝ)/N := by positivity
  have hb := profileEndpoint_nonneg s hs ((n : ℝ)/N)
  have hbB : profileEndpoint s hs ((n : ℝ)/N) ≤ s+δ :=
    (profileEndpoint_le_shifted_mass s hs hu).trans (by linarith)
  obtain ⟨p, hpm, hpd, hp⟩ := uniform_auxiliary_trial_polynomial s hs hδ hN n hnδ
  refine ⟨p, hpm, hpd, ?_⟩
  intro y hy
  have hd := auxiliaryPotential_equilibrium_decay s hs hδ hb hbB
    (by simpa only [profileMass_endpoint s hs hu] using hnδ) hy
  rw [profileMass_endpoint s hs hu] at hd
  calc
    _ ≤ (trialPrefactor (s+δ)*N^(4*n+16)*
        Real.exp (4*N*auxiliaryPotential s hs (profileEndpoint s hs ((n : ℝ)/N)) y))*
          Real.exp (-N*externalField s y) :=
      mul_le_mul_of_nonneg_right (hp y hy) (Real.exp_pos _).le
    _ = trialPrefactor (s+δ)*N^(4*n+16)*
        Real.exp (N*(4*auxiliaryPotential s hs (profileEndpoint s hs ((n : ℝ)/N)) y-
          externalField s y)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ trialPrefactor (s+δ)*N^(4*n+16)*
        Real.exp (N*(profileEquilibrium s hs ((n : ℝ)/N)-
          (Real.pi/2)*max 0 (y-tailThreshold s δ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hd hNpos.le))
        (mul_nonneg (trialPrefactor_pos _).le (by positivity))
    _ = _ := by
      rw [show N*(profileEquilibrium s hs ((n : ℝ)/N)-
          (Real.pi/2)*max 0 (y-tailThreshold s δ)) =
          N*profileEquilibrium s hs ((n : ℝ)/N)+
            (-(Real.pi/2)*N*max 0 (y-tailThreshold s δ)) by ring, Real.exp_add]
      ring

end Zeta5.Analysis
