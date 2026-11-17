import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebra and calculus of the positive-window analytic profile

This file verifies explicit elementary formulas from the analytic branch.
It does not assert the logarithmic-potential construction, the quantile
discretization estimate, or the asymptotic determinant estimate.
-/

namespace Zeta5.Analysis

noncomputable section

/-- Total mass of the auxiliary potential measure, written explicitly. -/
def profileMass (s b : ℝ) : ℝ :=
  (b + 1 - 2 * s - Real.sqrt (1 + b ^ 2) +
    2 * Real.sqrt (s ^ 2 + b ^ 2)) / 2

/-- Derivative of `profileMass` with respect to the endpoint. -/
def profileMassSlope (s b : ℝ) : ℝ :=
  (1 - b / Real.sqrt (1 + b ^ 2) +
    2 * b / Real.sqrt (s ^ 2 + b ^ 2)) / 2

theorem sqrt_one_add_sq_gt_one {b : ℝ} (hb : 0 < b) :
    1 < Real.sqrt (1 + b ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + b ^ 2)
  nlinarith [sq_pos_of_pos hb]

theorem sqrt_one_add_sq_gt_self {b : ℝ} (hb : 0 ≤ b) :
    b < Real.sqrt (1 + b ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + b ^ 2)
  nlinarith

theorem sqrt_one_add_sq_lt_one_add {b : ℝ} (hb : 0 < b) :
    Real.sqrt (1 + b ^ 2) < 1 + b := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (1 + b ^ 2)
  nlinarith

theorem sqrt_sum_sq_gt_right {s b : ℝ} (hs : 0 < s) (hb : 0 ≤ b) :
    b < Real.sqrt (s ^ 2 + b ^ 2) := by
  have heq := Real.sq_sqrt (show 0 ≤ s ^ 2 + b ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (s ^ 2 + b ^ 2)
  nlinarith [sq_pos_of_pos hs]

theorem sqrt_sum_sq_gt_left {s b : ℝ} (hs : 0 ≤ s) (hb : 0 < b) :
    s < Real.sqrt (s ^ 2 + b ^ 2) := by
  have heq := Real.sq_sqrt (show 0 ≤ s ^ 2 + b ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (s ^ 2 + b ^ 2)
  nlinarith [sq_pos_of_pos hb]

@[simp] theorem profileMass_zero {s : ℝ} (hs : 0 ≤ s) :
    profileMass s 0 = 0 := by
  simp [profileMass, Real.sqrt_sq hs]

theorem profileMass_pos {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    0 < profileMass s b := by
  have h1 := sqrt_one_add_sq_lt_one_add hb
  have h2 := sqrt_sum_sq_gt_left hs.le hb
  dsimp [profileMass]
  linarith

theorem endpoint_lt_shifted_mass {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    b < s + profileMass s b := by
  have h1 := sqrt_one_add_sq_lt_one_add hb
  have h2 := sqrt_sum_sq_gt_right hs hb.le
  dsimp [profileMass]
  linarith

theorem sqrt_lt_shifted_mass {s b : ℝ} (_hs : 0 < s) (hb : 0 < b) :
    Real.sqrt (s ^ 2 + b ^ 2) < s + profileMass s b := by
  have h1 := sqrt_one_add_sq_lt_one_add hb
  dsimp [profileMass]
  linarith

theorem profileMassSlope_pos {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    0 < profileMassSlope s b := by
  have ha : 0 < Real.sqrt (1 + b ^ 2) := by positivity
  have hc : 0 < Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have hba : b / Real.sqrt (1 + b ^ 2) < 1 :=
    (div_lt_one ha).2 (sqrt_one_add_sq_gt_self hb.le)
  have hbc : 0 < 2 * b / Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  dsimp [profileMassSlope]
  linarith

theorem profileMass_hasDerivAt {s b : ℝ} (hs : 0 < s) :
    HasDerivAt (profileMass s) (profileMassSlope s b) b := by
  have h₁ : 1 + b ^ 2 ≠ 0 := by positivity
  have h₂ : s ^ 2 + b ^ 2 ≠ 0 := by positivity
  have d₁ := (((hasDerivAt_id b).pow 2).const_add 1).sqrt h₁
  have d₂ := (((hasDerivAt_id b).pow 2).const_add (s ^ 2)).sqrt h₂
  have d := (((((hasDerivAt_id b).add_const 1).sub_const (2 * s)).sub d₁).add
    (d₂.const_mul 2)).div_const 2
  convert! d using 1
  simp [profileMassSlope]
  field_simp

theorem profileMass_continuous {s : ℝ} (hs : 0 < s) :
    Continuous (profileMass s) :=
  continuous_iff_continuousAt.mpr fun _ => (profileMass_hasDerivAt hs).continuousAt

theorem profileMass_strictMonoOn {s : ℝ} (hs : 0 < s) :
    StrictMonoOn (profileMass s) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (profileMass_continuous hs).continuousOn
  intro b hb
  have hb' : 0 < b := by simpa only [interior_Ici, Set.mem_Ioi] using hb
  rw [(profileMass_hasDerivAt hs).deriv]
  exact profileMassSlope_pos hs hb'

theorem profileMass_nonneg {s b : ℝ} (hs : 0 < s) (hb : 0 ≤ b) :
    0 ≤ profileMass s b := by
  have h := (profileMass_strictMonoOn hs).monotoneOn (show (0 : ℝ) ∈ Set.Ici 0 by simp) hb hb
  simpa only [profileMass_zero hs.le] using h

theorem exists_profileMass_eq {s u : ℝ} (hs : 0 < s) (hu : 0 ≤ u) :
    ∃ b : ℝ, 0 ≤ b ∧ profileMass s b = u := by
  let B : ℝ := u + s + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hmB : u ≤ profileMass s B := by
    have h := endpoint_lt_shifted_mass hs hB
    dsimp [B] at h ⊢
    linarith
  have hm0 : profileMass s 0 ≤ u := by simpa only [profileMass_zero hs.le] using hu
  obtain ⟨b, hb, hbu⟩ :=
    intermediate_value_Icc hB.le (profileMass_continuous hs).continuousOn ⟨hm0, hmB⟩
  exact ⟨b, hb.1, hbu⟩

theorem mass_curvature_identity {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    2 * (s + profileMass s b - b * profileMassSlope s b) =
      1 - 1 / Real.sqrt (1 + b ^ 2) +
        2 * s ^ 2 / Real.sqrt (s ^ 2 + b ^ 2) := by
  have ha : 0 < Real.sqrt (1 + b ^ 2) := by positivity
  have hc : 0 < Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have ha_sq := Real.sq_sqrt (show 0 ≤ 1 + b ^ 2 by positivity)
  have hc_sq := Real.sq_sqrt (show 0 ≤ s ^ 2 + b ^ 2 by positivity)
  have hba : b ^ 2 / Real.sqrt (1 + b ^ 2) =
      Real.sqrt (1 + b ^ 2) - 1 / Real.sqrt (1 + b ^ 2) := by
    field_simp
    nlinarith
  have hbc : b ^ 2 / Real.sqrt (s ^ 2 + b ^ 2) =
      Real.sqrt (s ^ 2 + b ^ 2) - s ^ 2 / Real.sqrt (s ^ 2 + b ^ 2) := by
    field_simp
    nlinarith
  calc
    _ = 1 - Real.sqrt (1 + b ^ 2) + b ^ 2 / Real.sqrt (1 + b ^ 2) +
        2 * Real.sqrt (s ^ 2 + b ^ 2) -
        2 * (b ^ 2 / Real.sqrt (s ^ 2 + b ^ 2)) := by
      dsimp [profileMass, profileMassSlope]
      ring
    _ = _ := by rw [hba, hbc]; ring

theorem mass_curvature_pos {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    0 < s + profileMass s b - b * profileMassSlope s b := by
  have ha := sqrt_one_add_sq_gt_one hb
  have ha_pos : 0 < Real.sqrt (1 + b ^ 2) := by positivity
  have hdiv : 1 / Real.sqrt (1 + b ^ 2) < 1 := (div_lt_one ha_pos).2 ha
  have hterm : 0 < 2 * s ^ 2 / Real.sqrt (s ^ 2 + b ^ 2) := by positivity
  have hid := mass_curvature_identity hs hb
  linarith

end

end Zeta5.Analysis
