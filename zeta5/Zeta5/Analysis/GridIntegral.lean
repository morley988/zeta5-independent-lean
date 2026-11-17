import Zeta5.Analysis.Trapezoids
import Zeta5.Certificate.AnalyticGrid
import Zeta5.Certificate.GridSaving

/-!
# From the exact 2048-node certificate to the real analytic integral

All endpoint square-root/logarithm checks are proved by Lean, their one-sided
real interpretation is proved in `GridSaving`, and concavity is proved for
the actual explicit profile. This file connects those results by integrating
the lower chords and summing them.
-/

namespace Zeta5.Certificate

open Zeta5.Analysis MeasureTheory

def terminalUpper (start previousUpper : ℕ) : List AnalyticNode → ℕ
  | [] => previousUpper
  | node :: rest => terminalUpper (start + 1) (node.uUpper start) rest

theorem previousUpper_le_terminalUpper {start previousUpper : ℕ} {nodes : List AnalyticNode}
    (h : checkAnalyticNodes start previousUpper nodes = true) :
    previousUpper ≤ terminalUpper start previousUpper nodes := by
  induction nodes generalizing start previousUpper with
  | nil => exact le_rfl
  | cons node rest ih =>
    rcases (checkAnalyticNodes_cons_iff start previousUpper node rest).mp h with
      ⟨hvalid, hgap, hrest⟩
    have hupper : node.uUpper start = node.uLower start + 3 := hvalid.2.2.2.2.2.2.1
    have hstep : previousUpper ≤ node.uUpper start := by omega
    exact hstep.trans (ih hrest)

theorem trapezoidNumerator_le_integral {start previousUpper previousG : ℕ}
    {nodes : List AnalyticNode} {previousMass δ : ℝ}
    (hcheck : checkAnalyticNodes start previousUpper nodes = true)
    (hprev0 : 0 ≤ previousMass)
    (hprevUpper : previousMass ≤ (previousUpper : ℝ) / (2 * fixedScale))
    (hprevG : (previousG : ℝ) / (fixedScale : ℝ) ^ 2 ≤
      analyticSaving (1 / 20) (by norm_num) previousMass)
    (hterminal : (terminalUpper start previousUpper nodes : ℝ) / (2 * fixedScale) ≤ δ) :
    (trapezoidNumerator start previousUpper previousG nodes : ℝ) /
        (4 * (fixedScale : ℝ) ^ 3) ≤
      ∫ x in previousMass..δ, analyticSaving (1 / 20) (by norm_num) x := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  induction nodes generalizing start previousUpper previousG previousMass with
  | nil =>
    simp only [trapezoidNumerator, Nat.cast_zero, zero_div]
    have hδ : previousMass ≤ δ := hprevUpper.trans hterminal
    exact intervalIntegral.integral_nonneg hδ fun x hx =>
      analyticSaving_nonneg (1 / 20) (by norm_num) (hprev0.trans hx.1)
  | cons node rest ih =>
    rcases (checkAnalyticNodes_cons_iff start previousUpper node rest).mp hcheck with
      ⟨hvalid, hgap, hrest⟩
    let currentMass : ℝ := profileMass (1 / 20) (gridPoint start)
    have hinterval := node.mass_interval hvalid
    have hcurrent0 : 0 ≤ currentMass := (node.massLower_pos hvalid).le.trans hinterval.1
    have hcurrentUpper : currentMass ≤ (node.uUpper start : ℝ) / (2 * fixedScale) := hinterval.2
    have hcurrentG := node.savingLower_le hvalid
    have hih := ih hrest hcurrent0 hcurrentUpper hcurrentG hterminal
    have hgapR : (previousUpper : ℝ) ≤ node.uLower start := by exact_mod_cast hgap.le
    have hwidth : (previousUpper : ℝ) / (2 * fixedScale) ≤ node.massLower start :=
      div_le_div_of_nonneg_right hgapR (by positivity)
    have hfirst := lower_trapezoid_le (1 / 20) (by norm_num) hprev0 hprevUpper
      hinterval.1 hwidth hprevG hcurrentG (by positivity) (node.savingLower_pos hvalid).le
    have hfirst_eq :
        ((node.uLower start - previousUpper : ℕ) : ℝ) *
            ((node.gNumerator start + previousG : ℕ) : ℝ) /
            (4 * (fixedScale : ℝ) ^ 3) =
          (node.massLower start - (previousUpper : ℝ) / (2 * fixedScale)) / 2 *
            ((previousG : ℝ) / (fixedScale : ℝ) ^ 2 + node.savingLower start) := by
      rw [Nat.cast_sub hgap.le]
      push_cast
      dsimp [AnalyticNode.massLower, AnalyticNode.savingLower]
      field_simp
      ring
    have hcurrentδ : currentMass ≤ δ := by
      apply hcurrentUpper.trans
      apply le_trans _ hterminal
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast previousUpper_le_terminalUpper hrest) (by positivity)
    have hprevCurrent : previousMass ≤ currentMass := hprevUpper.trans (hwidth.trans hinterval.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (analyticSaving_intervalIntegrable (1 / 20) (by norm_num) hprev0 hprevCurrent)
      (analyticSaving_intervalIntegrable (1 / 20) (by norm_num) hcurrent0 hcurrentδ)
    simp only [trapezoidNumerator, Nat.cast_add, Nat.cast_mul]
    rw [add_div]
    have hfirst' :
        ((node.uLower start - previousUpper : ℕ) : ℝ) *
          ((node.gNumerator start : ℝ) + previousG) / (4 * (fixedScale : ℝ) ^ 3) ≤
        ∫ x in previousMass..currentMass, analyticSaving (1 / 20) (by norm_num) x := by
      convert! hfirst using 1
      simpa only [Nat.cast_add] using hfirst_eq
    linarith

set_option maxRecDepth 32768 in
theorem analytic_terminalUpper_exact :
    terminalUpper 1 0 analyticNodes = analyticNode2048.uUpper 2048 := by decide

noncomputable def analyticIntegral : ℝ :=
  ∫ u in (0 : ℝ)..(6 / 5 : ℝ), analyticSaving (1 / 20) (by norm_num) u

theorem analyticTotalNumerator_le_integral :
    (analyticTotalNumerator : ℝ) / (4 * (fixedScale : ℝ) ^ 3) ≤ analyticIntegral := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hlast : (analyticNode2048.uUpper 2048 : ℝ) * 5 < 12 * fixedScale := by
    exact_mod_cast analyticLast_lt_delta
  have hterminal : (terminalUpper 1 0 analyticNodes : ℝ) / (2 * fixedScale) ≤ (6 / 5 : ℝ) := by
    rw [analytic_terminalUpper_exact]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * fixedScale)).2
    linarith
  have h := trapezoidNumerator_le_integral analyticNodes_all_checks
    (previousMass := 0) (δ := 6 / 5) le_rfl (by simp) initialSaving_le hterminal
  simpa only [analyticTotalNumerator_exact, analyticIntegral] using h

theorem analyticIntegral_gt_threshold : (54133 / 10000 : ℝ) < analyticIntegral := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hfinite : (analyticTotalNumerator : ℝ) * 10000 >
      54133 * (4 * (fixedScale : ℝ) ^ 3) := by
    exact_mod_cast analyticTotalNumerator_gt_threshold
  have hratio : (54133 / 10000 : ℝ) <
      (analyticTotalNumerator : ℝ) / (4 * (fixedScale : ℝ) ^ 3) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (fixedScale : ℝ) ^ 3)).2
    linarith
  exact hratio.trans_le analyticTotalNumerator_le_integral

theorem analyticIntegral_gt_displayed : (54133705070 / 10 ^ 10 : ℝ) < analyticIntegral := by
  have hM : (0 : ℝ) < fixedScale := by exact_mod_cast fixedScale_pos
  have hfinite : (analyticTotalNumerator : ℝ) * 10 ^ 10 >
      54133705070 * (4 * (fixedScale : ℝ) ^ 3) := by
    exact_mod_cast analyticTotalNumerator_gt_displayed
  have hratio : (54133705070 / 10 ^ 10 : ℝ) <
      (analyticTotalNumerator : ℝ) / (4 * (fixedScale : ℝ) ^ 3) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (fixedScale : ℝ) ^ 3)).2
    linarith
  exact hratio.trans_le analyticTotalNumerator_le_integral

theorem analyticIntegral_eq_neg_profileIntegral :
    analyticIntegral = -(∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      analyticProfile (1 / 20) (by norm_num) u) := by
  simp only [analyticIntegral, analyticSaving, intervalIntegral.integral_neg]

end Zeta5.Certificate
