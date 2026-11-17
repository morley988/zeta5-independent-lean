import Zeta5.Analysis.RiemannWeight
import Zeta5.Analysis.ProfileContinuity

/-! # Exact grid bounds for the decreasing analytic profile -/

noncomputable section
namespace Zeta5.Analysis
open Real Set MeasureTheory Filter Finset
open scoped Topology BigOperators

theorem analyticProfile_antitoneOn (s : ℝ) (hs : 0 < s) :
    AntitoneOn (analyticProfile s hs) (Ici 0) := by
  apply (strictAntiOn_of_deriv_neg (convex_Ici 0) (analyticProfile_continuousOn s hs) ?_).antitoneOn
  intro u hu
  have hu' : 0 < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
  rw [(analyticProfile_hasDerivAt s hs hu').deriv]
  exact analyticProfileSlope_neg s hs hu'

/-- The left-endpoint sum exceeds its integral by at most the total decrease
over the interval. This estimate remains uniform at u=0. -/
theorem analyticProfile_grid_upper (s : ℝ) (hs : 0 < s) {N : ℝ} (hN : 0 < N) (r : ℕ) :
    (∑ k ∈ range r, analyticProfile s hs ((k : ℝ) / N)) ≤
      N * (∫ u in 0..((r : ℝ) / N), analyticProfile s hs u) +
        analyticProfile s hs 0 - analyticProfile s hs ((r : ℝ) / N) := by
  let f : ℝ → ℝ := fun u => -analyticProfile s hs (max 0 u)
  have hf : Continuous f := by
    exact ((analyticProfile_continuousOn s hs).comp_continuous
      (continuous_const.max continuous_id) (fun u => le_max_left 0 u)).neg
  have hmono : MonotoneOn f (Ici 0) := by
    intro a ha b hb hab
    dsimp [f]
    rw [max_eq_right ha, max_eq_right hb]
    exact neg_le_neg (analyticProfile_antitoneOn s hs ha hb hab)
  have hgrid := (monotone_grid_integral_bounds f hf hmono hN r).2
  have hint : (∫ u in 0..((r : ℝ) / N), f u) =
      -(∫ u in 0..((r : ℝ) / N), analyticProfile s hs u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by positivity)] at hu
    dsimp [f]
    rw [max_eq_right hu.1]
  have hval (k : ℕ) : f ((k : ℝ) / N) = -analyticProfile s hs ((k : ℝ) / N) := by
    dsimp [f]
    rw [max_eq_right (by positivity)]
  rw [hint] at hgrid
  simp only [hval, Finset.sum_neg_distrib, mul_neg] at hgrid
  have htel := Finset.sum_range_sub (fun k : ℕ => analyticProfile s hs ((k : ℝ) / N)) r
  rw [Finset.sum_sub_distrib] at htel
  simp only [Nat.cast_zero, zero_div] at htel
  linarith

end Zeta5.Analysis
