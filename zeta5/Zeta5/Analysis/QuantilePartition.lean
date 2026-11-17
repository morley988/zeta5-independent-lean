import Zeta5.Analysis.QuantileQuadrature
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-!
# Existence of equal-mass interval partitions

Only finiteness and absence of atoms are needed.  The cumulative integral is
continuous, and its prescribed levels force the chosen endpoints into strictly
increasing order; positivity of a density is not needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Zeta5.Analysis

lemma nullSingletonClass_of_fourth_power_smallBall
    (μ : Measure ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ (v ρ : ℝ), 0 < ρ →
      μ {w : ℝ | |v-w| < ρ^4} ≤ ENNReal.ofReal (C*ρ)) :
    NullSingletonClass μ := by
  constructor
  intro v
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  change μ {v} ≤ 0 + (ε : ℝ≥0∞)
  rw [zero_add]
  have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hden : 0 < C+1 := by linarith
  have hρ : 0 < (ε : ℝ)/(C+1) := div_pos hεr hden
  calc
    μ {v} ≤ μ {w : ℝ | |v-w| < ((ε : ℝ)/(C+1))^4} := by
      apply measure_mono
      intro w hw
      rcases mem_singleton_iff.mp hw with rfl
      simpa using pow_pos hρ 4
    _ ≤ ENNReal.ofReal (C*((ε : ℝ)/(C+1))) := hsmall _ _ hρ
    _ ≤ (ε : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

lemma integral_one_eq_real_Ioc (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ _ in a..b, (1 : ℝ) ∂μ) = μ.real (Ioc a b) := by
  rw [intervalIntegral.integral_const', Ioc_eq_empty_of_le hab]
  simp

/-- A positive integer number of equal-mass cells exists for every finite,
atomless measure on an interval whose mass has the required value. -/
theorem exists_equalMass_partition (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {N B : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (n : ℕ) (hn : 0 < n) (hmass : μ.real (Ioc 0 B) = (n : ℝ)/N) :
    ∃ a : ℕ → ℝ, a 0 = 0 ∧ a n = B ∧
      (∀ j ≤ n, a j ∈ Icc (0 : ℝ) B) ∧
      (∀ j < n, a j < a (j+1)) ∧
      (∀ j < n, μ.real (Ioc (a j) (a (j+1))) = 1/N) := by
  let F : ℝ → ℝ := fun x => ∫ _ in 0..x, (1 : ℝ) ∂μ
  have hFcont : Continuous F := (integrable_const (1 : ℝ)).continuous_primitive 0
  have hFzero : F 0 = 0 := by simp [F]
  have hFB : F B = (n : ℝ)/N := by
    dsimp [F]
    rw [integral_one_eq_real_Ioc μ hB, hmass]
  have hFmono : Monotone F := by
    intro x y hxy
    have hid := intervalIntegral.integral_add_adjacent_intervals
      (μ := μ) (f := fun _ => (1 : ℝ)) (a := 0) (b := x) (c := y)
      intervalIntegrable_const intervalIntegrable_const
    have hp := intervalIntegral.integral_nonneg_of_forall (μ := μ) hxy
      (fun _ : ℝ => (show (0 : ℝ) ≤ 1 by norm_num))
    dsimp [F]
    linarith
  have hex (j : ℕ) (hj : j ≤ n) : ∃ x ∈ Icc (0 : ℝ) B, F x = (j : ℝ)/N := by
    apply intermediate_value_Icc hB hFcont.continuousOn
    rw [hFzero, hFB]
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hj) hN.le
  choose x hxmem hxval using hex
  let a : ℕ → ℝ := fun j => if h0 : j = 0 then 0
    else if hj : j < n then x j hj.le else B
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = B := by simp [a, Nat.ne_of_gt hn]
  have hamem (j : ℕ) (hj : j ≤ n) : a j ∈ Icc (0 : ℝ) B := by
    by_cases h0 : j = 0
    · simp [a, h0, hB]
    by_cases hjn : j < n
    · simpa [a, h0, hjn] using hxmem j hjn.le
    · simp [a, h0, hjn, hB]
  have haval (j : ℕ) (hj : j ≤ n) : F (a j) = (j : ℝ)/N := by
    by_cases h0 : j = 0
    · simp [a, h0, hFzero]
    by_cases hjn : j < n
    · simpa [a, h0, hjn] using hxval j hjn.le
    · have hjeq : j = n := le_antisymm hj (Nat.le_of_not_gt hjn)
      simpa [a, h0, hjn, hjeq, Nat.ne_of_gt hn] using hFB
  have hastrict (j : ℕ) (hj : j < n) : a j < a (j+1) := by
    by_contra h
    have hh := hFmono (le_of_not_gt h)
    rw [haval j hj.le, haval (j+1) hj] at hh
    have hdiv : (j : ℝ)/N < (j+1 : ℕ)/N :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self j) hN
    exact (not_lt_of_ge hh) hdiv
  refine ⟨a, ha0, han, hamem, hastrict, ?_⟩
  intro j hj
  have hid := intervalIntegral.integral_add_adjacent_intervals
    (μ := μ) (f := fun _ => (1 : ℝ)) (a := 0) (b := a j) (c := a (j+1))
    intervalIntegrable_const intervalIntegrable_const
  change F (a j) + (∫ _ in a j..a (j+1), (1 : ℝ) ∂μ) = F (a (j+1)) at hid
  rw [haval j hj.le, haval (j+1) hj,
    integral_one_eq_real_Ioc μ (hastrict j hj).le] at hid
  push_cast at hid
  rw [add_div] at hid
  linarith

end Zeta5.Analysis
