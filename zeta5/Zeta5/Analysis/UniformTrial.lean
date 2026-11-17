import Zeta5.Analysis.MixtureEquilibrium
import Zeta5.Analysis.ProfileInverse

/-!
# Uniform trial polynomials, including degree zero

The endpoint is bounded by `s + δ` when its mass is at most `δ`.
Consequently the logarithmic quadrature estimate has a single prefactor for
the entire range of polynomial degrees used in the Gram determinant.
-/

namespace Zeta5.Analysis

noncomputable def trialPrefactor (B : ℝ) : ℝ :=
  Real.exp (8*(3+(3/2 : ℝ)*B))*(1+B^2)^4

lemma trialPrefactor_pos (B : ℝ) : 0 < trialPrefactor B := by
  unfold trialPrefactor
  positivity

lemma trialPrefactor_one_le {B : ℝ} (hB : 0 ≤ B) : 1 ≤ trialPrefactor B := by
  have he : 1 ≤ Real.exp (8*(3+(3/2 : ℝ)*B)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1 ≤ (1+B^2)^4 := one_le_pow₀ (by nlinarith [sq_nonneg B])
  exact one_le_mul_of_one_le_of_one_le he hp

lemma trialPrefactor_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    trialPrefactor a ≤ trialPrefactor b := by
  have hb : 0 ≤ b := ha.trans hab
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact pow_le_pow_left₀ (by positivity) (by nlinarith) 4
  · positivity
  · positivity

lemma profileEndpoint_le_shifted_mass (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 ≤ u) :
    profileEndpoint s hs u ≤ s+u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp only [profileEndpoint_zero, add_zero]
    exact hs.le
  · have h := endpoint_lt_shifted_mass hs (profileEndpoint_pos s hs hu)
    rw [profileMass_endpoint s hs hu.le] at h
    exact h.le

lemma auxiliaryPotential_zero_support (s : ℝ) (hs : 0 < s) {y : ℝ} (hy : 0 ≤ y) :
    auxiliaryPotential s hs 0 y = 0 := by
  rw [auxiliaryPotential_eq_mixture s hs (le_refl (0 : ℝ)) hy]
  simp [mixturePotential]

/-- A uniform quantitative monic trial polynomial for every degree whose
normalized mass lies in `[0, δ]`. -/
theorem uniform_auxiliary_trial_polynomial (s : ℝ) (hs : 0 < s) {δ N : ℝ}
    (hδ : 0 ≤ δ) (hN : 1 ≤ N) (n : ℕ) (hnδ : (n : ℝ)/N ≤ δ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ, 0 ≤ y →
      |p.eval (N^2*y^2)|^2 ≤ trialPrefactor (s+δ)*N^(4*n+16)*
        Real.exp (4*N*auxiliaryPotential s hs (profileEndpoint s hs ((n : ℝ)/N)) y) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hu : 0 ≤ (n : ℝ)/N := div_nonneg (Nat.cast_nonneg n) hNpos.le
  have hb := profileEndpoint_nonneg s hs ((n : ℝ)/N)
  have hbB : profileEndpoint s hs ((n : ℝ)/N) ≤ s+δ :=
    (profileEndpoint_le_shifted_mass s hs hu).trans (by linarith)
  rcases n.eq_zero_or_pos with rfl | hn
  · refine ⟨1, Polynomial.monic_one, Polynomial.natDegree_one, ?_⟩
    intro y hy
    simp only [Nat.cast_zero, zero_div, profileEndpoint_zero,
      auxiliaryPotential_zero_support s hs hy, mul_zero, Real.exp_zero, mul_one,
      Polynomial.eval_one, abs_one, one_pow, Nat.mul_zero, zero_add]
    exact one_le_mul_of_one_le_of_one_le (trialPrefactor_one_le (by positivity))
      (one_le_pow₀ hN)
  · obtain ⟨p, hpm, hpd, hp⟩ := auxiliaryPotential_trial_polynomial s hs hb hN n hn
      (profileMass_endpoint s hs hu)
    refine ⟨p, hpm, hpd, ?_⟩
    intro y _
    apply (hp y).trans
    change trialPrefactor (profileEndpoint s hs ((n : ℝ)/N))*N^(4*n+16)*_ ≤ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (trialPrefactor_mono hb hbB) (by positivity))
      (Real.exp_pos _).le

end Zeta5.Analysis
