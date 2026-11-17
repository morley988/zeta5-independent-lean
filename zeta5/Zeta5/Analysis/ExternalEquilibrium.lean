import Zeta5.Analysis.EquilibriumConstant
import Zeta5.Analysis.UniformTrial
import Zeta5.Analysis.ExternalField

/-!
# Equilibrium against the actual external field

All objects here are constructed explicitly: the positive auxiliary measure,
its logarithmic potential, the external-field integral, and the inverse
endpoint.  The equilibrium inequality and its constant are proved, not
supplied as hypotheses.
-/

namespace Zeta5.Analysis

theorem auxiliaryPotential_equilibrium_le (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    4*auxiliaryPotential s hs b y-externalField s y ≤
      profileEquilibrium s hs (profileMass s b) := by
  have hu := auxiliaryPotential_le_base_add_slope s hs hb hy
  have hv := externalField_sub_zero hs hy
  have hc := basePotential_eq_profile s hs hb
  rw [externalField_zero hs] at hv
  nlinarith

theorem auxiliaryPotential_equilibrium_eq (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hy : 0 ≤ y) (hyb : y ≤ b) :
    4*auxiliaryPotential s hs b y-externalField s y =
      profileEquilibrium s hs (profileMass s b) := by
  have hu := auxiliaryPotential_eq_base_add_slope s hs hy hyb
  have hv := externalField_sub_zero hs hy
  have hc := basePotential_eq_profile s hs (hy.trans hyb)
  rw [externalField_zero hs] at hv
  nlinarith

theorem auxiliaryPotential_endpoint_equilibrium_le (s : ℝ) (hs : 0 < s) {u y : ℝ}
    (hu : 0 ≤ u) (hy : 0 ≤ y) :
    4*auxiliaryPotential s hs (profileEndpoint s hs u) y-externalField s y ≤
      profileEquilibrium s hs u := by
  simpa only [profileMass_endpoint s hs hu] using
    auxiliaryPotential_equilibrium_le s hs (profileEndpoint_nonneg s hs u) hy

/-- Multiplication of the explicit trial bound by the external-field weight.
This statement can be applied to a fixed chosen polynomial, so the same
polynomial remains available for a sharper tail estimate. -/
lemma weighted_trial_bound (s : ℝ) (hs : 0 < s) {N u y K : ℝ} (hN : 0 ≤ N)
    (hu : 0 ≤ u) (hy : 0 ≤ y) (hK : 0 ≤ K) {p : Polynomial ℝ}
    (hp : |p.eval (N^2*y^2)|^2 ≤ K*
      Real.exp (4*N*auxiliaryPotential s hs (profileEndpoint s hs u) y)) :
    |p.eval (N^2*y^2)|^2*Real.exp (-N*externalField s y) ≤
      K*Real.exp (N*profileEquilibrium s hs u) := by
  calc
    _ ≤ (K*Real.exp (4*N*auxiliaryPotential s hs (profileEndpoint s hs u) y))*
        Real.exp (-N*externalField s y) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = K*Real.exp (N*(4*auxiliaryPotential s hs (profileEndpoint s hs u) y-
        externalField s y)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (auxiliaryPotential_endpoint_equilibrium_le s hs hu hy) hN)) hK

theorem uniform_weighted_trial_polynomial (s : ℝ) (hs : 0 < s) {δ N : ℝ}
    (hδ : 0 ≤ δ) (hN : 1 ≤ N) (n : ℕ) (hnδ : (n : ℝ)/N ≤ δ) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ, 0 ≤ y →
      |p.eval (N^2*y^2)|^2*Real.exp (-N*externalField s y) ≤
        trialPrefactor (s+δ)*N^(4*n+16)*Real.exp (N*profileEquilibrium s hs ((n : ℝ)/N)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨p, hpm, hpd, hp⟩ := uniform_auxiliary_trial_polynomial s hs hδ hN n hnδ
  refine ⟨p, hpm, hpd, ?_⟩
  intro y hy
  exact weighted_trial_bound s hs hNpos.le (by positivity) hy
    (mul_nonneg (trialPrefactor_pos _).le (by positivity))
    (hp y hy)

end Zeta5.Analysis
