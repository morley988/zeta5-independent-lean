import Zeta5.Analysis.AuxiliarySmallBall
import Zeta5.Analysis.ArcsinePotential
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual logarithmic potential equals its arcsine-mixture formula

All logarithms below are proved integrable against the constructed measure.
The pushforward and Fubini steps therefore relate ordinary Bochner integrals,
not formal expressions with unproved convergence assumptions.
-/

open MeasureTheory Set Filter

namespace Zeta5.Analysis

lemma integral_angleMeasure (f : ℝ → ℝ) :
    (∫ θ, f θ ∂angleMeasure) = (1/Real.pi)*(∫ θ in 0..Real.pi, f θ) := by
  rw [angleMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le Real.pi_pos.le]

lemma integral_radialMeasure (s : ℝ) (hs : 0 < s) (b : ℝ) (f : ℝ → ℝ) :
    (∫ a, f a ∂radialMeasure s hs b) = ∫ a in Ioc (0 : ℝ) b, f a*profileMassSlope s a := by
  rw [radialMeasure, integral_withDensity_eq_integral_toReal_smul
    (profileMassSlope_continuous hs).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro a ha
  dsimp only
  rw [ENNReal.toReal_ofReal (profileMassSlope_nonneg hs ha.1.le), smul_eq_mul, mul_comm]

lemma squaredAuxiliaryMeasure_restrict_Ioc (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    (squaredAuxiliaryMeasure s hs b).restrict (Ioc (0 : ℝ) (b^2)) =
      squaredAuxiliaryMeasure s hs b :=
  Measure.restrict_eq_self_of_ae_mem (squaredAuxiliaryMeasure_ae_mem_Ioc s hs hb)

/-- The true logarithmic kernel is integrable at every real evaluation point. -/
theorem squaredAuxiliaryMeasure_log_integrable (s : ℝ) (hs : 0 < s) {b : ℝ}
    (hb : 0 ≤ b) (v : ℝ) :
    Integrable (fun w : ℝ => Real.log |v-w|) (squaredAuxiliaryMeasure s hs b) := by
  have h := (log_integrableOn_and_truncated_integral_le
    (squaredAuxiliaryMeasure s hs b) (C := 3+(3/2 : ℝ)*b) (ε := 1)
    (by positivity) (by norm_num) (sq_nonneg b)
    (fun ρ hρ => squaredAuxiliaryMeasure_smallBall s hs hb v hρ)).1
  simpa only [IntegrableOn, squaredAuxiliaryMeasure_restrict_Ioc s hs hb] using h

lemma squaredAuxiliaryMeasure_intervalIntegral_log_eq (s : ℝ) (hs : 0 < s) {b : ℝ}
    (hb : 0 ≤ b) (v : ℝ) :
    (∫ w in 0..b^2, Real.log |v-w| ∂squaredAuxiliaryMeasure s hs b) =
      ∫ w, Real.log |v-w| ∂squaredAuxiliaryMeasure s hs b := by
  rw [intervalIntegral.integral_of_le (sq_nonneg b),
    squaredAuxiliaryMeasure_restrict_Ioc s hs hb]

noncomputable def mixturePotential (s b y : ℝ) : ℝ :=
  ∫ a in 0..b, profileMassSlope s a*arcsinePotential a y

noncomputable def auxiliaryPotential (s : ℝ) (hs : 0 < s) (b y : ℝ) : ℝ :=
  (1/2 : ℝ)*(∫ w, Real.log |y^2-w| ∂squaredAuxiliaryMeasure s hs b)

/-- Exact measure-theoretic identification of the logarithmic potential with
its scalar arcsine-mixture integral. -/
theorem auxiliaryPotential_eq_mixture (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) : auxiliaryPotential s hs b y = mixturePotential s b y := by
  have hm : Measurable (fun w : ℝ => Real.log |y^2-w|) := by fun_prop
  have hmapint : Integrable (fun p : ℝ × ℝ => Real.log |y^2-(p.1*Real.cos p.2)^2|)
      ((radialMeasure s hs b).prod angleMeasure) := by
    exact (integrable_map_measure hm.aestronglyMeasurable
      squaredAuxiliaryMap_measurable.aemeasurable).mp
        (squaredAuxiliaryMeasure_log_integrable s hs hb (y^2))
  have hmain : (∫ w, Real.log |y^2-w| ∂squaredAuxiliaryMeasure s hs b) =
      2*mixturePotential s b y := by
    calc
      _ = ∫ p : ℝ × ℝ, Real.log |y^2-(p.1*Real.cos p.2)^2|
          ∂(radialMeasure s hs b).prod angleMeasure := by
        rw [squaredAuxiliaryMeasure, integral_map squaredAuxiliaryMap_measurable.aemeasurable
          hm.aestronglyMeasurable]
      _ = ∫ a, ∫ θ, Real.log |y^2-(a*Real.cos θ)^2| ∂angleMeasure ∂radialMeasure s hs b :=
        integral_prod _ hmapint
      _ = ∫ a, 2*arcsinePotential a y ∂radialMeasure s hs b := by
        apply integral_congr_ae
        filter_upwards [radialMeasure_ae_mem s hs b] with a ha
        rw [integral_angleMeasure]
        exact (arcsineSquared_halfAngle ha.1 hy).2
      _ = 2*mixturePotential s b y := by
        rw [integral_radialMeasure]
        unfold mixturePotential
        rw [intervalIntegral.integral_of_le hb, ← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro a _
        ring
  unfold auxiliaryPotential
  rw [hmain]
  ring

/-- The concrete monic trial polynomial bound in potential notation. -/
theorem auxiliaryPotential_trial_polynomial (s : ℝ) (hs : 0 < s) {b N : ℝ}
    (hb : 0 ≤ b) (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)
    (hmass : profileMass s b = (n : ℝ)/N) :
    ∃ p : Polynomial ℝ, p.Monic ∧ p.natDegree = n ∧ ∀ y : ℝ,
      |p.eval (N^2*y^2)|^2 ≤
        Real.exp (8*(3+(3/2 : ℝ)*b)) * (1+b^2)^4 * N^(4*n+16) *
          Real.exp (4*N*auxiliaryPotential s hs b y) := by
  obtain ⟨p, hpmonic, hpdeg, hp⟩ := auxiliaryMeasure_trial_polynomial s hs hb hN n hn hmass
  refine ⟨p, hpmonic, hpdeg, ?_⟩
  intro y
  have hpy := hp (y^2)
  rw [squaredAuxiliaryMeasure_intervalIntegral_log_eq s hs hb] at hpy
  convert! hpy using 1 <;> dsimp [auxiliaryPotential] <;> ring

end Zeta5.Analysis
