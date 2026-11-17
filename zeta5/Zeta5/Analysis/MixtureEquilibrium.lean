import Zeta5.Analysis.AuxiliaryPotential
import Zeta5.Analysis.ArcsineGrowth
import Zeta5.Analysis.EquilibriumKernel
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Equilibrium of the actual positive mixture potential

The positive Abel representation and a fully justified Fubini interchange show
that the potential grows with the external-field slope until the support ends,
and grows no faster thereafter.  The explicit value of the constant at zero
is evaluated in a separate scalar calculation.
-/

open MeasureTheory Set Filter

namespace Zeta5.Analysis

noncomputable def basePotential (s b : ℝ) : ℝ :=
  ∫ a in 0..b, profileMassSlope s a*Real.log (a/2)

noncomputable def truncatedAbel (s b t : ℝ) : ℝ :=
  ∫ a in 0..b, profileMassSlope s a*abelKernel t a

lemma basePotential_intervalIntegrable (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun a => profileMassSlope s a*Real.log (a/2)) volume 0 b := by
  have hlog : IntervalIntegrable (fun a : ℝ => Real.log a-Real.log 2) volume 0 b :=
    intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const
  have hlogdiv : IntervalIntegrable (fun a : ℝ => Real.log (a/2)) volume 0 b := by
    apply hlog.congr_uIoo
    rw [uIoo_of_le hb]
    intro a ha
    exact (Real.log_div ha.1.ne' (by norm_num)).symm
  exact hlogdiv.continuousOn_mul (profileMassSlope_continuous hs).continuousOn

lemma truncatedAbel_intervalIntegrable (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    IntervalIntegrable (truncatedAbel s b) volume 0 y := by
  have hprod := profileMassSlope_abel_prod_integrable s hs (y := y) hb
  have houter := hprod.integral_prod_right
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  change Integrable (fun t => ∫ a in 0..b, profileMassSlope s a*abelKernel t a)
    (volume.restrict (Ioc 0 y))
  simpa only [intervalIntegral.integral_of_le hb] using houter

/-- The actual scalar mixture potential equals its value at zero plus a
positive-kernel integral.  Joint integrability is supplied by the preceding
Abel estimates. -/
theorem mixturePotential_growth (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    mixturePotential s b y = basePotential s b+(∫ t in 0..y, truncatedAbel s b t) := by
  have hprod := profileMassSlope_abel_prod_integrable s hs (y := y) hb
  have hbase := (basePotential_intervalIntegrable s hs hb).1
  have hleft := hprod.integral_prod_left
  have heq : (fun a => profileMassSlope s a*arcsinePotential a y) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) b)]
      (fun a => profileMassSlope s a*Real.log (a/2) +
        ∫ t in Ioc (0 : ℝ) y, profileMassSlope s a*abelKernel t a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with a ha
    rw [(arcsinePotential_eq_log_add_abel ha.1 hy).2, mul_add,
      intervalIntegral.integral_of_le hy, integral_const_mul]
  unfold mixturePotential basePotential
  rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb,
    integral_congr_ae heq, integral_add hbase hleft]
  congr 1
  rw [integral_integral_swap hprod]
  simp only [truncatedAbel, intervalIntegral.integral_of_le hy,
    intervalIntegral.integral_of_le hb]

theorem mixturePotential_le_base_add_slope (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    mixturePotential s b y ≤ basePotential s b+(∫ t in 0..y, equilibriumSlope s t) := by
  rw [mixturePotential_growth s hs hb hy]
  apply add_le_add_right
  apply intervalIntegral.integral_mono_on_of_le_Ioo hy
    (truncatedAbel_intervalIntegrable s hs hb hy)
    ((equilibriumSlope_continuous s).intervalIntegrable 0 y)
  intro t ht
  exact (profileMassSlope_abel_truncated s hs hb ht.1).2.1

theorem mixturePotential_eq_base_add_slope (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hy : 0 ≤ y) (hyb : y ≤ b) :
    mixturePotential s b y = basePotential s b+(∫ t in 0..y, equilibriumSlope s t) := by
  rw [mixturePotential_growth s hs (hy.trans hyb) hy]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hy
  intro t ht
  exact (profileMassSlope_abel_truncated s hs (hy.trans hyb) ht.1).2.2 (ht.2.le.trans hyb)

/-- The equilibrium inequality for the logarithmic potential of the actual
positive measure, expressed with the integrated external-field slope. -/
theorem auxiliaryPotential_le_base_add_slope (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) :
    auxiliaryPotential s hs b y ≤ basePotential s b+(∫ t in 0..y, equilibriumSlope s t) := by
  rw [auxiliaryPotential_eq_mixture s hs hb hy]
  exact mixturePotential_le_base_add_slope s hs hb hy

/-- Equality holds throughout the support interval. -/
theorem auxiliaryPotential_eq_base_add_slope (s : ℝ) (hs : 0 < s) {b y : ℝ}
    (hy : 0 ≤ y) (hyb : y ≤ b) :
    auxiliaryPotential s hs b y = basePotential s b+(∫ t in 0..y, equilibriumSlope s t) := by
  rw [auxiliaryPotential_eq_mixture s hs (hy.trans hyb) hy]
  exact mixturePotential_eq_base_add_slope s hs hy hyb

lemma auxiliaryPotential_zero (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    auxiliaryPotential s hs b 0 = basePotential s b := by
  simpa using auxiliaryPotential_eq_base_add_slope s hs (le_refl (0 : ℝ)) hb

end Zeta5.Analysis
