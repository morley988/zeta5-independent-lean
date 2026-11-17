import Zeta5.Analysis.Profile
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Hom.Set

/-!
# The inverse endpoint of the analytic profile

The endpoint is constructed from the actual mass formula, rather than
postulated as a function with inverse and derivative assumptions.
-/

namespace Zeta5.Analysis

open scoped NNReal

noncomputable section

def profileMassNNReal (s : ℝ) (hs : 0 < s) (b : ℝ≥0) : ℝ≥0 :=
  ⟨profileMass s b, profileMass_nonneg hs b.coe_nonneg⟩

theorem profileMassNNReal_strictMono (s : ℝ) (hs : 0 < s) :
    StrictMono (profileMassNNReal s hs) := by
  intro a b hab
  exact profileMass_strictMonoOn hs a.coe_nonneg b.coe_nonneg hab

theorem profileMassNNReal_surjective (s : ℝ) (hs : 0 < s) :
    Function.Surjective (profileMassNNReal s hs) := by
  intro u
  obtain ⟨b, hb, hbu⟩ := exists_profileMass_eq hs u.coe_nonneg
  refine ⟨⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  exact hbu

def profileMassOrderIso (s : ℝ) (hs : 0 < s) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (profileMassNNReal s hs)
    (profileMassNNReal_strictMono s hs) (profileMassNNReal_surjective s hs)

def profileEndpoint (s : ℝ) (hs : 0 < s) (u : ℝ) : ℝ :=
  ((profileMassOrderIso s hs).symm u.toNNReal : ℝ)

theorem profileEndpoint_nonneg (s : ℝ) (hs : 0 < s) (u : ℝ) :
    0 ≤ profileEndpoint s hs u :=
  NNReal.coe_nonneg _

theorem profileMass_endpoint (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 ≤ u) :
    profileMass s (profileEndpoint s hs u) = u := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((profileMassOrderIso s hs).apply_symm_apply u.toNNReal)
  change profileMass s (profileEndpoint s hs u) = (u.toNNReal : ℝ) at h
  simpa only [Real.coe_toNNReal u hu] using h

theorem profileEndpoint_mass (s : ℝ) (hs : 0 < s) {b : ℝ} (hb : 0 ≤ b) :
    profileEndpoint s hs (profileMass s b) = b := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ))
    ((profileMassOrderIso s hs).symm_apply_apply (⟨b, hb⟩ : ℝ≥0))
  have hm : (profileMass s b).toNNReal = profileMassNNReal s hs ⟨b, hb⟩ := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (profileMass_nonneg hs hb)
  change ((profileMassOrderIso s hs).symm (profileMassNNReal s hs ⟨b, hb⟩) : ℝ) = b at h
  simpa only [profileEndpoint, hm] using h

@[simp] theorem profileEndpoint_zero (s : ℝ) (hs : 0 < s) :
    profileEndpoint s hs 0 = 0 := by
  simpa only [profileMass_zero hs.le] using profileEndpoint_mass s hs (b := 0) le_rfl

theorem profileEndpoint_pos (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    0 < profileEndpoint s hs u := by
  have hn := profileEndpoint_nonneg s hs u
  have hmass := profileMass_endpoint s hs hu.le
  by_contra! h
  have hz : profileEndpoint s hs u = 0 := le_antisymm h hn
  rw [hz, profileMass_zero hs.le] at hmass
  linarith

theorem profileEndpoint_continuous (s : ℝ) (hs : 0 < s) :
    Continuous (profileEndpoint s hs) :=
  NNReal.continuous_coe.comp ((profileMassOrderIso s hs).symm.continuous.comp
    continuous_real_toNNReal)

theorem profileEndpoint_hasDerivAt (s : ℝ) (hs : 0 < s) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (profileEndpoint s hs)
      (profileMassSlope s (profileEndpoint s hs u))⁻¹ u := by
  apply HasDerivAt.of_local_left_inverse (profileEndpoint_continuous s hs).continuousAt
    (profileMass_hasDerivAt hs)
    (ne_of_gt (profileMassSlope_pos hs (profileEndpoint_pos s hs hu)))
  filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
  exact profileMass_endpoint s hs hv.le

end

end Zeta5.Analysis
