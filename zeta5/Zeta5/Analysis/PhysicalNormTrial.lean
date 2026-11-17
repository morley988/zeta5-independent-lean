import Zeta5.Analysis.PhysicalNorm

/-! # Uniform actual norm bounds from the constructive potential trial -/

noncomputable section
namespace Zeta5.Analysis
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def normEnvelope (y : ℝ) : ℝ := (1 + y ^ 5) * Real.exp (-(Real.pi / 2) * y)

def normEnvelopeMass : ℝ := 1 / (Real.pi / 2) + 120 / (Real.pi / 2) ^ 6

theorem normEnvelope_integrable : IntegrableOn normEnvelope (Ioi 0) := by
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 0
        (by positivity : (0 : ℝ) < Real.pi / 2)
  have h5 : IntegrableOn (fun y : ℝ => y ^ 5 * Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [neg_mul] using
      PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 5
        (by positivity : (0 : ℝ) < Real.pi / 2)
  unfold normEnvelope
  simp only [add_mul, one_mul]
  exact h0.add h5

theorem normEnvelope_integral : (∫ y : ℝ in Ioi 0, normEnvelope y) = normEnvelopeMass := by
  unfold normEnvelope
  simp only [add_mul, one_mul]
  have h0 : IntegrableOn (fun y : ℝ => Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 0
      (by positivity : (0 : ℝ) < Real.pi / 2)
  have h5 : IntegrableOn (fun y : ℝ => y ^ 5 * Real.exp (-(Real.pi / 2) * y)) (Ioi 0) := by
    simpa only [neg_mul] using PhysicalMeasure.integrableOn_pow_mul_exp_neg_mul 5
      (by positivity : (0 : ℝ) < Real.pi / 2)
  rw [integral_add h0 h5]
  have hv0 := PhysicalMeasure.integral_pow_mul_exp_neg_mul 0
    (by positivity : (0 : ℝ) < Real.pi / 2)
  have hv5 := PhysicalMeasure.integral_pow_mul_exp_neg_mul 5
    (by positivity : (0 : ℝ) < Real.pi / 2)
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_one,
    Nat.reduceAdd, Nat.reduceMul, Nat.succ_eq_add_one, pow_zero, one_mul, zero_add,
    pow_one] at hv0 hv5
  simpa only [normEnvelopeMass, neg_mul] using congrArg₂ (· + ·) hv0 hv5


theorem normEnvelopeMass_pos : 0 < normEnvelopeMass := by unfold normEnvelopeMass; positivity

theorem exponential_tail_envelope {N y T : ℝ} (hN : 1 ≤ N) :
    Real.exp (-(Real.pi / 2) * N * max 0 (y - T)) ≤
      Real.exp ((Real.pi / 2) * T) * Real.exp (-(Real.pi / 2) * y) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm : 0 ≤ max 0 (y - T) := le_max_left _ _
  have hmul : max 0 (y - T) ≤ N * max 0 (y - T) := by nlinarith
  have hmax := le_max_right (0 : ℝ) (y - T)
  nlinarith [Real.pi_pos]

theorem windowSquaredNorm_scaled (N m : ℕ) (hN : 0 < N) (P : ℝ[X]) :
    windowSquaredNorm N m P = (N : ℝ) * ∫ y : ℝ in Ioi 0,
      P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * physicalCommonWeight N m ((N : ℝ) * y) := by
  have h := integral_comp_mul_left_Ioi'
    (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m x) 0
    (by exact_mod_cast hN : (0 : ℝ) < N)
  simpa only [windowSquaredNorm_integral, mul_zero, smul_eq_mul, mul_pow] using h.symm

/-- A single positive constant controls every degree in a fixed mass window.
The exponent 22 records only polynomial errors and disappears on the N² scale. -/
theorem exists_uniform_windowSquaredNorm_bound (s : ℝ) (hs : 0 < s) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ N m k : ℕ, 0 < N → (m : ℝ) / N = s → (k : ℝ) / N ≤ δ →
      ∃ P : ℝ[X], P.Monic ∧ P.natDegree = k ∧
        windowSquaredNorm N m P ≤ K * physicalWeightScale N m * (N : ℝ) ^ (4 * k + 22) *
          Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)) := by
  obtain ⟨C, hC, hdensity⟩ := PhysicalMeasure.exists_density_exponential_bound
  let K : ℝ := C * trialPrefactor (s + δ) * Real.exp ((Real.pi / 2) * tailThreshold s δ) *
    normEnvelopeMass
  have hK : 0 < K := by dsimp [K]; exact mul_pos (mul_pos (mul_pos hC
    (trialPrefactor_pos _)) (Real.exp_pos _)) normEnvelopeMass_pos
  refine ⟨K, hK, ?_⟩
  intro N m k hN hms hkδ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨P, hPm, hPk, hP⟩ := uniform_weighted_trial_polynomial_decay s hs hδ hN1 k hkδ
  refine ⟨P, hPm, hPk, ?_⟩
  let A : ℝ := C * (N : ℝ) ^ 5 * physicalWeightScale N m *
    (trialPrefactor (s + δ) * (N : ℝ) ^ (4 * k + 16) *
      Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N))) *
    Real.exp ((Real.pi / 2) * tailThreshold s δ)
  have hW : 0 < physicalWeightScale N m := physicalWeightScale_pos hN m
  have hT : 0 < trialPrefactor (s + δ) := trialPrefactor_pos _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint {y : ℝ} (hy : 0 < y) :
      P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * physicalCommonWeight N m ((N : ℝ) * y) ≤
        A * normEnvelope y := by
    have hw := physicalCommonWeight_scaled_bound hC hdensity N m hN hy
    rw [hms] at hw
    have htrial := hP y hy.le
    rw [sq_abs] at htrial
    have htail := exponential_tail_envelope (y := y) (T := tailThreshold s δ) hN1
    calc
      _ ≤ P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 *
          (C * (N : ℝ) ^ 5 * physicalWeightScale N m * (1 + y ^ 5) *
            Real.exp (-(N : ℝ) * externalField s y)) :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = (C * (N : ℝ) ^ 5 * physicalWeightScale N m * (1 + y ^ 5)) *
          (P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 * Real.exp (-(N : ℝ) * externalField s y)) := by ring
      _ ≤ (C * (N : ℝ) ^ 5 * physicalWeightScale N m * (1 + y ^ 5)) *
          (trialPrefactor (s + δ) * (N : ℝ) ^ (4 * k + 16) *
            Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)) *
              Real.exp (-(Real.pi / 2) * (N : ℝ) * max 0 (y - tailThreshold s δ))) := by
        exact mul_le_mul_of_nonneg_left htrial (by positivity [physicalWeightScale_pos hN m])
      _ ≤ (C * (N : ℝ) ^ 5 * physicalWeightScale N m * (1 + y ^ 5)) *
          (trialPrefactor (s + δ) * (N : ℝ) ^ (4 * k + 16) *
            Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)) *
              (Real.exp ((Real.pi / 2) * tailThreshold s δ) * Real.exp (-(Real.pi / 2) * y))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (by positivity))
          (by positivity)
      _ = _ := by dsimp [A, normEnvelope]; ring
  have hscaled : IntegrableOn (fun y : ℝ => P.eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 *
      physicalCommonWeight N m ((N : ℝ) * y)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m x) 0 hNr).mpr
        (by simpa only [mul_zero] using windowSquaredNorm_integrable N m P)
    simpa only [mul_pow] using h
  rw [windowSquaredNorm_scaled N m hN]
  have hI := integral_mono_ae hscaled (normEnvelope_integrable.const_mul A) (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact hpoint hy)
  rw [integral_const_mul, normEnvelope_integral] at hI
  apply (mul_le_mul_of_nonneg_left hI hNr.le).trans_eq
  dsimp [A, K]
  have hp : (N : ℝ) * (N : ℝ) ^ 5 * (N : ℝ) ^ (4 * k + 16) =
      (N : ℝ) ^ (4 * k + 22) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  calc
    _ = (C * trialPrefactor (s + δ) * Real.exp ((Real.pi / 2) * tailThreshold s δ) * normEnvelopeMass) *
        physicalWeightScale N m * ((N : ℝ) * (N : ℝ) ^ 5 * (N : ℝ) ^ (4 * k + 16)) *
          Real.exp ((N : ℝ) * profileEquilibrium s hs ((k : ℝ) / N)) := by ring
    _ = _ := by rw [hp]

end Zeta5.Analysis
