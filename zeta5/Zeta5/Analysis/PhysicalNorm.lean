import Zeta5.Analysis.RiemannWeight
import Zeta5.Analysis.PhysicalWeight
import Zeta5.Analysis.PotentialTail

/-! # Trial-polynomial norms for the actual physical measure -/

noncomputable section
namespace Zeta5.Analysis
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

def physicalCommonWeight (N m : ℕ) (x : ℝ) : ℝ :=
  (realWindowBasis m).eval (x ^ 2) ^ 2 * PhysicalMeasure.weightedDensity N x

def physicalWeightScale (N m : ℕ) : ℝ :=
  (Nat.factorial (2 * m) : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (4 * m) / (N : ℝ) ^ (2 * N)

def windowSquaredNorm (N m : ℕ) (P : ℝ[X]) : ℝ :=
  PhysicalMeasure.momentFunctional N ((realWindowBasis m) ^ 2 * P ^ 2)

theorem windowSquaredNorm_integral (N m : ℕ) (P : ℝ[X]) :
    windowSquaredNorm N m P = ∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m x := by
  rw [windowSquaredNorm, PhysicalMeasure.momentFunctional_apply]
  simp only [eval_mul, eval_pow, physicalCommonWeight]
  congr 1
  funext x
  ring

theorem windowSquaredNorm_integrable (N m : ℕ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x ^ 2) ^ 2 * physicalCommonWeight N m x) (Ioi 0) := by
  have h := PhysicalMeasure.weighted_polynomial_integrable N ((realWindowBasis m) ^ 2 * P ^ 2)
  simpa only [eval_mul, eval_pow, physicalCommonWeight, mul_assoc, mul_comm, mul_left_comm] using h

theorem physicalWeightScale_pos {N : ℕ} (hN : 0 < N) (m : ℕ) :
    0 < physicalWeightScale N m := by unfold physicalWeightScale; positivity

theorem physicalCommonWeight_nonneg (N m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ physicalCommonWeight N m x :=
  mul_nonneg (sq_nonneg _) (PhysicalMeasure.weightedDensity_pos N hx).le

theorem physicalCommonWeight_scaled_bound {C : ℝ} (hC : 0 < C)
    (hdensity : ∀ x : ℝ, 0 < x → PhysicalMeasure.density x ≤
      C * (1 + x ^ 5) * Real.exp (-(2 * Real.pi * x)))
    (N m : ℕ) (hN : 0 < N) {y : ℝ} (hy : 0 < y) :
    physicalCommonWeight N m ((N : ℝ) * y) ≤
      C * (N : ℝ) ^ 5 * physicalWeightScale N m * (1 + y ^ 5) *
        Real.exp (-(N : ℝ) * externalField ((m : ℝ) / N) y) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB := realWindowBasis_riemann_upper N m hN hy
  have hD := realDenominator_riemann_lower N hN hy
  have hd := hdensity ((N : ℝ) * y) (mul_pos hNr hy)
  have hpoly : 1 + ((N : ℝ) * y) ^ 5 ≤ (N : ℝ) ^ 5 * (1 + y ^ 5) := by
    have h : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ hN1
    rw [mul_pow]
    nlinarith
  have hd' : PhysicalMeasure.density ((N : ℝ) * y) ≤
      C * (N : ℝ) ^ 5 * (1 + y ^ 5) * Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) := by
    apply hd.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hC.le) (Real.exp_nonneg _)
  have hBsq : (realWindowBasis m).eval ((N : ℝ) ^ 2 * y ^ 2) ^ 2 ≤
      (Nat.factorial (2 * m) : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (4 * m) *
        Real.exp (2 * (N : ℝ) * externalIntegral ((m : ℝ) / N) y) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hB 2
    rw [sq_abs, mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul] at h
    have he : 2 * m * 2 = 4 * m := by omega
    simpa only [he, Nat.cast_ofNat, mul_assoc] using h
  have hDpos : 0 < (N : ℝ) ^ (2 * N) * Real.exp ((N : ℝ) * externalIntegral 1 y) := by positivity
  unfold physicalCommonWeight PhysicalMeasure.weightedDensity
  rw [mul_pow]
  calc
    _ ≤ ((Nat.factorial (2 * m) : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (4 * m) *
        Real.exp (2 * (N : ℝ) * externalIntegral ((m : ℝ) / N) y)) *
      ((C * (N : ℝ) ^ 5 * (1 + y ^ 5) * Real.exp (-(2 * Real.pi * ((N : ℝ) * y)))) /
        ((N : ℝ) ^ (2 * N) * Real.exp ((N : ℝ) * externalIntegral 1 y))) := by
      apply mul_le_mul hBsq _
        (div_nonneg (PhysicalMeasure.density_pos (mul_pos hNr hy)).le
          (PhysicalMeasure.realDenominator_eval_pos N (by positivity)).le) (by positivity)
      exact div_le_div₀ (by positivity) hd' hDpos hD
    _ = _ := by
      unfold physicalWeightScale externalField
      rw [div_mul_eq_div_mul_one_div, ← mul_assoc]
      have hexp : Real.exp (2 * (N : ℝ) * externalIntegral ((m : ℝ) / N) y) *
          Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) /
          Real.exp ((N : ℝ) * externalIntegral 1 y) =
            Real.exp (-(N : ℝ) *
              (2 * Real.pi * y + externalIntegral 1 y - 2 * externalIntegral ((m : ℝ) / N) y)) := by
        rw [← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      calc
        _ = (C * (N : ℝ) ^ 5 *
            ((Nat.factorial (2 * m) : ℝ)⁻¹ ^ 2 * (N : ℝ) ^ (4 * m) / (N : ℝ) ^ (2 * N)) *
            (1 + y ^ 5)) * (Real.exp (2 * (N : ℝ) * externalIntegral ((m : ℝ) / N) y) *
              Real.exp (-(2 * Real.pi * ((N : ℝ) * y))) /
                Real.exp ((N : ℝ) * externalIntegral 1 y)) := by ring
        _ = _ := by rw [hexp]

end Zeta5.Analysis
