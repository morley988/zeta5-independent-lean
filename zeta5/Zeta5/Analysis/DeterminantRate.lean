import Zeta5.Analysis.NormRowRate
import Zeta5.Analysis.ProfileGrid
import Zeta5.Analysis.AnalyticError
import Zeta5.Analysis.GridIntegral
import Zeta5.Endpoint.PhysicalCriterion

/-!
# The analytic rate of the actual ζ(5) determinant

Every hypothesis concerning the physical density, the potential, the trial
polynomials, the factorial basis change and the Gram determinant is discharged.
The finite integral certificate therefore bounds the actual determinant.
-/

noncomputable section
namespace Zeta5.Analysis
open Real Set Filter Polynomial Zeta5.Endpoint
open scoped Topology BigOperators

def analyticEndpointDrop : ℝ :=
  analyticProfile (1 / 20) (by norm_num) 0 -
    analyticProfile (1 / 20) (by norm_num) (6 / 5)

theorem windowSquaredNorm_pos_of_monic (N m : ℕ) {P : ℝ[X]} (hP : P.Monic) :
    0 < windowSquaredNorm N m P := by
  have h := commonMomentFunctional_square_pos N m P hP.ne_zero
  rw [commonMomentFunctional_square_eq] at h
  exact pos_of_mul_pos_right h (sq_nonneg _)

/-- An explicit negligible remainder bounds the actual determinant at all
positive stages n. The constant C is independent of the stage and every row. -/
theorem exists_windowValue_log_bound : ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    Real.log (windowValue n) ≤
      -Zeta5.Certificate.analyticIntegral * windowScale n + analyticError C analyticEndpointDrop n := by
  obtain ⟨K, hK, hnorm⟩ := exists_uniform_windowSquaredNorm_bound
    (1 / 20) (by norm_num) (6 / 5) (by norm_num)
  refine ⟨Real.log K, ?_⟩
  intro n hn
  have hN : 0 < 20 * n := by omega
  have hNr : (0 : ℝ) < (20 * n : ℕ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hms : (n : ℝ) / (20 * n : ℕ) = (1 / 20 : ℝ) := by
    push_cast
    field_simp
  have hrδ : ((24 * n : ℕ) : ℝ) / (20 * n : ℕ) = (6 / 5 : ℝ) := by
    push_cast
    field_simp
    ring
  have hkδ (k : Fin (24 * n)) : (k.val : ℝ) / (20 * n : ℕ) ≤ (6 / 5 : ℝ) := by
    rw [← hrδ]
    apply div_le_div_of_nonneg_right _ hNr.le
    exact_mod_cast k.isLt.le
  have hpExists (k : Fin (24 * n)) := hnorm (20 * n) n k.val hN hms (hkδ k)
  choose p hpm hpd hpbound using hpExists
  have hdet := windowDeterminant_le_trial_norms n p hpm hpd
  change windowValue n ≤ _ at hdet
  have hprod : (∏ k : Fin (24 * n), gramNormFactor (20 * n) n k.val * windowSquaredNorm (20 * n) n (p k)) ≤
      ∏ k : Fin (24 * n), rowNormUpper K (1 / 20) (by norm_num) (20 * n) n k.val := by
    apply Finset.prod_le_prod
    · intro k hk
      exact mul_nonneg (gramNormFactor_pos _ _ _).le (windowSquaredNorm_pos_of_monic _ _ (hpm k)).le
    · intro k hk
      exact mul_le_mul_of_nonneg_left (hpbound k) (gramNormFactor_pos _ _ _).le
  have hbound := hdet.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hlog := Real.log_le_log (windowValue_pos n) hbound
  have hrows (k : Fin (24 * n)) := log_rowNormUpper_le_profile hK
    (by norm_num : (0 : ℝ) < 1 / 20) hN hms k.val
  have hupperPos (k : Fin (24 * n)) :
      0 < rowNormUpper K (1 / 20) (by norm_num) (20 * n) n k.val :=
    rowNormUpper_pos hK (by norm_num) hN n k.val
  rw [Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr (fun k _ => (hupperPos k).ne')),
    Real.log_prod (fun k _ => (hupperPos k).ne')] at hlog
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (24 * n)))) => hrows k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hgrid := analyticProfile_grid_upper (1 / 20) (by norm_num) hNr (24 * n)
  rw [hrδ] at hgrid
  rw [← Fin.sum_univ_eq_sum_range] at hgrid
  have hscaled := mul_le_mul_of_nonneg_left hgrid hNr.le
  have hmain : -(Zeta5.Certificate.analyticIntegral) * windowScale n =
      ((20 * n : ℕ) : ℝ) ^ 2 *
        (∫ u in (0 : ℝ)..(6 / 5 : ℝ), analyticProfile (1 / 20) (by norm_num) u) := by
    rw [Zeta5.Certificate.analyticIntegral_eq_neg_profileIntegral]
    simp only [neg_neg, windowScale, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hmain]
  unfold analyticError analyticEndpointDrop
  push_cast at hlog hsum hscaled ⊢
  nlinarith

/-- The actual analytic rate estimate, in the form required by the endpoint. -/
theorem exists_analytic_rate_error : ∃ E : ℕ → ℝ,
    Tendsto (fun n => E n / windowScale n) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, Real.log (windowValue n) ≤
      -Zeta5.Certificate.analyticIntegral * windowScale n + E n) := by
  obtain ⟨C, hC⟩ := exists_windowValue_log_bound
  refine ⟨analyticError C analyticEndpointDrop, analyticError_over_windowScale_limit C analyticEndpointDrop, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact hC n hn

end Zeta5.Analysis
