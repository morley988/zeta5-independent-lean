import Zeta5.Analysis.PhysicalMeasureMoments
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# The physical polynomial functional and strict Gram positivity

This file proves positivity for the actual density divided by the manuscript's
`D_N`, on all polynomial squares.  Connecting these Gram entries to the
rational affine matrix still requires the separate Stieltjes identity.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

/-- Every real polynomial in `x²` is integrable against the physical density. -/
theorem polynomial_density_integrable (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval (x ^ 2) * density x) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, add_mul]
    exact hp.add hq
  | monomial n a =>
    simp only [eval_monomial, ← pow_mul, mul_assoc]
    exact (density_moment_integrable n).const_mul a

/-- `D_N` after mapping its rational coefficients to the reals. -/
def realDenominator (N : ℕ) : ℝ[X] :=
  (Zeta5.Construction.denominator N).map (Rat.castHom ℝ)

theorem realDenominator_eval_ge_one (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (realDenominator N).eval t := by
  simp only [realDenominator, Zeta5.Construction.denominator, Polynomial.map_prod,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, eval_prod, eval_add, eval_X, eval_C]
  apply Finset.one_le_prod
  intro i hi
  simp only [map_pow, map_add, map_natCast, map_one]
  have hi' : 1 ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  nlinarith

theorem realDenominator_eval_pos (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 < (realDenominator N).eval t := lt_of_lt_of_le zero_lt_one (realDenominator_eval_ge_one N ht)

/-- Density for the polynomial Gram form with denominator `D_N(x²)`. -/
def weightedDensity (N : ℕ) (x : ℝ) : ℝ :=
  density x / (realDenominator N).eval (x ^ 2)

theorem weightedDensity_pos (N : ℕ) {x : ℝ} (hx : 0 < x) : 0 < weightedDensity N x :=
  div_pos (density_pos hx) (realDenominator_eval_pos N (sq_nonneg x))

theorem weightedDensity_measurable (N : ℕ) : Measurable (weightedDensity N) := by
  unfold weightedDensity
  exact density_measurable.div ((realDenominator N).continuous.measurable.comp (measurable_id.pow_const 2))

theorem weighted_polynomial_integrable (N : ℕ) (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => p.eval (x ^ 2) * weightedDensity N x) (Ioi 0) := by
  apply (polynomial_density_integrable p).norm.mono'
    ((p.continuous.measurable.comp (measurable_id.pow_const 2)).mul
      (weightedDensity_measurable N)).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hd := realDenominator_eval_ge_one N (sq_nonneg x)
  have hdpos := realDenominator_eval_pos N (sq_nonneg x)
  calc
    ‖p.eval (x ^ 2) * weightedDensity N x‖ =
        ‖p.eval (x ^ 2) * density x‖ / (realDenominator N).eval (x ^ 2) := by
      simp only [weightedDensity, ← mul_div_assoc, norm_div, Real.norm_eq_abs, abs_of_pos hdpos]
    _ ≤ ‖p.eval (x ^ 2) * density x‖ := div_le_self (norm_nonneg _) hd

/-- The actual real polynomial functional defined by the positive density. -/
def momentFunctional (N : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ in Ioi 0, p.eval (x ^ 2) * weightedDensity N x
  map_add' p q := by
    simp only [eval_add, add_mul]
    exact integral_add (weighted_polynomial_integrable N p) (weighted_polynomial_integrable N q)
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]

theorem momentFunctional_apply (N : ℕ) (p : ℝ[X]) :
    momentFunctional N p = ∫ x : ℝ in Ioi 0, p.eval (x ^ 2) * weightedDensity N x := rfl

/-- A nonzero real polynomial has a nonzero evaluation at `x²` for almost every
real `x`; the possible exceptions form the finite root set of `p(X²)`. -/
theorem polynomial_square_argument_ne_zero_ae (p : ℝ[X]) (hp : p ≠ 0) :
    ∀ᵐ x : ℝ, p.eval (x ^ 2) ≠ 0 := by
  have hc : p.comp (X ^ 2) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hp, false_or, not_and_or]
    right
    intro h
    have hh := congrArg Polynomial.natDegree h
    norm_num at hh
  have hfinite : {x : ℝ | p.eval (x ^ 2) = 0}.Finite := by
    simpa only [Polynomial.IsRoot, eval_comp, eval_pow, eval_X] using
      Polynomial.finite_setOfPred_isRoot hc
  rw [ae_iff]
  simpa only [not_not] using hfinite.measure_zero volume

/-- Strict positivity on every nonzero square for the actual weighted density. -/
theorem momentFunctional_square_pos (N : ℕ) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < momentFunctional N (p ^ 2) := by
  have hpos : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 < (p ^ 2).eval (x ^ 2) * weightedDensity N x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi,
      ae_restrict_of_ae (polynomial_square_argument_ne_zero_ae p hp)] with x hx hp'
    rw [eval_pow]
    exact mul_pos (sq_pos_of_ne_zero hp') (weightedDensity_pos N hx)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => (p ^ 2).eval (x ^ 2) * weightedDensity N x) := hpos.mono (fun x hx => hx.le)
  have hi := weighted_polynomial_integrable N (p ^ 2)
  have hnonneg : 0 ≤ momentFunctional N (p ^ 2) := integral_nonneg_of_ae hn
  apply lt_of_le_of_ne hnonneg
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz.symm
  have hfalse : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), False := by
    filter_upwards [hpos, hzero] with x hx hz'
    exact (ne_of_gt hx) hz'
  have hvol : volume (Ioi (0 : ℝ)) ≠ 0 := by simp
  haveI : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot := (ae_restrict_neBot).mpr hvol
  obtain ⟨x, hx⟩ := Filter.Eventually.exists hfalse
  exact hx

/-- Unconditional strict positivity of each physical Gram determinant. -/
theorem physical_gram_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (p : ι → ℝ[X]) (hp : LinearIndependent ℝ p) :
    0 < (Zeta5.Analysis.polynomialGram (momentFunctional N) p).det :=
  Zeta5.Analysis.polynomialGram_det_pos (momentFunctional N) (momentFunctional_square_pos N) p hp

@[simp] theorem weightedDensity_zero (x : ℝ) : weightedDensity 0 x = density x := by
  simp [weightedDensity, realDenominator, Zeta5.Construction.denominator]

theorem momentFunctional_zero_monomial (k : ℕ) (a : ℝ) :
    momentFunctional 0 (Polynomial.monomial k a) =
      a * (Zeta5.Construction.rationalMoment k : ℝ) := by
  rw [momentFunctional_apply]
  simp only [eval_monomial, weightedDensity_zero, ← pow_mul, mul_assoc]
  rw [integral_const_mul, density_moment]

/-- The rational polynomial moment functional used in the matrix construction
is exactly integration against the physical density. -/
theorem momentFunctional_zero_rational (p : ℚ[X]) :
    momentFunctional 0 (p.map (Rat.castHom ℝ)) =
      (Zeta5.Construction.polynomialMoment p : ℝ) := by
  calc
    _ = momentFunctional 0 ((p.sum fun k a => monomial k a).map (Rat.castHom ℝ)) := by
      rw [sum_monomial_eq]
    _ = ∑ k ∈ p.support, (p.coeff k : ℝ) * (Zeta5.Construction.rationalMoment k : ℝ) := by
      simp only [Polynomial.sum_def, Polynomial.map_sum, Polynomial.map_monomial,
        map_sum, momentFunctional_zero_monomial, Rat.coe_castHom]
    _ = _ := by
      simp only [Zeta5.Construction.polynomialMoment, Polynomial.sum_def, Rat.cast_sum, Rat.cast_mul]

/-- The actual central-factorial basis, with real coefficients, is a polynomial sequence. -/
def windowBasisSequence : Polynomial.Sequence ℝ where
  elems' j := (Zeta5.Construction.windowBasis j).map (Rat.castHom ℝ)
  degree_eq' j := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree,
      Zeta5.Construction.windowBasis_natDegree]
    unfold Zeta5.Construction.windowBasis
    exact fun h => Zeta5.Construction.centralPolynomial_ne_zero j
      (Polynomial.comp_neg_X_eq_zero_iff.mp h)

/-- Consecutive windows in the manuscript's actual basis are independent. -/
theorem physical_window_basis_independent (m r : ℕ) :
    LinearIndependent ℝ
      (fun j : Fin r => (Zeta5.Construction.windowBasis (m + j.val)).map (Rat.castHom ℝ)) :=
  Zeta5.Analysis.sequence_window_linearIndependent windowBasisSequence m r

/-- Positivity of the unscaled physical determinant with the actual window. -/
theorem physical_window_gram_det_pos (N m r : ℕ) :
    0 < (Zeta5.Analysis.polynomialGram (momentFunctional N)
      (fun j : Fin r => (Zeta5.Construction.windowBasis (m + j.val)).map (Rat.castHom ℝ))).det :=
  physical_gram_det_pos N _ (physical_window_basis_independent m r)

/-- Positivity includes the manuscript's factor `(N!)²`. -/
theorem physical_scaled_window_gram_det_pos (N m r : ℕ) :
    0 < (((Nat.factorial N : ℝ) ^ 2) • Zeta5.Analysis.polynomialGram (momentFunctional N)
      (fun j : Fin r => (Zeta5.Construction.windowBasis (m + j.val)).map (Rat.castHom ℝ))).det := by
  exact Zeta5.Analysis.scaled_polynomialGram_det_pos (momentFunctional N)
    (momentFunctional_square_pos N) _ (physical_window_basis_independent m r) _ (by positivity)

end Zeta5.Analysis.PhysicalMeasure
