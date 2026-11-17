import Zeta5.Analysis.PhysicalMeasurePushforward
import Zeta5.Construction.Functional
import Zeta5.Endpoint.ZetaBridge

/-!
# The precise remaining Stieltjes interface for the affine matrix

The polynomial moments, the actual measure, and Gram positivity are proved
unconditionally in the imported modules.  This file derives the interpretation
of the affine matrix from one explicitly named Stieltjes hypothesis.  It does
not assert that hypothesis.
-/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial Zeta5.Construction
open scoped Topology BigOperators

private theorem realDenominator_eq_nodal (N : ℕ) :
    realDenominator N = Lagrange.nodal (Finset.range N)
      (fun i : ℕ => (pole (i + 1) : ℝ)) := by
  simp only [realDenominator, denominator_eq_nodal, Lagrange.nodal,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom]

/-- Partial fractions for an arbitrary rational numerator, evaluated on the
positive real half line. -/
theorem real_partialFractions (N : ℕ) (P : ℚ[X]) {t : ℝ} (ht : 0 ≤ t) :
    (P.map (Rat.castHom ℝ)).eval t / (realDenominator N).eval t =
      ((P / denominator N).map (Rat.castHom ℝ)).eval t +
        ∑ i ∈ Finset.range N,
          ((P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1)) : ℚ) : ℝ) /
            (t + ((i + 1 : ℕ) : ℝ) ^ 2) := by
  have hinj : Function.Injective (fun i : ℕ => (pole (i + 1) : ℝ)) :=
    Rat.cast_injective.comp squarePole_injective
  have hnode : ∀ i ∈ Finset.range N, t ≠ (pole (i + 1) : ℝ) := by
    intro i hi
    have hi' : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
    simp only [pole, Rat.cast_neg, Rat.cast_pow, Rat.cast_natCast]
    exact ne_of_gt (by nlinarith [sq_pos_of_pos hi'])
  have h := partialFraction_evaluation (Finset.range N)
    (fun i : ℕ => (pole (i + 1) : ℝ)) hinj.injOn (P.map (Rat.castHom ℝ)) t hnode
  rw [← realDenominator_eq_nodal] at h
  rw [h]
  congr 1
  · simp only [realDenominator, Polynomial.map_div]
  · apply Finset.sum_congr rfl
    intro i hi
    have heval (Q : ℚ[X]) : (Q.map (Rat.castHom ℝ)).eval (pole (i + 1) : ℝ) =
        ((Q.eval (pole (i + 1)) : ℚ) : ℝ) := by
      rw [eval_map]
      exact eval₂_at_apply (Rat.castHom ℝ) (pole (i + 1))
    rw [heval, show (realDenominator N).derivative =
      (denominator N).derivative.map (Rat.castHom ℝ) by
        simp only [realDenominator, derivative_map], heval]
    simp only [Rat.cast_div, pole, Rat.cast_neg, Rat.cast_pow, Rat.cast_natCast, sub_neg_eq_add]


/-- The one remaining analytic identity at the poles needed by the pencil.
This is a proposition, not an assumption or axiom of the development. -/
def StieltjesAtPositiveIntegers (z : ℝ) : Prop :=
  ∀ i : ℕ, 0 < i → stieltjesTransform (i : ℝ) = (stieltjes i).eval₂ (Rat.castHom ℝ) z

/-- Once the explicit Stieltjes identity is proved, the whole fixed-denominator
functional has its intended integral interpretation. -/
theorem momentFunctional_eq_numeratorFunctional {z : ℝ}
    (hStieltjes : StieltjesAtPositiveIntegers z) (N : ℕ) (P : ℚ[X]) :
    momentFunctional N (P.map (Rat.castHom ℝ)) =
      (numeratorFunctional N P).eval₂ (Rat.castHom ℝ) z := by
  let a (i : ℕ) : ℝ :=
    ((P.eval (pole (i + 1)) / (denominator N).derivative.eval (pole (i + 1)) : ℚ) : ℝ)
  have hi (i : ℕ) : Integrable (fun t : ℝ => a i / (t + ((i + 1 : ℕ) : ℝ) ^ 2))
      physicalMeasure := by
    simpa only [div_eq_mul_inv, one_mul] using
      (physicalMeasure_stieltjes_integrable (y := ((i + 1 : ℕ) : ℝ)) (by positivity)).const_mul (a i)
  rw [momentFunctional_eq_measure_integral]
  calc
    _ = ∫ t : ℝ, ((P / denominator N).map (Rat.castHom ℝ)).eval t +
        ∑ i ∈ Finset.range N, a i / (t + ((i + 1 : ℕ) : ℝ) ^ 2) ∂physicalMeasure := by
      apply integral_congr_ae
      filter_upwards [physicalMeasure_ae_pos] with t ht
      exact real_partialFractions N P ht.le
    _ = (Zeta5.Construction.polynomialMoment (P / denominator N) : ℝ) +
        ∑ i ∈ Finset.range N, a i * stieltjesTransform ((i + 1 : ℕ) : ℝ) := by
      rw [integral_add (physicalMeasure_polynomial_integrable _)
        (integrable_finsetSum _ (fun i _ => hi i)), physicalMeasure_polynomial_integral,
        integral_finsetSum _ (fun i _ => hi i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      simp only [div_eq_mul_inv, one_mul, integral_const_mul, stieltjesTransform]
    _ = _ := by
      rw [numeratorFunctional_apply]
      simp only [eval₂_add, eval₂_C, eval₂_finsetSum, eval₂_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi'
      rw [hStieltjes (i + 1) (by omega)]
      rfl

/-- Each actual affine matrix entry equals its physical Gram entry, conditional
only on the explicitly displayed Stieltjes identity. -/
theorem entry_eval_eq_physical_gram {z : ℝ}
    (hStieltjes : StieltjesAtPositiveIntegers z) (N j k : ℕ) :
    (entry N j k).eval₂ (Rat.castHom ℝ) z =
      (Nat.factorial N : ℝ) ^ 2 * momentFunctional N
        ((windowBasis j).map (Rat.castHom ℝ) * (windowBasis k).map (Rat.castHom ℝ)) := by
  rw [entry_eq_numeratorFunctional, eval₂_mul, eval₂_C,
    ← momentFunctional_eq_numeratorFunctional hStieltjes]
  simp only [Polynomial.map_mul, map_pow, map_natCast]

/-- The actual determinant is strictly positive once the sole remaining
Stieltjes identity for the matrix interpretation is supplied. -/
theorem windowDeterminant_pos_of_stieltjes {z : ℝ}
    (hStieltjes : StieltjesAtPositiveIntegers z) (n : ℕ) :
    0 < (windowDeterminant n).eval₂ (Rat.castHom ℝ) z := by
  rw [windowDeterminant_eval_real]
  have hM : (windowConstant n).map (Rat.castHom ℝ) + z • (windowLinear n).map (Rat.castHom ℝ) =
      ((Nat.factorial (20 * n) : ℝ) ^ 2) • Zeta5.Analysis.polynomialGram (momentFunctional (20 * n))
        (fun j : Fin (24 * n) => (windowBasis (n + j.val)).map (Rat.castHom ℝ)) := by
    ext j k
    have h := entry_eval_eq_physical_gram hStieltjes (20 * n) (n + j.val) (n + k.val)
    simpa only [entry, eval₂_add, eval₂_C, eval₂_mul, eval₂_X, windowConstant, windowLinear,
      Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Zeta5.Analysis.polynomialGram] using h
  rw [hM]
  exact physical_scaled_window_gram_det_pos (20 * n) n (24 * n)

theorem windowDeterminant_ne_zero_of_stieltjes {z : ℝ}
    (hStieltjes : StieltjesAtPositiveIntegers z) (n : ℕ) : windowDeterminant n ≠ 0 := by
  intro h
  have hpos := windowDeterminant_pos_of_stieltjes hStieltjes n
  simpa [h] using hpos

end Zeta5.Analysis.PhysicalMeasure
