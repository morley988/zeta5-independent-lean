import Zeta5.Arithmetic.LocalInterpolation
import Zeta5.Arithmetic.LocalQuotient
import Zeta5.Arithmetic.CentralIntegerValued
import Zeta5.Construction.PartialFractions

/-!
# The actual central truncation on a maximal residue class

The polynomial `centralExpansion g N` agrees with `g` at every physical
square through `N²`. Its substituted high coefficients vanish modulo `p`
above `floor(2N/p)`. Unit-difference interpolation therefore transfers the
extra factor on a maximal restriction class to the whole truncation.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

theorem centralExpansion_squareValuedLower {g : ℚ[X]} {w : ℤ}
    (hg : SquareValuedLower p w g) (N : ℕ) :
    SquareValuedLower p w (centralExpansion g N) := by
  intro k
  rw [centralExpansion, eval_finsetSum]
  apply padicLower_sum
  intro a ha
  rw [eval_mul, eval_C]
  simpa only [add_zero] using (centralCoefficient_padicLower hg a).mul
    (centralStar_squareIntegral (p := p) a k)

def centralTail (N : ℕ) (g : ℚ[X]) : ℚ[X] :=
  (g - centralExpansion g N).comp (-X)

def centralQuotient (N : ℕ) (g : ℚ[X]) : ℚ[X] :=
  centralTail N g / denominator N

theorem denominator_dvd_centralTail (N : ℕ) (g : ℚ[X]) :
    denominator N ∣ centralTail N g := by
  rw [denominator_eq_nodal, Lagrange.nodal]
  apply prod_dvd_of_coprime
  · exact (pairwise_coprime_X_sub_C squarePole_injective).set_pairwise _
  · intro i hi
    rw [dvd_iff_isRoot]
    change (centralTail N g).eval (pole (i + 1)) = 0
    simp only [centralTail, eval_comp, eval_neg, eval_X, pole, neg_neg, eval_sub]
    rw [centralExpansion_eval_square g (show i + 1 ≤ N by simpa using mem_range.mp hi)]
    exact sub_self _

theorem centralTail_eq_denominator_mul_quotient (N : ℕ) (g : ℚ[X]) :
    centralTail N g = denominator N * centralQuotient N g := by
  exact (EuclideanDomain.mul_div_cancel' (denominator_ne_zero N) (denominator_dvd_centralTail N g)).symm

theorem centralTail_comp_square (N : ℕ) (g A : ℚ[X]) :
    (centralTail N g).comp (-(A ^ 2)) = g.comp (A ^ 2) - (centralExpansion g N).comp (A ^ 2) := by
  simp only [centralTail, comp_assoc, neg_comp, X_comp, neg_neg, sub_comp]

theorem centralTail_integerValued {g : ℚ[X]} (hg : SquareValuedLower p 0 g) (N : ℕ) :
    IntegerValuedAt p ((centralTail N g).comp (-(X ^ 2))) := by
  rw [centralTail_comp_square]
  intro k
  simp only [eval_sub, eval_comp, eval_pow, eval_X, sub_eq_add_neg, eval_add, eval_neg]
  exact (hg k).add (centralExpansion_squareValuedLower hg N k).neg

theorem centralTail_natDegree_le (N : ℕ) (g : ℚ[X]) :
    (centralTail N g).natDegree ≤ max g.natDegree N := by
  rw [centralTail, natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  exact (natDegree_sub_le _ _).trans (max_le_max le_rfl (centralExpansion_natDegree_le g N))

theorem centralSquareLocal_eval_level (N : ℕ) (g : ℚ[X]) (c : ℤ)
    {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    ((centralExpansion g N).comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) =
      (g.comp ((localAffine p c) ^ 2)).eval (physicalLocalLevel p c i : ℚ) := by
  simp only [eval_comp, eval_pow, localAffine, eval_add, eval_C, eval_mul, eval_X]
  rw [physicalLocalLevel_reconstruct hi]
  rcases i with ⟨i, b⟩
  have hiN : i.val + 1 ≤ N := by have := i.isLt; omega
  cases b <;> simp only [signedPhysicalRoot, Bool.false_eq_true, ↓reduceIte,
    Int.cast_neg, neg_sq, Int.cast_natCast]
  · exact centralExpansion_eval_square g hiN
  · exact centralExpansion_eval_square g hiN

theorem centralExpansion_maximal_local_gain {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : c ∈ maximalReflectedClasses N p)
    (hkernel : PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p 1 ((centralExpansion g N).comp ((localAffine p c) ^ 2)) := by
  have hcpair := mem_filter.mp hc
  obtain ⟨hcpos, hchalf⟩ := mem_Icc.mp hcpair.1
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcsmall : 2 * c < p := by omega
  have hsize : (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)).card =
      2 * (N / p) + 1 + 2 * (N % p) / p := by
    change physicalLocalMultiplicity N p c = _
    rw [physicalLocalMultiplicity_eq_reflectedSize N p c (by omega) hcsmall]
    exact hcpair.2
  have hfloor : 2 * N / p = 2 * (N / p) + 2 * (N % p) / p := by
    have hdecomp := Nat.mod_add_div N p
    conv_lhs => rw [← hdecomp]
    rw [mul_add, show 2 * (p * (N / p)) = p * (2 * (N / p)) by ring,
      Nat.add_mul_div_left _ _ hp]
    omega
  apply polynomialPadicLower_of_high_coeff_of_eval
    (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N))
    (physicalLocalLevel p c) (physicalLocalLevel_unit_differences (c : ℤ) hsmall)
  · intro k hk
    have hI : IntegerValuedAt p ((centralExpansion g N).comp (X ^ 2)) := by
      intro z
      simpa only [eval_comp, eval_pow, eval_X] using centralExpansion_squareValuedLower hg N z
    have hdeg : ((centralExpansion g N).comp (X ^ 2)).natDegree ≤ 2 * N := by
      rw [natDegree_comp, natDegree_X_pow]
      have := centralExpansion_natDegree_le g N
      omega
    have h := integerValuedAt_local_high_coeff hI hdeg hsmall (show 2 * N / p < k by
      rw [hsize] at hk
      omega) (c : ℤ)
    simpa only [comp_assoc, pow_comp, X_comp] using h
  · intro i hi
    rw [centralSquareLocal_eval_level N g c hi]
    exact hkernel.eval_integral (padicLower_int _)

theorem centralTail_maximal_local_gain {N c : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2)
    (hc : c ∈ maximalReflectedClasses N p)
    (hkernel : PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p 1 ((centralTail N g).comp (-(localAffine p c) ^ 2)) := by
  rw [centralTail_comp_square, sub_eq_add_neg]
  exact hkernel.add (centralExpansion_maximal_local_gain hg hsmall hc hkernel).neg

theorem centralQuotient_natDegree_le (N : ℕ) (g : ℚ[X]) :
    (centralQuotient N g).natDegree ≤ max g.natDegree N - N := by
  rw [centralQuotient, ← divByMonic_eq_div _ (denominator_monic N),
    natDegree_divByMonic _ (denominator_monic N), denominator_natDegree]
  exact Nat.sub_le_sub_right (centralTail_natDegree_le N g) N

theorem centralTail_negativeSquare_natDegree_le (N : ℕ) (g : ℚ[X]) :
    ((centralTail N g).comp (-(X ^ 2))).natDegree ≤ 2 * max g.natDegree N := by
  rw [natDegree_comp, natDegree_neg, natDegree_X_pow]
  have := centralTail_natDegree_le N g
  omega

theorem normalizedCentralQuotient_momentNumerator_natDegree_le (N : ℕ) (g : ℚ[X]) :
    (bernoulliMomentNumerator (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)).natDegree ≤
      2 * (max g.natDegree N - N) + 5 := by
  apply (bernoulliMomentNumerator_natDegree_le _).trans
  have h := (natDegree_C_mul_le ((N.factorial : ℚ) ^ 2) (centralQuotient N g)).trans
    (centralQuotient_natDegree_le N g)
  omega

theorem centralQuotient_moment_bound {N : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 6 < p ^ 2) :
    PadicLower p (-5 - ((2 * (N % p) / p : ℕ) : ℤ))
      (polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  apply normalized_quotient_moment_lower hp
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))
    (by omega) (centralTail_integerValued hg N)
    (centralTail_negativeSquare_natDegree_le N g) (by omega)
    (normalizedCentralQuotient_momentNumerator_natDegree_le N g) (by omega)
    (centralTail_eq_denominator_mul_quotient N g)

theorem centralQuotient_moment_bound_on_kernel {N : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 6 < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PadicLower p (-4 - ((2 * (N % p) / p : ℕ) : ℤ))
      (polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  apply normalized_quotient_moment_lower_on_kernel hp
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))
    (by omega) (centralTail_integerValued hg N)
    (centralTail_negativeSquare_natDegree_le N g) (by omega)
    (fun c hc => centralTail_maximal_local_gain hg (by omega) hc (hkernel c hc))
    (normalizedCentralQuotient_momentNumerator_natDegree_le N g) (by omega)
    (centralTail_eq_denominator_mul_quotient N g)

end Zeta5.Arithmetic
