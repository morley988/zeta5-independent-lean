import Zeta5.Arithmetic.LocalDenominator
import Mathlib.LinearAlgebra.Lagrange

/-!
# Interpolation with unit differences

At distinct integral nodes whose pairwise differences are units at `p`,
Lagrange interpolation preserves coefficientwise lower valuation bounds.
Combining this with a high-coefficient bound gives the elementary
vanishing criterion needed on a maximal reflected residue class.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue

variable {p : ℕ} [Fact p.Prime]

theorem lagrangeBasis_integral {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℤ) {i : ι} (hi : i ∈ s)
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(p : ℤ) ∣ v i - v j) :
    PolynomialPadicLower p 0 (Lagrange.basis s (fun i => (v i : ℚ)) i) := by
  unfold Lagrange.basis
  have h := PolynomialPadicLower.prod (p := p) (s.erase i)
    (fun j => Lagrange.basisDivisor (v i : ℚ) (v j : ℚ)) (fun _ => 0) (by
      intro j hj
      obtain ⟨hji, hjs⟩ := mem_erase.mp hj
      have hunit : PadicLower p 0 (((v i : ℚ) - v j)⁻¹) := by
        simpa only [Int.cast_sub] using
          inverse_int_integral_of_not_dvd (p := p) (v i - v j) (hdiff i hi j hjs hji.symm)
      simpa only [Lagrange.basisDivisor, sub_eq_add_neg, zero_add] using
        (PolynomialPadicLower.constant hunit).mul
          (polynomialPadicLower_X.add (PolynomialPadicLower.constant (padicLower_int (v j))).neg))
  simpa using h

theorem polynomialPadicLower_of_interpolation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℤ) {P : ℚ[X]} {w : ℤ}
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(p : ℤ) ∣ v i - v j)
    (hdegree : P.degree < s.card)
    (heval : ∀ i ∈ s, PadicLower p w (P.eval (v i : ℚ))) :
    PolynomialPadicLower p w P := by
  have hv : Set.InjOn (fun i => (v i : ℚ)) s := by
    intro i hi j hj he
    by_contra hne
    change (v i : ℚ) = (v j : ℚ) at he
    have he' : v i = v j := by exact_mod_cast he
    exact hdiff i hi j hj hne (by rw [he', sub_self]; exact dvd_zero _)
  rw [Lagrange.eq_interpolate hv hdegree, Lagrange.interpolate_apply]
  apply PolynomialPadicLower.sum
  intro i hi
  simpa only [add_zero] using (PolynomialPadicLower.constant (heval i hi)).mul
    (lagrangeBasis_integral s v hi hdiff)

def coefficientTruncation (P : ℚ[X]) (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range n, C (P.coeff k) * X ^ k

theorem coefficientTruncation_coeff (P : ℚ[X]) (n k : ℕ) :
    (coefficientTruncation P n).coeff k = if k < n then P.coeff k else 0 := by
  simp [coefficientTruncation, finsetSum_coeff, coeff_C_mul_X_pow]

theorem coefficientTruncation_degree_lt (P : ℚ[X]) (n : ℕ) :
    (coefficientTruncation P n).degree < n := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  simp only [coefficientTruncation_coeff, if_neg (by omega : ¬k < n)]

theorem polynomialPadicLower_of_high_coeff_of_eval {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℤ) {P : ℚ[X]} {w : ℤ}
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(p : ℤ) ∣ v i - v j)
    (hhigh : ∀ k, s.card ≤ k → PadicLower p w (P.coeff k))
    (heval : ∀ i ∈ s, PadicLower p w (P.eval (v i : ℚ))) :
    PolynomialPadicLower p w P := by
  let T := coefficientTruncation P s.card
  have htail : PolynomialPadicLower p w (P - T) := by
    intro k
    rw [coeff_sub, coefficientTruncation_coeff]
    by_cases hk : k < s.card
    · rw [if_pos hk, sub_self]
      exact PadicLower.zero _
    · rw [if_neg hk, sub_zero]
      exact hhigh k (by omega)
  have hT : PolynomialPadicLower p w T := by
    apply polynomialPadicLower_of_interpolation s v hdiff (coefficientTruncation_degree_lt P s.card)
    intro i hi
    have he : T.eval (v i : ℚ) = P.eval (v i : ℚ) - (P - T).eval (v i : ℚ) := by
      rw [eval_sub]
      ring
    rw [he, sub_eq_add_neg]
    exact (heval i hi).add (htail.eval_integral (padicLower_int (v i))).neg
  have h := htail.add hT
  simpa only [sub_add_cancel] using h

theorem signedPhysicalRoot_injective (N : ℕ) :
    Function.Injective (@signedPhysicalRoot N) := by
  rintro ⟨i, bi⟩ ⟨j, bj⟩ he
  cases bi <;> cases bj <;> simp [signedPhysicalRoot] at he
  · exact Prod.ext (Fin.ext (by omega)) rfl
  · omega
  · omega
  · exact Prod.ext (Fin.ext (by omega)) rfl

theorem signedPhysicalRoot_bounds {N : ℕ} (i : Fin N × Bool) :
    -(N : ℤ) ≤ signedPhysicalRoot i ∧ signedPhysicalRoot i ≤ N := by
  rcases i with ⟨i, b⟩
  have hi := i.isLt
  cases b <;> simp only [signedPhysicalRoot, Bool.false_eq_true, ↓reduceIte,
    Nat.cast_add, Nat.cast_one] <;> omega

def physicalLocalLevel {N : ℕ} (p : ℕ) (c : ℤ) (i : Fin N × Bool) : ℤ :=
  (signedPhysicalRoot i - c) / p

theorem physicalLocalLevel_mul {N : ℕ} {c : ℤ} {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    (p : ℤ) * physicalLocalLevel p c i = signedPhysicalRoot i - c := by
  have hd := (mem_filter.mp hi).2
  apply Int.mul_ediv_cancel'
  simpa only [neg_sub] using (dvd_neg.mpr hd)

theorem physicalLocalLevel_reconstruct {N : ℕ} {c : ℤ} {i : Fin N × Bool}
    (hi : i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)) :
    (c : ℚ) + (p : ℚ) * (physicalLocalLevel p c i : ℚ) = (signedPhysicalRoot i : ℚ) := by
  have h := physicalLocalLevel_mul hi
  have hQ : (p : ℚ) * (physicalLocalLevel p c i : ℚ) = (signedPhysicalRoot i : ℚ) - c := by
    exact_mod_cast h
  linarith

theorem physicalLocalLevel_unit_differences {N : ℕ} (c : ℤ) (hsmall : 2 * N < p ^ 2) :
    ∀ i ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N),
      ∀ j ∈ divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N),
        i ≠ j → ¬(p : ℤ) ∣ physicalLocalLevel p c i - physicalLocalLevel p c j := by
  intro i hi j hj hne hd
  obtain ⟨a, ha⟩ := hd
  have hi' := physicalLocalLevel_mul hi
  have hj' := physicalLocalLevel_mul hj
  have he : signedPhysicalRoot i - signedPhysicalRoot j = (p : ℤ) ^ 2 * a := by
    calc
      signedPhysicalRoot i - signedPhysicalRoot j =
          (p : ℤ) * (physicalLocalLevel p c i - physicalLocalLevel p c j) := by linarith
      _ = _ := by rw [ha]; ring
  have hbi := signedPhysicalRoot_bounds i
  have hbj := signedPhysicalRoot_bounds j
  have hs : 2 * (N : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hsmall
  have ha0 : a = 0 := by
    by_contra ha0
    rcases lt_or_gt_of_ne ha0 with ha' | ha'
    · have ha1 : a ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left ha1 (sq_nonneg (p : ℤ))
      nlinarith
    · have ha1 : 1 ≤ a := by omega
      have hm := mul_le_mul_of_nonneg_left ha1 (sq_nonneg (p : ℤ))
      nlinarith
  have hroot : signedPhysicalRoot i = signedPhysicalRoot j := by rw [ha0, mul_zero] at he; omega
  exact hne (signedPhysicalRoot_injective N hroot)

end Zeta5.Arithmetic
