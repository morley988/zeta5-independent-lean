import Zeta5.Reuse.AllocationBlocks
import Zeta5.Reuse.IndexBounds
import Zeta5.Construction.BasisChange

/-!
# Local residue matrices and the two Vandermonde gains

The rectangular determinant expansion is recycled from the four-value
proof.  Applying it in a translated monomial basis preserves the separate
cost of the high atoms.  Both selected exponent sums contribute, giving
the full quadratic cluster gain without a larger mixed-minor expansion.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Allocation
variable {p : ℕ} [Fact p.Prime]

def atomicMatrix {d : ℕ} (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (r : ℕ) :
    Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => ∑ a, w a * C ((x a) ^ (i.val + j.val))

theorem selected_card_le {k d : ℕ} (f : Fin k → Fin d)
    (hf : Function.Injective f) (s : Finset (Fin d)) :
    (Finset.univ.filter (fun i => f i ∈ s)).card ≤ min k s.card := by
  apply le_min
  · exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin k)
  · apply Finset.card_le_card_of_injOn f
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact hf.injOn

theorem polynomialPower_padicLower {x : ℚ} (hx : PadicLower p 1 x) (n : ℕ) :
    PolynomialPadicLower p (n : ℤ) (C (x ^ n)) := by
  simpa only [map_pow, mul_one] using (PolynomialPadicLower.constant hx).pow n

theorem atomicMinor_translated_bound {d r k : ℕ}
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hx : ∀ i, PadicLower p 1 (x i))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i))
    (rows cols : Fin k → Fin r)
    (hr : Function.Injective rows) (hc : Function.Injective cols) :
    PolynomialPadicLower p
      ((k : ℤ) * (k - 1) + k * base - 5 * (min k high.card : ℕ))
      ((atomicMatrix w x r).submatrix rows cols).det := by
  classical
  let A : Matrix (Fin k) (Fin d) ℚ[X] := fun i a => C ((x a) ^ (rows i).val)
  let B : Matrix (Fin d) (Fin k) ℚ[X] := fun a j => w a * C ((x a) ^ (cols j).val)
  have he : (atomicMatrix w x r).submatrix rows cols = A * B := by
    funext i j
    simp only [atomicMatrix, Matrix.submatrix_apply, Matrix.mul_apply, A, B,
      pow_add, map_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, rectangular_expansion]
  apply PolynomialPadicLower.sum
  intro f hf
  by_cases hinj : Function.Injective f
  · have hA : PolynomialPadicLower p (∑ i, ((rows i).val : ℤ))
        (A.submatrix id f).det := by
      have h := polynomialPadicLower_det_weighted (A.submatrix id f)
        (fun i => ((rows i).val : ℤ)) (fun _ => 0) 0 (by
          intro i j
          change PolynomialPadicLower p (((rows i).val : ℤ) + 0 + 0)
            (C ((x (f j)) ^ (rows i).val))
          simpa only [add_zero] using polynomialPower_padicLower (hx (f j)) (rows i).val)
      simpa using h
    have hB := PolynomialPadicLower.prod (p := p) Finset.univ
      (fun i => B (f i) i)
      (fun i => base - 5 * (if f i ∈ high then (1 : ℤ) else 0) + (cols i).val)
      (fun i _ => (hw (f i)).mul (polynomialPower_padicLower (hx (f i)) (cols i).val))
    have hhigh : (∑ i : Fin k, if f i ∈ high then (1 : ℤ) else 0) =
        ((Finset.univ.filter (fun i => f i ∈ high)).card : ℤ) := by simp
    have hcard : ((Finset.univ.filter (fun i => f i ∈ high)).card : ℤ) ≤
        (min k high.card : ℕ) := by exact_mod_cast selected_card_le f hinj high
    have hr' := twice_sum_injective_nat_lower (fun i => (rows i).val)
      (fun i j h => hr (Fin.ext h))
    have hc' := twice_sum_injective_nat_lower (fun i => (cols i).val)
      (fun i j h => hc (Fin.ext h))
    apply (hA.mul hB).mono
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hhigh]
    nlinarith
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    rw [Matrix.det_zero_of_column_eq hne (fun a => by simp [Matrix.submatrix_apply, hij]),
      zero_mul]
    exact PolynomialPadicLower.zero _

theorem atomic_translated_minorLower {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hx : ∀ i, PadicLower p 1 (x i))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r)
      (fun k => (k : ℤ) * (k - 1) + k * base - 5 * (min k high.card : ℕ)) := by
  intro k rows cols
  by_cases hr : Function.Injective rows
  · by_cases hc : Function.Injective cols
    · exact atomicMinor_translated_bound w x high base hx hw rows cols hr hc
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
      rw [Matrix.det_zero_of_column_eq hne (fun a => by simp [Matrix.submatrix_apply, hij])]
      exact PolynomialPadicLower.zero _
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hr
    have hrow : ((atomicMatrix w x r).submatrix rows cols) i =
        ((atomicMatrix w x r).submatrix rows cols) j := by
      funext a
      change atomicMatrix w x r (rows i) (cols a) = atomicMatrix w x r (rows j) (cols a)
      rw [hij]
    rw [Matrix.det_zero_of_row_eq hne hrow]
    exact PolynomialPadicLower.zero _

def atomicFunctional {d : ℕ} (w : Fin d → ℚ[X]) (x : Fin d → ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  ∑ a, (LinearMap.toSpanSingleton ℚ ℚ[X] (w a)).comp (Polynomial.leval (x a))

theorem atomicFunctional_apply {d : ℕ} (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (P : ℚ[X]) :
    atomicFunctional w x P = ∑ a, C (P.eval (x a)) * w a := by
  simp [atomicFunctional, Polynomial.smul_eq_C_mul]

theorem atomicFunctional_monomialGram {d : ℕ} (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (r : ℕ) :
    monomialGram (atomicFunctional w x) r = atomicMatrix w x r := by
  funext i j
  simp only [monomialGram, atomicFunctional_apply, eval_pow, eval_X, atomicMatrix]
  apply Finset.sum_congr rfl
  intro a ha
  ring

def shiftMatrix (r : ℕ) (c : ℚ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  coefficientMatrix r (fun j => (X + C c) ^ j.val)

theorem atomic_shift_congruence {d : ℕ} (w : Fin d → ℚ[X]) (x : Fin d → ℚ)
    (r : ℕ) (c : ℚ) :
    atomicMatrix w x r = (shiftMatrix r c).transpose *
      atomicMatrix w (fun a => x a - c) r * shiftMatrix r c := by
  have h := polynomialValuedGram_change_of_basis
    (atomicFunctional w (fun a => x a - c)) r (fun j => (X + C c) ^ j.val)
    (fun j => by simpa using j.isLt)
  rw [atomicFunctional_monomialGram] at h
  change _ = (coefficientMatrix r (fun j => (X + C c) ^ j.val)).transpose *
    atomicMatrix w (fun a => x a - c) r * coefficientMatrix r (fun j => (X + C c) ^ j.val)
  rw [← h]
  funext i j
  simp only [atomicMatrix, atomicFunctional_apply, eval_mul, eval_pow, eval_add, eval_X, eval_C]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sub_add_cancel, ← pow_add]
  ring

theorem shiftMatrix_integral (r : ℕ) {c : ℚ} (hc : PadicLower p 0 c) :
    ∀ i j, PolynomialPadicLower p 0 (shiftMatrix r c i j) := by
  intro i j
  apply PolynomialPadicLower.constant
  have h := ((polynomialPadicLower_X (p := p)).add
    (PolynomialPadicLower.constant hc)).pow j.val
  simpa only [mul_zero] using h i.val

theorem minorLower_integral_change {r : ℕ} (A U V : Matrix (Fin r) (Fin r) ℚ[X])
    (bound : ℕ → ℤ) (hA : MinorLower (p := p) A bound)
    (hU : ∀ i j, PolynomialPadicLower p 0 (U i j))
    (hV : ∀ i j, PolynomialPadicLower p 0 (V i j)) :
    MinorLower (p := p) (U * A * V) bound := by
  intro k rows cols
  have he : (U * A * V).submatrix rows cols =
      U.submatrix rows id * A * V.submatrix id cols := by
    rw [Matrix.submatrix_mul (U * A) V rows id cols Function.bijective_id,
      Matrix.submatrix_mul U A rows id id Function.bijective_id, Matrix.submatrix_id_id]
  rw [he]
  apply right_integral _ _ _ _ (fun i j => hV i (cols j))
  intro f
  have he' : (U.submatrix rows id * A).submatrix id f =
      U.submatrix rows id * A.submatrix id f := by
    funext i j
    simp [Matrix.mul_apply]
  rw [he']
  apply left_integral _ _ _ (fun i j => hU (rows i) j)
  intro g
  simpa only [Matrix.submatrix_submatrix, Function.comp_def, id_eq] using hA k g f

theorem atomic_minorLower {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d)) (base : ℤ)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (base - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r)
      (fun k => (k : ℤ) * (k - 1) + k * base - 5 * (min k high.card : ℕ)) := by
  rw [atomic_shift_congruence w x r c]
  apply minorLower_integral_change _ _ _ _
    (atomic_translated_minorLower r w (fun i => x i - c) high base hx hw)
  · intro i j
    exact shiftMatrix_integral r hc j i
  · exact shiftMatrix_integral r hc

#print axioms atomic_minorLower

end Zeta5.Arithmetic
