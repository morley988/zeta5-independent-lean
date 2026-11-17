import Zeta5.Arithmetic.PadicResidue
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A restriction kernel supplies determinant valuation

A basis of the kernel over the residue field is extended to a full basis and
lifted to rational local integers. The lifted change of rows has unit
 determinant. Every kernel row gains a factor of p in every coefficient.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Module Matrix Polynomial Finset OddZeta.FourValue
open scoped BigOperators

/-- Extend a basis of a kernel to a square matrix of independent rows. -/
theorem exists_kernel_row_basis {K ι ρ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype ρ]
    (f : (ι → K) →ₗ[K] (ρ → K)) :
    ∃ T : Matrix ι ι K, ∃ s : Finset ι,
      T.det ≠ 0 ∧ s.card = finrank K (LinearMap.ker f) ∧
      ∀ i ∈ s, f (T i) = 0 := by
  classical
  let S := LinearMap.ker f
  let b₀ := Module.finBasis K S
  let v : Fin (finrank K S) → (ι → K) := fun i => (b₀ i : ι → K)
  have hv : LinearIndependent K v := by
    exact b₀.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let B := Module.Basis.extend hv.linearIndepOn_id
  letI := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card (hv.linearIndepOn_id.extend (Set.subset_univ _)) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq hcard
  let b := B.reindex e
  let j : Fin (finrank K S) → ι := fun k =>
    e ⟨v k, hv.linearIndepOn_id.subset_extend (Set.subset_univ _) (Set.mem_range_self k)⟩
  have hj : Function.Injective j := by
    intro k l h
    apply hv.injective
    exact congrArg (fun z : hv.linearIndepOn_id.extend (Set.subset_univ _) => (z : ι → K)) (e.injective h)
  have hbj (k : Fin (finrank K S)) : b (j k) = v k := by
    simp [b, j, Module.Basis.reindex_apply, B, Module.Basis.extend_apply_self]
  refine ⟨fun i k => b i k, Finset.univ.image j, ?_, ?_, ?_⟩
  · have h := (Pi.basisFun K ι).isUnit_det b
    rw [Pi.basisFun_det_apply] at h
    exact h.ne_zero
  · rw [Finset.card_image_of_injective _ hj]
    simp [S]
  · intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    change f (b (j k)) = 0
    rw [hbj]
    exact (b₀ k).property


variable {p : ℕ} [Fact p.Prime]

/-- A coefficientwise radical containing the restriction kernel gives one
factor of p for each dimension not detected by the restriction map. -/
theorem polynomialPadicLower_det_of_restriction_kernel
    {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]
    (A : Matrix ι ι ℚ[X]) (R : Matrix ρ ι ℚ)
    (hA : ∀ i j, PolynomialPadicLower p 0 (A i j))
    (hR : ∀ a i, PadicLower p 0 (R a i))
    (hker : ∀ x : ι → ℚ, (∀ i, PadicLower p 0 (x i)) →
      (∀ a, PadicLower p 1 (∑ i, R a i * x i)) →
      ∀ j, PolynomialPadicLower p 1 (∑ i, C (x i) * A i j)) :
    PolynomialPadicLower p
      ((Fintype.card ι : ℤ) - min (Fintype.card ι) (Fintype.card ρ)) A.det := by
  classical
  let RI : Matrix ρ ι (padicIntegralSubring p) := fun a i => ⟨R a i, hR a i⟩
  let Rbar : Matrix ρ ι (PadicResidueField p) := RI.map (padicReduction p)
  obtain ⟨T, s, hT, hs, hTs⟩ := exists_kernel_row_basis Rbar.mulVecLin
  choose TL hTL using fun i j => padicReduction_surjective (p := p) (T i j)
  let TI : Matrix ι ι (padicIntegralSubring p) := Matrix.of TL
  let TQ : Matrix ι ι ℚ := fun i j => (TL i j : ℚ)
  have hTQ (i j : ι) : PadicLower p 0 (TQ i j) := (TL i j).property
  have hmap : (padicReduction p).mapMatrix TI = T := by
    ext i j
    exact hTL i j
  have hredDet : padicReduction p (TI.det) ≠ 0 := by
    rw [RingHom.map_det, hmap]
    exact hT
  have hdetval : ((TI.det : padicIntegralSubring p) : ℚ) = TQ.det := by
    exact (padicIntegralSubring p).subtype.map_det TI
  have hinv : PadicLower p 0 (TQ.det⁻¹) := by
    rw [← hdetval]
    exact padicReduction_ne_zero_inv hredDet
  have hdet0 : TQ.det ≠ 0 := by
    intro h0
    apply hredDet
    apply (padicReduction_eq_zero _).mpr
    rw [hdetval, h0]
    exact PadicLower.zero 1
  have hRker (i : ι) (hi : i ∈ s) (a : ρ) :
      PadicLower p 1 (∑ j, R a j * TQ i j) := by
    have hh : padicReduction p (∑ j, RI a j * TL i j) = 0 := by
      simp only [map_sum, map_mul, hTL]
      exact congrFun (hTs i hi) a
    have hk := (padicReduction_eq_zero _).mp hh
    simpa [RI, TQ] using hk
  let U : Matrix ι ι ℚ[X] := C.mapMatrix TQ * A
  have hU (i j : ι) : PolynomialPadicLower p (if i ∈ s then 1 else 0) (U i j) := by
    dsimp only [U]
    rw [Matrix.mul_apply]
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, Matrix.map_apply, RingHom.mapMatrix_apply]
      exact hker (TQ i) (hTQ i) (hRker i hi) j
    · simp only [hi, ↓reduceIte, Matrix.map_apply, RingHom.mapMatrix_apply]
      apply PolynomialPadicLower.sum
      intro k hk
      simpa using (PolynomialPadicLower.constant (hTQ i k)).mul (hA k j)
  have hUdet : PolynomialPadicLower p (s.card : ℤ) U.det := by
    have hh := polynomialPadicLower_det_weighted (p := p) U
      (fun i => if i ∈ s then 1 else 0) (fun _ => 0) 0
      (fun i j => by simpa using hU i j)
    simpa using hh
  have hAdet : PolynomialPadicLower p (s.card : ℤ) A.det := by
    have hh := (PolynomialPadicLower.constant hinv).mul hUdet
    have hid : C (TQ.det⁻¹) * U.det = A.det := by
      dsimp [U]
      rw [Matrix.det_mul, ← RingHom.map_det, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hdet0, map_one, one_mul]
    simpa only [zero_add, hid] using hh
  apply hAdet.mono
  have hnull := Rbar.mulVecLin.finrank_range_add_finrank_ker
  have hrange := (LinearMap.range Rbar.mulVecLin).finrank_le
  rw [Module.finrank_fintype_fun_eq_card] at hnull hrange
  rw [hs]
  omega

end Zeta5.Arithmetic
