import Zeta5.Arithmetic.SmallPrimeProper

/-!
# The actual all-prime logarithmic entry and determinant bound

The product of two central polynomials is expanded in the integral square-node
basis.  Proper residues, the constant quotient, and all higher polynomial
quotients have been bounded in the imported modules.  The only fixed loss is
the exact factor `96 = 24 · 2²`.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

theorem numeratorFunctional_scaledCentral_padicLower (N R l : ℕ)
    (hNR : N ≤ R) (hl : l ≤ 2*R-2) :
    PolynomialPadicLower p (-9*(Nat.log p (4*R+4) : ℤ)-(padicValNat p 24 : ℤ))
      (numeratorFunctional N (scaledCentralNumerator N l)) := by
  by_cases hlN : l ≤ N
  · exact numeratorFunctional_scaledCentral_proper_padicLower_log N l (4*R+4) hlN (by omega)
  · let k := l-N-1
    have hrep : N+k+1 = l := by dsimp [k]; omega
    rw [← hrep, numeratorFunctional_scaledCentral_high]
    exact PolynomialPadicLower.constant (centralQuotientMoment_padicLower_log N k (4*R+4)
      (by omega) (by omega))

lemma scaledCentralProduct_expansion (N j k : ℕ) {d : ℕ → ℚ}
    (hd : centralPolynomial j*centralPolynomial k =
      ∑ a ∈ range (j+k+1), C (d a)*centralPolynomial a) :
    C ((Nat.factorial N : ℚ)^2)*(windowBasis j*windowBasis k) =
      ∑ a ∈ range (j+k+1), C (d a)*scaledCentralNumerator N a := by
  have he := congrArg (fun P : ℚ[X] => P.comp (-X)) hd
  simp only [mul_comp, Polynomial.sum_comp, C_comp] at he
  change windowBasis j*windowBasis k =
    ∑ a ∈ range (j+k+1), C (d a)*windowBasis a at he
  rw [he, mul_sum]
  apply sum_congr rfl
  intro a _
  unfold scaledCentralNumerator
  ring

lemma entry_central_expansion (N j k : ℕ) {d : ℕ → ℚ}
    (hd : centralPolynomial j*centralPolynomial k =
      ∑ a ∈ range (j+k+1), C (d a)*centralPolynomial a) :
    entry N j k = ∑ a ∈ range (j+k+1),
      C (d a)*numeratorFunctional N (scaledCentralNumerator N a) := by
  rw [entry_eq_numeratorFunctional]
  have he : C ((Nat.factorial N : ℚ)^2)*numeratorFunctional N (windowBasis j*windowBasis k) =
      numeratorFunctional N (C ((Nat.factorial N : ℚ)^2)*(windowBasis j*windowBasis k)) := by
    simpa only [Polynomial.smul_eq_C_mul] using
      ((numeratorFunctional N).map_smul ((Nat.factorial N : ℚ)^2) (windowBasis j*windowBasis k)).symm
  rw [he, scaledCentralProduct_expansion N j k hd, map_sum]
  apply sum_congr rfl
  intro a _
  simpa only [Polynomial.smul_eq_C_mul] using
    (numeratorFunctional N).map_smul (d a) (scaledCentralNumerator N a)

lemma padicValNat_ninetySix (p : ℕ) [Fact p.Prime] :
    padicValNat p 96 = padicValNat p 24+2*padicValNat p 2 := by
  rw [show 96 = 24*2^2 by norm_num, padicValNat.mul (by norm_num) (by norm_num), padicValNat.pow]

/-- The manuscript's actual small-prime entry bound, valid at every prime.
The hypothesis `N≤R` covers the chosen window parameters. -/
theorem entry_smallPrime_padicLower (N R j k : ℕ) (hNR : N ≤ R) (hj : j < R) (hk : k < R) :
    PolynomialPadicLower p (-9*(Nat.log p (4*R+4) : ℤ)-(padicValNat p 96 : ℤ))
      (entry N j k) := by
  obtain ⟨d, hd, he⟩ := centralProduct_expansion (p := p) j k
  rw [entry_central_expansion N j k he]
  apply PolynomialPadicLower.sum
  intro a ha
  have hT := numeratorFunctional_scaledCentral_padicLower (p := p) N R a hNR
    (by have := mem_range.mp ha; omega)
  have h := (PolynomialPadicLower.constant (hd a)).mul hT
  convert! h using 1
  rw [padicValNat_ninetySix]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem windowPencil_smallPrime_padicLower (n : ℕ) (i j : Fin (24*n)) :
    PolynomialPadicLower p (-9*(Nat.log p (100*n+4) : ℤ)-(padicValNat p 96 : ℤ))
      (windowPencil n i j) := by
  have h := entry_smallPrime_padicLower (p := p) (20*n) (25*n) (n+i.val) (n+j.val)
    (by omega) (by have := i.isLt; omega) (by have := j.isLt; omega)
  simpa only [windowPencil, show 4*(25*n)+4 = 100*n+4 by omega] using h

/-- All coefficients of the actual determinant have the logarithmic
small-prime loss times the matrix dimension. -/
theorem windowDeterminant_smallPrime_padicLower (n : ℕ) :
    PolynomialPadicLower p
      (-((24*n : ℕ) : ℤ)*(9*(Nat.log p (100*n+4) : ℤ)+(padicValNat p 96 : ℤ)))
      (windowDeterminant n) := by
  have h := polynomialPadicLower_det_weighted (p := p) (windowPencil n)
    (fun _ => 0) (fun _ => 0)
    (-9*(Nat.log p (100*n+4) : ℤ)-(padicValNat p 96 : ℤ))
    (fun i j => by simpa using windowPencil_smallPrime_padicLower (p := p) n i j)
  simp only [sum_const_zero, zero_add, Fintype.card_fin] at h
  convert! h using 1
  ring

end Zeta5.Arithmetic
