import Zeta5.Arithmetic.SharedAllocation

/-! Integral matrix terms may be added without altering the quotient's
two minor bounds. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Allocation
variable {p : ℕ} [Fact p.Prime]

theorem integral_matrix_minorLower {r : ℕ} (A : Matrix (Fin r) (Fin r) ℚ[X])
    (hA : ∀ i j, PolynomialPadicLower p 0 (A i j)) :
    MinorLower (p := p) A (fun _ => 0) := by
  intro a rows cols
  have h := polynomialPadicLower_det_weighted (p := p) (A.submatrix rows cols)
    (fun _ => 0) (fun _ => 0) 0 (fun i j => hA (rows i) (cols j))
  simpa using h

theorem minorLower_add_integral {r t : ℕ} (Q I : Matrix (Fin r) (Fin r) ℚ[X])
    (hQ : MinorLower (p := p) Q (fun a => -(min a t : ℤ)))
    (hI : ∀ i j, PolynomialPadicLower p 0 (I i j)) :
    MinorLower (p := p) (Q + I) (fun a => -(min a t : ℤ)) := by
  intro a rows cols
  let Q' := Q.submatrix rows cols
  let I' := I.submatrix rows cols
  have hI' : MinorLower (p := p) I' (fun _ => 0) :=
    integral_matrix_minorLower I' (fun i j => hI (rows i) (cols j))
  have hQ' : MinorLower (p := p) Q' (fun b => -(min b t : ℤ)) := by
    intro b rs cs
    exact hQ b (rows ∘ rs) (cols ∘ cs)
  let B : Fin 2 → Matrix (Fin a) (Fin a) ℚ[X] := ![Q', I']
  have hzero := sum_matrix_dual_lower (p := p) B 0 ![(t : ℤ), 0] (by
    intro i
    fin_cases i
    · intro b rs cs
      exact (hQ' b rs cs).mono (by
        change (0 : ℤ) * b - (t : ℤ) ≤ -min (b : ℤ) t
        simpa using neg_le_neg (min_le_right (b : ℤ) t))
    · simpa [B] using hI')
  have hone := sum_matrix_dual_lower (p := p) B (-1) ![(0 : ℤ), 0] (by
    intro i
    fin_cases i
    · intro b rs cs
      exact (hQ' b rs cs).mono (by
        change (-1 : ℤ) * b - 0 ≤ -min (b : ℤ) t
        simpa using neg_le_neg (min_le_left (b : ℤ) t))
    · intro b rs cs
      exact (hI' b rs cs).mono (by change (-1 : ℤ) * b - 0 ≤ 0; omega))
  simp only [Fin.sum_univ_two, B, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, zero_add, add_zero, sub_zero, neg_one_mul, zero_sub] at hzero hone
  change PolynomialPadicLower p (-min (a : ℤ) t) (Q' + I').det
  by_cases hat : a ≤ t
  · rw [min_eq_left (by exact_mod_cast hat : (a : ℤ) ≤ t)]
    exact hone
  · rw [min_eq_right (by exact_mod_cast (by omega : t ≤ a) : (t : ℤ) ≤ a)]
    exact hzero

#print axioms minorLower_add_integral

end Zeta5.Arithmetic
