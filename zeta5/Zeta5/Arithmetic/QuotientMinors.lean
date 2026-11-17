import Zeta5.Arithmetic.QuotientSupport
import Zeta5.Reuse.PolynomialValuations
import Mathlib.Order.Interval.Finset.Nat

/-! The actual quotient matrix has the claimed bound on every minor,
including arbitrary repeated row and column selections. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem polynomialDet_terminal_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ[X]) (bad : Finset ι)
    (hweak : ∀ i j, PolynomialPadicLower p (-1) (A i j))
    (hstrong : ∀ i j, j ∉ bad → PolynomialPadicLower p 0 (A i j)) :
    PolynomialPadicLower p (-(bad.card : ℤ)) A.det := by
  have h := polynomialPadicLower_det_weighted A (fun _ => 0)
    (fun j => if j ∈ bad then -1 else 0) 0 (by
      intro i j
      by_cases hj : j ∈ bad
      · simpa [hj] using hweak i j
      · simpa [hj] using hstrong i j hj)
  simpa using h

theorem selected_terminal_card_le {a r t : ℕ} (cols : Fin a → Fin r)
    (hc : Function.Injective cols) :
    (Finset.univ.filter (fun j => r - t ≤ (cols j).val)).card ≤ min a t := by
  apply le_min
  · exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin a)
  · have h := Finset.card_le_card_of_injOn (fun j : Fin a => (cols j).val)
      (s := Finset.univ.filter (fun j => r - t ≤ (cols j).val))
      (t := Finset.Ico (r - t) r) (by
        intro j hj
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2, (cols j).isLt⟩) (by
        intro i hi j hj hij
        exact hc (Fin.ext hij))
    rw [Nat.card_Ico] at h
    omega

def quotientPencil (N m r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => C (quotientMoment N m i.val j.val)

theorem quotientPencil_minor_padicLower (N m R a : ℕ) (hp : 5 < p) (hmR : m ≤ R)
    (rows cols : Fin a → Fin (R - m)) :
    PolynomialPadicLower p (-(min a (terminalSize N m R p) : ℕ))
      ((quotientPencil N m (R - m)).submatrix rows cols).det := by
  classical
  by_cases hc : Function.Injective cols
  · let bad : Finset (Fin a) := Finset.univ.filter
      (fun j => (R - m) - terminalSize N m R p ≤ (cols j).val)
    have hb := polynomialDet_terminal_columns
      ((quotientPencil N m (R - m)).submatrix rows cols) bad
      (fun i j => PolynomialPadicLower.constant
        (quotientMoment_padicLower N m (rows i).val (cols j).val hp)) (by
          intro i j hj
          apply PolynomialPadicLower.constant
          apply quotientMoment_integral_outside_terminalSize N m R _ _ hp hmR
            (rows i).isLt (cols j).isLt
          right
          have hn : ¬ (R - m) - terminalSize N m R p ≤ (cols j).val := by
            simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hj
          omega)
    have hcard : bad.card ≤ min a (terminalSize N m R p) :=
      selected_terminal_card_le cols hc
    have hcast : (bad.card : ℤ) ≤ (min a (terminalSize N m R p) : ℕ) := by
      exact_mod_cast hcard
    exact hb.mono (neg_le_neg hcast)
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])]
    exact PolynomialPadicLower.zero _

#print axioms quotientPencil_minor_padicLower

end Zeta5.Arithmetic
