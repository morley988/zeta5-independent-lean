import Zeta5.Reuse.AllocationBlocks
import Zeta5.Arithmetic.QuotientMinors
import Zeta5.Arithmetic.ClusterCosts

/-! Two affine minor bounds give the shared-dimension bound exactly.
This is the algebraic assembly of the quotient and residue-class bounds;
the actual residue-class estimates are proved separately. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Allocation
variable {p : ℕ} [Fact p.Prime]

theorem quotient_minor_zero_price (N m R : ℕ) (hp : 5 < p) (hmR : m ≤ R) :
    MinorLower (p := p) (quotientPencil N m (R - m))
      (fun _ => -(terminalSize N m R p : ℤ)) := by
  intro a rows cols
  exact (quotientPencil_minor_padicLower N m R a hp hmR rows cols).mono (by
    exact neg_le_neg (by exact_mod_cast min_le_right a (terminalSize N m R p)))

theorem quotient_minor_minus_one_price (N m R : ℕ) (hp : 5 < p) (hmR : m ≤ R) :
    MinorLower (p := p) (quotientPencil N m (R - m)) (fun a => -(a : ℤ)) := by
  intro a rows cols
  exact (quotientPencil_minor_padicLower N m R a hp hmR rows cols).mono (by
    exact neg_le_neg (by exact_mod_cast min_le_left a (terminalSize N m R p)))

theorem shared_dimension_matrix_bound {d r : ℕ}
    (Q : Matrix (Fin r) (Fin r) ℚ[X])
    (A : Fin d → Matrix (Fin r) (Fin r) ℚ[X])
    (pen : Fin d → ℤ) (high : Fin d → ℕ) (t : ℕ)
    (hhigh : ∑ i, high i ≤ r)
    (hQ : MinorLower (p := p) Q (fun a => -(min a t : ℤ)))
    (hA0 : ∀ i, MinorLower (p := p) (A i) (fun _ => -(pen i)))
    (hA1 : ∀ i, MinorLower (p := p) (A i) (fun a => -(a : ℤ) - (pen i - high i))) :
    PolynomialPadicLower p
      (-(∑ i, pen i) - (min t (r - ∑ i, high i) : ℕ)) (Q + ∑ i, A i).det := by
  let B : Fin (d + 1) → Matrix (Fin r) (Fin r) ℚ[X] := Fin.cases Q A
  have hsum : (∑ i, B i) = Q + ∑ i, A i := by simp [B, Fin.sum_univ_succ]
  have hzero := sum_matrix_dual_lower (p := p) B 0 (Fin.cases (t : ℤ) pen) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a rows cols
      simpa [B] using (hQ a rows cols).mono
        (neg_le_neg (by exact_mod_cast min_le_right a t))
    · simpa [B] using hA0 j)
  have hone := sum_matrix_dual_lower (p := p) B (-1)
      (Fin.cases (0 : ℤ) (fun i => pen i - high i)) (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a rows cols
      simpa [B] using (hQ a rows cols).mono
        (neg_le_neg (by exact_mod_cast min_le_left a t))
    · simpa [B] using hA1 j)
  rw [hsum] at hzero hone
  simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    zero_mul, zero_sub, neg_one_mul, zero_add, Finset.sum_sub_distrib] at hzero hone
  by_cases ht : t ≤ r - ∑ i, high i
  · rw [min_eq_left ht]
    convert hzero using 1 <;> ring
  · rw [min_eq_right (le_of_lt (lt_of_not_ge ht))]
    convert hone using 1
    rw [Nat.cast_sub hhigh, Nat.cast_sum]
    ring

#print axioms shared_dimension_matrix_bound

end Zeta5.Arithmetic
