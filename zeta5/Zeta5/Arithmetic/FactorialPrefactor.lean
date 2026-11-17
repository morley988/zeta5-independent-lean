import Zeta5.Arithmetic.UpperBandAssembly

/-! The exact signed factorial charge from the rational change of basis. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

def factorialPrefactor (N m r : ℕ) : ℚ :=
  (Nat.factorial N : ℚ) ^ (2 * r) *
    ∏ k : Fin r, ((Nat.factorial (2 * (m + k.val)) : ℚ)⁻¹) ^ 2

def factorialCharge (N m r p : ℕ) : ℤ :=
  2 * (∑ k : Fin r, (((2 * (m + k.val)) / p : ℕ) : ℤ)) -
    2 * r * ((N / p : ℕ) : ℤ)

theorem factorialPrefactor_padicLower (N m r : ℕ)
    (hN : N < p ^ 2) (hR : ∀ k : Fin r, 2 * (m + k.val) < p ^ 2) :
    PadicLower p (-factorialCharge N m r p) (factorialPrefactor N m r) := by
  have htop : PadicLower p (2 * (r : ℤ) * ((N / p : ℕ) : ℤ))
      ((Nat.factorial N : ℚ) ^ (2 * r)) := by
    right
    rw [padicValRat.pow, padicValRat.of_nat, factorial_padicVal_of_lt_sq hN]
    push_cast
    rfl
  have hbot := padicLower_prod (p := p) Finset.univ
    (fun k : Fin r => ((Nat.factorial (2 * (m + k.val)) : ℚ)⁻¹) ^ 2)
    (fun k => -2 * (((2 * (m + k.val)) / p : ℕ) : ℤ)) (by
      intro k hk
      right
      rw [padicValRat.pow, padicValRat.inv, padicValRat.of_nat,
        factorial_padicVal_of_lt_sq (hR k)]
      norm_num)
  have h := htop.mul hbot
  convert h using 1 <;> first | rfl | (simp only [factorialCharge, ← Finset.mul_sum]; ring)

theorem windowMatrix_det_padicLower (N m r : ℕ) (w : ℤ)
    (hN : N < p ^ 2) (hR : ∀ k : Fin r, 2 * (m + k.val) < p ^ 2)
    (hM : PolynomialPadicLower p w (monomialPencil N m r).det) :
    PolynomialPadicLower p (-factorialCharge N m r p + w)
      (Matrix.det (fun i j : Fin r => entry N (m + i.val) (m + j.val))) := by
  rw [windowDeterminant_change_of_basis]
  exact (PolynomialPadicLower.constant (factorialPrefactor_padicLower N m r hN hR)).mul hM

theorem windowDeterminant_padicLower_of_monomial (n : ℕ) (w : ℤ)
    (hlarge : 50 * n < p ^ 2)
    (hM : PolynomialPadicLower p w (monomialPencil (20 * n) n (24 * n)).det) :
    PolynomialPadicLower p (-factorialCharge (20 * n) n (24 * n) p + w)
      (windowDeterminant n) := by
  exact windowMatrix_det_padicLower (20 * n) n (24 * n) w (by omega)
    (fun k => by have hk := k.isLt; omega) hM

theorem windowDeterminant_upperBand_bound (n : ℕ) (hn : 0 < n) (hp : 5 < p)
    (hmp : 2 * n < p) (hpN : p ≤ 20 * n) (hN : 20 * n < 3 * p)
    (hlarge : 50 * n < p ^ 2) :
    PolynomialPadicLower p
      (-factorialCharge (20 * n) n (24 * n) p - 7 * (upperHighCount (20 * n) p : ℤ) +
        2 * (upperAffectedCount (20 * n) n p : ℤ) -
        (min (terminalSize (20 * n) n (25 * n) p)
          (24 * n - upperHighCount (20 * n) p) : ℕ)) (windowDeterminant n) := by
  have hHr : upperHighCount (20 * n) p ≤ 25 * n - n := by
    unfold upperHighCount
    omega
  have h := monomialPencil_upperBand_bound (20 * n) n (25 * n) hp hn (by omega)
    hmp hpN hN (by omega) hHr
  have hr : 25 * n - n = 24 * n := by omega
  rw [hr] at h
  have hf := windowDeterminant_padicLower_of_monomial n _ hlarge h
  convert hf using 1 <;> ring

#print axioms factorialPrefactor_padicLower
#print axioms windowDeterminant_upperBand_bound

end Zeta5.Arithmetic
