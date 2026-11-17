import Zeta5.Arithmetic.ReflectedClasses
import Zeta5.Arithmetic.AtomicClusterBounds

/-! Actual residue weights in each reflected class satisfy the sharp
ordinary and common-root valuation bounds used by the minor estimates. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction
variable {p : ℕ} [Fact p.Prime]

theorem reflected_square_congr {N c i : ℕ} (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) :
    (p : ℤ) ∣ (c : ℤ) ^ 2 - (i : ℤ) ^ 2 := by
  have hdiv := Nat.mod_add_div i p
  obtain hi0 | hi1 := (mem_reflectedNodes.mp hi).2.2
  · rw [hi0] at hdiv
    have he : (i : ℤ) = c + (p : ℤ) * (i / p : ℕ) := by exact_mod_cast hdiv.symm
    refine ⟨-(2 * (c : ℤ) * (i / p : ℕ) + (p : ℤ) * (i / p : ℕ) ^ 2), ?_⟩
    rw [he]
    ring
  · rw [hi1] at hdiv
    have he : (i : ℤ) = (p : ℤ) * ((i / p : ℕ) + 1) - c := by
      have hh : ((p - c : ℕ) : ℤ) + (p : ℤ) * (i / p : ℕ) = i := by exact_mod_cast hdiv
      rw [Nat.cast_sub (by omega : c ≤ p)] at hh
      linarith
    refine ⟨2 * (c : ℤ) * ((i / p : ℕ) + 1) -
      (p : ℤ) * ((i / p : ℕ) + 1) ^ 2, ?_⟩
    rw [he]
    ring

theorem reflected_pole_congr {N c i : ℕ} (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) : PadicLower p 1 (pole i - pole c) := by
  have h := padicLower_int_of_dvd (p := p) _ (reflected_square_congr hc hcp hi)
  convert h using 1 <;> simp [pole] <;> ring

theorem reflected_stieltjes_bound {N c i : ℕ} (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : i < p ^ 2) :
    PolynomialPadicLower p (-5 * (if p < i then (1 : ℤ) else 0)) (stieltjes i) := by
  have hi0 := (mem_reflectedNodes.mp hi).1
  have hni := reflected_node_not_dvd hc hcp hi
  by_cases hhigh : p < i
  · simpa [hhigh] using stieltjes_polynomial_padicLower (p := p) i hp hi0 hsmall
  · have hilow : i < p := by
      have hne : i ≠ p := by intro he; subst i; exact hni (dvd_refl p)
      omega
    simpa [hhigh] using stieltjes_polynomial_integral (p := p) i hp hilow

theorem reflected_atomWeight_bound (N m c i : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N)
    (hi : i ∈ reflectedNodes N p c) (hsmall : N + i < p ^ 2) :
    PolynomialPadicLower p
      (-(highReflectedNodes N p c).card - 1 - 5 * (if p < i then (1 : ℤ) else 0))
      (monomialAtomWeight N m i) := by
  have hd := denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi hsmall
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  have hd' : padicValRat p ((denominator N).derivative.eval (pole i)) ≤
      ((highReflectedNodes N p c).card : ℤ) + 1 := by
    rw [hd, ← hh]
    push_cast
    omega
  have hw := monomialAtomWeight_bound N m i 0
    (-5 * (if p < i then (1 : ℤ) else 0))
    ((highReflectedNodes N p c).card + 1)
    (commonFactor_eval_sq_integral m i)
    (reflected_stieltjes_bound hp hc hcp hi (by omega)) hd'
  convert hw using 1 <;> ring

theorem affected_reflected_atomWeight_bound (N m c i : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hcm : c < m) (hpN : p ≤ N)
    (hi : i ∈ reflectedNodes N p c) (hsmall : N + i < p ^ 2) :
    PolynomialPadicLower p
      (1 - (highReflectedNodes N p c).card - 5 * (if p < i then (1 : ℤ) else 0))
      (monomialAtomWeight N m i) := by
  have hd := denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi hsmall
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  have hd' : padicValRat p ((denominator N).derivative.eval (pole i)) ≤
      ((highReflectedNodes N p c).card : ℤ) + 1 := by
    rw [hd, ← hh]
    push_cast
    omega
  have hw := monomialAtomWeight_bound N m i 2
    (-5 * (if p < i then (1 : ℤ) else 0))
    ((highReflectedNodes N p c).card + 1)
    (commonFactor_eval_sq_gain hcm (reflected_square_congr hc hcp hi))
    (reflected_stieltjes_bound hp hc hcp hi (by omega)) hd'
  convert hw using 1 <;> ring

#print axioms reflected_pole_congr
#print axioms reflected_atomWeight_bound
#print axioms affected_reflected_atomWeight_bound

end Zeta5.Arithmetic
