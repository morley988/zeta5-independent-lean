import Zeta5.Arithmetic.LowPairs
import Zeta5.Arithmetic.IntegralMatrices

/-! Two affine all-minor bounds for every actual reflected class,
including all-low classes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Allocation
variable {p : ℕ} [Fact p.Prime]

theorem low_reflected_class_integral (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2)
    (hhigh : (highReflectedNodes N p c).card = 0) :
    ∀ k l : Fin r, PolynomialPadicLower p 0 (monomialReflectedClass N m r p c k l) := by
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  have hcard : (reflectedNodes N p c).card = 2 := by
    rw [reflectedNodes_card N p c hc hcp]
    omega
  have hall : (reflectedNodes N p c).filter (fun i => i ≤ p) = reflectedNodes N p c := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    by_contra h
    have hmem : i ∈ highReflectedNodes N p c := Finset.mem_filter.mpr ⟨hi, by omega⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  have hset : reflectedNodes N p c = {c, p - c} := by
    rw [← hall]
    exact reflected_low_nodes N p c hc hcp hpN
  have hpair := low_reflected_pair_integral N m r c hp hc hcp (by omega) hsmall hcard
  intro k l
  rw [monomialReflectedClass_eq_sum, hset,
    Finset.sum_pair (by omega : c ≠ p - c), Matrix.add_apply]
  exact hpair k l

def reflectedPenalty (N m p c : ℕ) : ℤ :=
  (if c < m then 5 else 7) * (highReflectedNodes N p c).card

theorem reflected_class_dual_bounds (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 3 * p)
    (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun _ => -reflectedPenalty N m p c) ∧
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun k => -(k : ℤ) - (reflectedPenalty N m p c - (highReflectedNodes N p c).card)) := by
  by_cases hz : (highReflectedNodes N p c).card = 0
  · have h := integral_matrix_minorLower (p := p) (monomialReflectedClass N m r p c)
      (low_reflected_class_integral N m r c hp hc hcp hpN hsmall hz)
    constructor
    · simpa [reflectedPenalty, hz] using h
    · intro k rows cols
      exact (h k rows cols).mono (by simp [reflectedPenalty, hz])
  have hpos : 1 ≤ (highReflectedNodes N p c).card := by omega
  have hfour := highReflectedNodes_card_le_four N p c hc hcp hpN hN
  by_cases hcm : c < m
  · have h := affected_reflected_class_minorLower N m r c hp hc hcp hcm hpN hsmall
    constructor
    · intro k rows cols
      apply (h k rows cols).mono
      have he := affectedClusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hpos hfour
      have hd := Int.natCast_nonneg ((highReflectedNodes N p c).card - k)
      simp only [reflectedPenalty, if_pos hcm]
      linarith
    · intro k rows cols
      apply (h k rows cols).mono
      have he := affectedClusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hpos hfour
      have hd : ((highReflectedNodes N p c).card : ℤ) - k ≤
          ((highReflectedNodes N p c).card - k : ℕ) := by omega
      simp only [reflectedPenalty, if_pos hcm]
      linarith
  · constructor
    · simpa [reflectedPenalty, hcm] using
        reflected_class_zero_price N m r c hp hc hcp hpN hN hsmall hpos
    · intro k rows cols
      convert reflected_class_minus_one_price N m r c hp hc hcp hpN hN hsmall hpos k rows cols using 1
      simp only [reflectedPenalty, if_neg hcm]
      ring

#print axioms low_reflected_class_integral
#print axioms reflected_class_dual_bounds

end Zeta5.Arithmetic
