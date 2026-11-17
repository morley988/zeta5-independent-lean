import Zeta5.Arithmetic.FinsetAtomicMinors
import Zeta5.Arithmetic.ReflectedWeights

/-! Sharp all-minor estimates for the actual reflected residue matrices. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Allocation
variable {p : ℕ} [Fact p.Prime]

def monomialReflectedClass (N m r p c : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  finsetAtomicMatrix (reflectedNodes N p c) (monomialAtomWeight N m) pole r

theorem monomialReflectedClass_eq_sum (N m r p c : ℕ) :
    monomialReflectedClass N m r p c =
      ∑ i ∈ reflectedNodes N p c, monomialAtom N m r i := by
  funext k l
  simp only [monomialReflectedClass, finsetAtomicMatrix, monomialAtom, Matrix.sum_apply]

theorem pole_padicIntegral (c : ℕ) : PadicLower p 0 (pole c) := by
  convert padicLower_int (p := p) (-((c : ℤ) ^ 2)) using 1 <;> simp [pole]

theorem reflected_class_minorLower (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun k => -clusterCost (highReflectedNodes N p c).card k) := by
  have h := finset_atomic_minorLower (reflectedNodes N p c)
    (highReflectedNodes N p c) (Finset.filter_subset _ _)
    (monomialAtomWeight N m) pole r (pole c) (-(highReflectedNodes N p c).card - 1)
    (pole_padicIntegral c) (fun i hi => reflected_pole_congr hc hcp hi) (by
      intro i hi
      have hiN := (mem_reflectedNodes.mp hi).2.1
      simpa only [highReflectedNodes, Finset.mem_filter, hi, true_and] using
        reflected_atomWeight_bound N m c i hp hc hcp hpN hi (by omega))
  intro k rows cols
  convert h k rows cols using 1 <;> first | rfl | (unfold clusterCost; ring)

theorem affected_reflected_class_minorLower (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hcm : c < m)
    (hpN : p ≤ N) (hsmall : 2 * N < p ^ 2) :
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun k => -affectedClusterCost (highReflectedNodes N p c).card k) := by
  have h := finset_atomic_minorLower (reflectedNodes N p c)
    (highReflectedNodes N p c) (Finset.filter_subset _ _)
    (monomialAtomWeight N m) pole r (pole c) (1 - (highReflectedNodes N p c).card)
    (pole_padicIntegral c) (fun i hi => reflected_pole_congr hc hcp hi) (by
      intro i hi
      have hiN := (mem_reflectedNodes.mp hi).2.1
      simpa only [highReflectedNodes, Finset.mem_filter, hi, true_and] using
        affected_reflected_atomWeight_bound N m c i hp hc hcp hcm hpN hi (by omega))
  intro k rows cols
  convert h k rows cols using 1 <;> first | rfl | (unfold affectedClusterCost; ring)

theorem reflected_class_zero_price (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 3 * p)
    (hsmall : 2 * N < p ^ 2) (hhigh : 1 ≤ (highReflectedNodes N p c).card) :
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun _ => -7 * (highReflectedNodes N p c).card) := by
  intro k rows cols
  apply (reflected_class_minorLower N m r c hp hc hcp hpN hsmall k rows cols).mono
  have h := clusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hhigh
    (highReflectedNodes_card_le_four N p c hc hcp hpN hN)
  have hd := Int.natCast_nonneg ((highReflectedNodes N p c).card - k)
  linarith

theorem reflected_class_minus_one_price (N m r c : ℕ) (hp : 5 < p)
    (hc : 0 < c) (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 3 * p)
    (hsmall : 2 * N < p ^ 2) (hhigh : 1 ≤ (highReflectedNodes N p c).card) :
    MinorLower (p := p) (monomialReflectedClass N m r p c)
      (fun k => -(k : ℤ) - 6 * (highReflectedNodes N p c).card) := by
  intro k rows cols
  apply (reflected_class_minorLower N m r c hp hc hcp hpN hsmall k rows cols).mono
  have h := clusterCost_le_with_deficit_all (highReflectedNodes N p c).card k hhigh
    (highReflectedNodes_card_le_four N p c hc hcp hpN hN)
  have hd : ((highReflectedNodes N p c).card : ℤ) - k ≤
      ((highReflectedNodes N p c).card - k : ℕ) := by omega
  linarith

#print axioms reflected_class_minorLower
#print axioms affected_reflected_class_minorLower
#print axioms reflected_class_minus_one_price

end Zeta5.Arithmetic
