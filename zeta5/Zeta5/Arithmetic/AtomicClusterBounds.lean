import Zeta5.Arithmetic.AtomicMinors
import Zeta5.Arithmetic.ClusterCosts

/-! From actual atomic matrices and weight valuations to the cluster
cost and its two affine envelopes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Allocation
variable {p : ℕ} [Fact p.Prime]

theorem ordinary_atomic_cluster {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (-(high.card : ℤ) - 1 - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r) (fun k => -clusterCost high.card k) := by
  have h := atomic_minorLower r w x c high (-(high.card : ℤ) - 1) hc hx hw
  intro k rows cols
  convert h k rows cols using 1
  unfold clusterCost
  ring

theorem affected_atomic_cluster {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (1 - (high.card : ℤ) - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r)
      (fun k => -affectedClusterCost high.card k) := by
  have h := atomic_minorLower r w x c high (1 - (high.card : ℤ)) hc hx hw
  intro k rows cols
  convert h k rows cols using 1
  unfold affectedClusterCost
  ring

theorem ordinary_atomic_zero_price {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hh : 1 ≤ high.card) (hh4 : high.card ≤ 4)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (-(high.card : ℤ) - 1 - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r) (fun _ => -7 * (high.card : ℤ)) := by
  intro k rows cols
  have h := ordinary_atomic_cluster r w x c high hc hx hw k rows cols
  apply h.mono
  have he := clusterCost_le_with_deficit_all high.card k hh hh4
  have hd := Int.natCast_nonneg (high.card - k)
  linarith

theorem ordinary_atomic_minus_one_price {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hh : 1 ≤ high.card) (hh4 : high.card ≤ 4)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (-(high.card : ℤ) - 1 - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r) (fun k => -(k : ℤ) - 6 * high.card) := by
  intro k rows cols
  have h := ordinary_atomic_cluster r w x c high hc hx hw k rows cols
  apply h.mono
  have he := clusterCost_le_with_deficit_all high.card k hh hh4
  have hd : (high.card : ℤ) - k ≤ (high.card - k : ℕ) := by omega
  linarith

theorem affected_atomic_zero_price {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hh : 1 ≤ high.card) (hh4 : high.card ≤ 4)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (1 - (high.card : ℤ) - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r) (fun _ => -5 * (high.card : ℤ)) := by
  intro k rows cols
  have h := affected_atomic_cluster r w x c high hc hx hw k rows cols
  apply h.mono
  have he := affectedClusterCost_le_with_deficit_all high.card k hh hh4
  have hd := Int.natCast_nonneg (high.card - k)
  linarith

theorem affected_atomic_minus_one_price {d : ℕ} (r : ℕ)
    (w : Fin d → ℚ[X]) (x : Fin d → ℚ) (c : ℚ) (high : Finset (Fin d))
    (hh : 1 ≤ high.card) (hh4 : high.card ≤ 4)
    (hc : PadicLower p 0 c) (hx : ∀ i, PadicLower p 1 (x i - c))
    (hw : ∀ i, PolynomialPadicLower p
      (1 - (high.card : ℤ) - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (atomicMatrix w x r) (fun k => -(k : ℤ) - 4 * high.card) := by
  intro k rows cols
  have h := affected_atomic_cluster r w x c high hc hx hw k rows cols
  apply h.mono
  have he := affectedClusterCost_le_with_deficit_all high.card k hh hh4
  have hd : (high.card : ℤ) - k ≤ (high.card - k : ℕ) := by omega
  linarith

#print axioms ordinary_atomic_minus_one_price
#print axioms affected_atomic_zero_price

end Zeta5.Arithmetic
