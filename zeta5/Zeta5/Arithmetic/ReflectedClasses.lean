import Zeta5.Arithmetic.ResidueValuations
import Mathlib.Data.Int.CardIntervalMod

/-! Exact Euclidean-division identities for reflected residue classes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction

theorem int_reflected_floor_sum (N i p : ℤ) (hp : 0 < p) :
    (N - i) / p + (N + i) / p =
      2 * (N / p) - 1 + (if i % p ≤ N % p then 1 else 0) +
        (if p - i % p ≤ N % p then 1 else 0) := by
  have hs0 := Int.emod_nonneg N (ne_of_gt hp)
  have hs1 := Int.emod_lt_of_pos N hp
  have hb0 := Int.emod_nonneg i (ne_of_gt hp)
  have hb1 := Int.emod_lt_of_pos i hp
  have hminus : (N % p - i % p) / p =
      (if i % p ≤ N % p then 0 else -1) := by
    split_ifs with h
    · apply (Int.ediv_eq_iff_of_pos hp).mpr
      constructor <;> omega
    · apply (Int.ediv_eq_iff_of_pos hp).mpr
      constructor <;> omega
  have hplus : (N % p + i % p) / p =
      (if p - i % p ≤ N % p then 1 else 0) := by
    split_ifs with h
    · apply (Int.ediv_eq_iff_of_pos hp).mpr
      constructor <;> omega
    · apply (Int.ediv_eq_iff_of_pos hp).mpr
      constructor <;> omega
  have hm : N - i = N % p - i % p + (N / p - i / p) * p := by
    have hN := Int.emod_add_ediv_mul N p
    have hi := Int.emod_add_ediv_mul i p
    nlinarith
  have ha : N + i = N % p + i % p + (N / p + i / p) * p := by
    have hN := Int.emod_add_ediv_mul N p
    have hi := Int.emod_add_ediv_mul i p
    nlinarith
  rw [hm, ha, Int.add_mul_ediv_right _ _ (ne_of_gt hp),
    Int.add_mul_ediv_right _ _ (ne_of_gt hp), hminus, hplus]
  split_ifs <;> omega

def reflectedSize (N p c : ℕ) : ℕ :=
  2 * (N / p) + (if c ≤ N % p then 1 else 0) +
    (if p - c ≤ N % p then 1 else 0)

theorem reflected_floor_sum (N i p : ℕ) (hp : 0 < p) (hiN : i ≤ N) :
    ((N - i) / p : ℕ) + ((N + i) / p : ℕ) =
      (reflectedSize N p (i % p) : ℤ) - 1 := by
  have h := int_reflected_floor_sum (N : ℤ) i p (by exact_mod_cast hp)
  rw [← Nat.cast_sub hiN, ← Nat.cast_add, ← Int.natCast_ediv, ← Int.natCast_ediv,
    ← Int.natCast_ediv, ← Int.natCast_emod, ← Int.natCast_emod] at h
  have hb := Nat.mod_lt i hp
  rw [← Nat.cast_sub (by omega : i % p ≤ p)] at h
  simp only [Int.ofNat_le] at h
  simp only [reflectedSize, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  linarith

def residueNodes (N p c : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter (fun i => i % p = c)

theorem residueNodes_card (N p c : ℕ) (hc : 0 < c) (hcp : c < p) :
    (residueNodes N p c).card = N / p + (if c ≤ N % p then 1 else 0) := by
  have hp : 0 < p := lt_trans hc hcp
  have he : residueNodes N p c =
      (Finset.range (N + 1)).filter (fun i => Nat.ModEq p i c) := by
    ext i
    simp only [residueNodes, Finset.mem_filter, Finset.mem_Ioc,
      Finset.mem_range, Nat.ModEq, Nat.mod_eq_of_lt hcp]
    by_cases hi : i = 0
    · simp [hi, ne_of_lt hc]
    · omega
  rw [he, ← Nat.count_eq_card_filter_range, Nat.count_succ,
    Nat.count_modEq_card _ hp, Nat.mod_eq_of_lt hcp]
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hcp]
  split_ifs <;> omega

def reflectedNodes (N p c : ℕ) : Finset ℕ :=
  residueNodes N p c ∪ residueNodes N p (p - c)

theorem reflectedNodes_card (N p c : ℕ) (hc : 0 < c) (hcp : 2 * c < p) :
    (reflectedNodes N p c).card = reflectedSize N p c := by
  have hc1 : c < p := by omega
  have hc2 : 0 < p - c := by omega
  have hc3 : p - c < p := by omega
  have hd : Disjoint (residueNodes N p c) (residueNodes N p (p - c)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    omega
  rw [reflectedNodes, Finset.card_union_of_disjoint hd,
    residueNodes_card _ _ _ hc hc1, residueNodes_card _ _ _ hc2 hc3]
  unfold reflectedSize
  omega

theorem mem_reflectedNodes {N p c i : ℕ} :
    i ∈ reflectedNodes N p c ↔
      0 < i ∧ i ≤ N ∧ (i % p = c ∨ i % p = p - c) := by
  simp only [reflectedNodes, residueNodes, Finset.mem_union,
    Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem reflectedSize_symm (N p c : ℕ) (hcp : c ≤ p) :
    reflectedSize N p (p - c) = reflectedSize N p c := by
  simp only [reflectedSize, Nat.sub_sub_self hcp]
  omega

def highReflectedNodes (N p c : ℕ) : Finset ℕ :=
  (reflectedNodes N p c).filter (fun i => p < i)

theorem reflected_low_nodes (N p c : ℕ) (hc : 0 < c) (hcp : 2 * c < p)
    (hpN : p ≤ N) :
    (reflectedNodes N p c).filter (fun i => i ≤ p) = {c, p - c} := by
  have hc1 : c < p := by omega
  have hc2 : p - c < p := by omega
  ext i
  simp only [Finset.mem_filter, mem_reflectedNodes, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hi0, hiN, hi⟩, hip⟩
    have hne : i ≠ p := by
      intro h
      subst i
      simp only [Nat.mod_self] at hi
      omega
    have hl : i < p := by omega
    simpa only [Nat.mod_eq_of_lt hl] using hi
  · rintro (rfl | rfl)
    · exact ⟨⟨hc, hc1.le.trans hpN, Or.inl (Nat.mod_eq_of_lt hc1)⟩, hc1.le⟩
    · exact ⟨⟨by omega, hc2.le.trans hpN, Or.inr (Nat.mod_eq_of_lt hc2)⟩, hc2.le⟩

theorem highReflectedNodes_card_add_two (N p c : ℕ) (hc : 0 < c)
    (hcp : 2 * c < p) (hpN : p ≤ N) :
    (highReflectedNodes N p c).card + 2 = reflectedSize N p c := by
  have h := Finset.card_filter_add_card_filter_not
    (s := reflectedNodes N p c) (p := fun i => p < i)
  have hl : (reflectedNodes N p c).filter (fun i => ¬p < i) = {c, p - c} := by
    simpa only [not_lt] using reflected_low_nodes N p c hc hcp hpN
  rw [hl, Finset.card_pair (by omega : c ≠ p - c), reflectedNodes_card N p c hc hcp] at h
  exact h

theorem highReflectedNodes_card_le_four (N p c : ℕ) (hc : 0 < c)
    (hcp : 2 * c < p) (hpN : p ≤ N) (hN : N < 3 * p) :
    (highReflectedNodes N p c).card ≤ 4 := by
  have hp : 0 < p := by omega
  have hq : N / p < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hh := highReflectedNodes_card_add_two N p c hc hcp hpN
  unfold reflectedSize at hh
  split_ifs at hh <;> omega

theorem reflected_node_not_dvd {N p c i : ℕ} (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) : ¬p ∣ i := by
  have hi' := (mem_reflectedNodes.mp hi).2.2
  intro h
  have hm := Nat.mod_eq_zero_of_dvd h
  rw [hm] at hi'
  omega

theorem denominator_derivative_reflected_valuation {p : ℕ} [Fact p.Prime]
    (N c i : ℕ) (hp : 2 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : N + i < p ^ 2) :
    padicValRat p ((denominator N).derivative.eval (pole i)) =
      (reflectedSize N p c : ℤ) - 1 := by
  obtain ⟨hi0, hiN, himod⟩ := mem_reflectedNodes.mp hi
  rw [denominator_derivative_valuation N i hp hi0 hiN hsmall,
    padicValNat.eq_zero_of_not_dvd (reflected_node_not_dvd hc hcp hi)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  rw [reflected_floor_sum N i p (by omega) hiN]
  rcases himod with h | h
  · rw [h]
  · rw [h, reflectedSize_symm N p c (by omega)]

#print axioms int_reflected_floor_sum
#print axioms reflected_floor_sum
#print axioms residueNodes_card
#print axioms reflectedNodes_card
#print axioms highReflectedNodes_card_add_two
#print axioms denominator_derivative_reflected_valuation

end Zeta5.Arithmetic
