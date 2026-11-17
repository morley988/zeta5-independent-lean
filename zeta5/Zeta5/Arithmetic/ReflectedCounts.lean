import Zeta5.Arithmetic.ReflectedClasses

/-! Summed high-node counts and the exact number of maximal classes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Finset

theorem sum_Icc_indicator_le (a s : ℕ) :
    (∑ c ∈ Icc 1 a, if c ≤ s then (1 : ℕ) else 0) = min a s := by
  have he : (Icc 1 a).filter (fun c => c ≤ s) = Icc 1 (min a s) := by
    ext c
    simp only [mem_filter, mem_Icc, le_min_iff]
    tauto
  rw [← sum_filter, he]
  simp

theorem sum_Icc_indicator_reflected (a s p : ℕ) (ha : a < p) (hs : s < p) :
    (∑ c ∈ Icc 1 a, if p - c ≤ s then (1 : ℕ) else 0) = a + s + 1 - p := by
  have he : (Icc 1 a).filter (fun c => p - c ≤ s) = Icc (p - s) a := by
    ext c
    simp only [mem_filter, mem_Icc]
    omega
  rw [← sum_filter, he]
  simp only [sum_const, smul_eq_mul, mul_one, Nat.card_Icc]
  omega

theorem sum_reflectedSize (N p a : ℕ) (hp : 0 < p) (ha : a < p) :
    (∑ c ∈ Icc 1 a, reflectedSize N p c) =
      2 * (N / p) * a + min a (N % p) + (a + N % p + 1 - p) := by
  simp only [reflectedSize, sum_add_distrib, sum_const, smul_eq_mul, Nat.card_Icc]
  rw [sum_Icc_indicator_le, sum_Icc_indicator_reflected a (N % p) p ha (Nat.mod_lt N hp)]
  simp only [Nat.add_sub_cancel]
  ring_nf

theorem sum_highReflectedNodes (N p a : ℕ) (hpN : p ≤ N) (ha : 2 * a < p) :
    (∑ c ∈ Icc 1 a, (highReflectedNodes N p c).card) =
      2 * (N / p - 1) * a + min a (N % p) + (a + N % p + 1 - p) := by
  have hp : 0 < p := by omega
  have hq : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
  have hh : (∑ c ∈ Icc 1 a, ((highReflectedNodes N p c).card + 2)) =
      ∑ c ∈ Icc 1 a, reflectedSize N p c := by
    apply sum_congr rfl
    intro c hc
    have hc' := mem_Icc.mp hc
    exact highReflectedNodes_card_add_two N p c (by omega) (by omega) hpN
  rw [sum_add_distrib, sum_const, Nat.card_Icc] at hh
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hh
  rw [sum_reflectedSize N p a hp (by omega)] at hh
  have hqm : N / p - 1 + 1 = N / p := by omega
  nlinarith

theorem total_highReflectedNodes (N p : ℕ) (hpN : p ≤ N) (hodd : p % 2 = 1) :
    (∑ c ∈ Icc 1 ((p - 1) / 2), (highReflectedNodes N p c).card) =
      N - p - (N / p - 1) := by
  have hp : 0 < p := by omega
  have ha : 2 * ((p - 1) / 2) < p := by omega
  rw [sum_highReflectedNodes N p ((p - 1) / 2) hpN ha]
  have hs : N % p < p := Nat.mod_lt N hp
  have hq : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hpN)
  have hN := Nat.mod_add_div N p
  have hh : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hind : min ((p - 1) / 2) (N % p) +
      ((p - 1) / 2 + N % p + 1 - p) = N % p := by omega
  rw [add_assoc, hind]
  have hqm : N / p - 1 + 1 = N / p := by omega
  have hpoly : 2 * (N / p - 1) * ((p - 1) / 2) + N % p + p + (N / p - 1) = N := by
    nlinarith
  omega

theorem affected_highReflectedNodes (N p m : ℕ) (hm : 0 < m)
    (hpN : p ≤ N) (hmp : 2 * m < p) :
    (∑ c ∈ Icc 1 (m - 1), (highReflectedNodes N p c).card) =
      2 * (N / p - 1) * (m - 1) + min (m - 1) (N % p) + (m + N % p - p) := by
  have h := sum_highReflectedNodes N p (m - 1) hpN (by omega)
  convert h using 1 <;> omega

def maximalReflectedClasses (N p : ℕ) : Finset ℕ :=
  (Icc 1 ((p - 1) / 2)).filter
    (fun c => reflectedSize N p c = 2 * (N / p) + 1 + (2 * (N % p)) / p)

theorem reflected_epsilon (N p : ℕ) (hp : 0 < p) :
    (2 * (N % p)) / p = if 2 * (N % p) < p then 0 else 1 := by
  have hs := Nat.mod_lt N hp
  split_ifs with h
  · exact Nat.div_eq_of_lt h
  · apply Nat.div_eq_of_lt_le <;> omega

theorem maximalReflectedClasses_card (N p : ℕ) (hodd : p % 2 = 1) :
    (maximalReflectedClasses N p).card =
      if 2 * (N % p) < p then N % p else N % p - (p - 1) / 2 := by
  have hp : 0 < p := by omega
  have hs := Nat.mod_lt N hp
  have he := reflected_epsilon N p hp
  by_cases hsmall : 2 * (N % p) < p
  · have hset : maximalReflectedClasses N p = Icc 1 (N % p) := by
      ext c
      simp only [maximalReflectedClasses, mem_filter, mem_Icc, reflectedSize,
        he, if_pos hsmall]
      split_ifs <;> omega
    rw [hset, Nat.card_Icc, if_pos hsmall]
    omega
  · have hset : maximalReflectedClasses N p = Icc (p - N % p) ((p - 1) / 2) := by
      ext c
      simp only [maximalReflectedClasses, mem_filter, mem_Icc, reflectedSize,
        he, if_neg hsmall]
      split_ifs <;> omega
    rw [hset, Nat.card_Icc, if_neg hsmall]
    omega

theorem reflectedSize_le_max (N p c : ℕ) (hodd : p % 2 = 1)
    (hc : 1 ≤ c) (hcp : c ≤ (p - 1) / 2) :
    reflectedSize N p c ≤ 2 * (N / p) + 1 + (2 * (N % p)) / p := by
  have hp : 0 < p := by omega
  have hs := Nat.mod_lt N hp
  rw [reflected_epsilon N p hp]
  unfold reflectedSize
  split_ifs <;> omega

#print axioms total_highReflectedNodes
#print axioms affected_highReflectedNodes
#print axioms maximalReflectedClasses_card
#print axioms reflectedSize_le_max

end Zeta5.Arithmetic
