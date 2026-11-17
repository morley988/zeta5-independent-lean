import Zeta5.Arithmetic.ReflectedCounts
import Zeta5.Arithmetic.ReflectedMinors

/-! A genuine partition of the physical nodes into their reflected classes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Finset Polynomial Zeta5.Construction

def reflectedLabel (p i : ℕ) : ℕ := min (i % p) (p - i % p)

theorem reflectedLabel_le_half (p i : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    reflectedLabel p i ≤ (p - 1) / 2 := by
  have hr := Nat.mod_lt i hp
  unfold reflectedLabel
  omega

theorem reflectedLabel_eq_zero (p i : ℕ) (hp : 0 < p) :
    reflectedLabel p i = 0 ↔ p ∣ i := by
  have hr := Nat.mod_lt i hp
  rw [Nat.dvd_iff_mod_eq_zero]
  unfold reflectedLabel
  omega

theorem reflectedLabel_eq_iff (p i c : ℕ) (hp : 0 < p)
    (hc : 0 < c) (hcp : 2 * c < p) :
    reflectedLabel p i = c ↔ i % p = c ∨ i % p = p - c := by
  have hr := Nat.mod_lt i hp
  unfold reflectedLabel
  omega

def zeroClassNodes (N p : ℕ) : Finset ℕ := (Ioc 0 N).filter (fun i => p ∣ i)

theorem reflectedLabel_zero_fiber (N p : ℕ) (hp : 0 < p) :
    (Ioc 0 N).filter (fun i => reflectedLabel p i = 0) = zeroClassNodes N p := by
  ext i
  simp [zeroClassNodes, reflectedLabel_eq_zero p i hp]

theorem reflectedLabel_fiber (N p c : ℕ) (hp : 0 < p)
    (hc : 0 < c) (hcp : 2 * c < p) :
    (Ioc 0 N).filter (fun i => reflectedLabel p i = c) = reflectedNodes N p c := by
  ext i
  simp only [mem_filter, mem_Ioc, reflectedLabel_eq_iff p i c hp hc hcp,
    mem_reflectedNodes]
  tauto

theorem sum_reflected_partition {M : Type*} [AddCommMonoid M]
    (N p : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) (f : ℕ → M) :
    (∑ i ∈ Ioc 0 N, f i) = (∑ i ∈ zeroClassNodes N p, f i) +
      ∑ c ∈ Icc 1 ((p - 1) / 2), ∑ i ∈ reflectedNodes N p c, f i := by
  have hm : ∀ i ∈ Ioc 0 N, reflectedLabel p i ∈ Icc 0 ((p - 1) / 2) := by
    intro i hi
    exact mem_Icc.mpr ⟨Nat.zero_le _, reflectedLabel_le_half p i hp hodd⟩
  have h := sum_fiberwise_of_maps_to hm f
  have he : Icc 0 ((p - 1) / 2) = insert 0 (Icc 1 ((p - 1) / 2)) := by
    ext c
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert (by simp)] at h
  rw [reflectedLabel_zero_fiber N p hp] at h
  rw [← h]
  congr 1
  apply sum_congr rfl
  intro c hc
  have hc' := mem_Icc.mp hc
  rw [reflectedLabel_fiber N p c hp (by omega) (by omega)]

theorem sum_range_succ_eq_Ioc {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ i ∈ range N, f (i + 1)) = ∑ i ∈ Ioc 0 N, f i := by
  have he : Ioc 0 N = Ico 1 (N + 1) := by
    ext i
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [he]
  rw [sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

#print axioms sum_reflected_partition

end Zeta5.Arithmetic
