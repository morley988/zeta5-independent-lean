import Zeta5.Arithmetic.ReflectedBounds
import Zeta5.Arithmetic.ReflectedPartition
import Zeta5.Arithmetic.ZeroClass

/-! The complete monomial determinant bound in the upper prime band.
All atom matrices, class counts, and quotient terms are the actual ones. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction Allocation Finset
variable {p : ℕ} [Fact p.Prime]

def upperHighCount (N p : ℕ) : ℕ := N - p - (N / p - 1)
def upperAffectedCount (N m p : ℕ) : ℕ :=
  2 * (N / p - 1) * (m - 1) + min (m - 1) (N % p) + (m + N % p - p)

theorem sum_fin_succ_eq_Icc {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → M) :
    (∑ i : Fin d, f (i.val + 1)) = ∑ c ∈ Icc 1 d, f c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)), sum_range_succ_eq_Ioc]
  congr 1

theorem sum_reflectedPenalty (N m p : ℕ) (hm : 0 < m) (hpN : p ≤ N)
    (hmp : 2 * m < p) (hodd : p % 2 = 1) :
    (∑ c ∈ Icc 1 ((p - 1) / 2), reflectedPenalty N m p c) =
      7 * (upperHighCount N p : ℤ) - 2 * (upperAffectedCount N m p : ℤ) := by
  have hfilter : (Icc 1 ((p - 1) / 2)).filter (fun c => c < m) = Icc 1 (m - 1) := by
    ext c
    simp only [mem_filter, mem_Icc]
    omega
  have hA : (∑ c ∈ Icc 1 ((p - 1) / 2),
      if c < m then (highReflectedNodes N p c).card else 0) = upperAffectedCount N m p := by
    rw [← sum_filter, hfilter]
    exact affected_highReflectedNodes N p m hm hpN hmp
  have hAZ : (∑ c ∈ Icc 1 ((p - 1) / 2),
      if c < m then ((highReflectedNodes N p c).card : ℤ) else 0) =
      (upperAffectedCount N m p : ℤ) := by exact_mod_cast hA
  have hHZ : (∑ c ∈ Icc 1 ((p - 1) / 2), ((highReflectedNodes N p c).card : ℤ)) =
      (upperHighCount N p : ℤ) := by
    exact_mod_cast total_highReflectedNodes N p hpN hodd
  have he (c : ℕ) : reflectedPenalty N m p c =
      7 * (highReflectedNodes N p c).card -
        2 * (if c < m then ((highReflectedNodes N p c).card : ℤ) else 0) := by
    unfold reflectedPenalty
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hHZ, hAZ]

theorem monomialPencil_reflected_decomposition (N m r p : ℕ)
    (hp : 0 < p) (hodd : p % 2 = 1) :
    monomialPencil N m r =
      (quotientPencil N m r + ∑ i ∈ zeroClassNodes N p, monomialAtom N m r i) +
        ∑ c : Fin ((p - 1) / 2), monomialReflectedClass N m r p (c.val + 1) := by
  rw [monomialPencil_residue_decomposition, sum_range_succ_eq_Ioc,
    sum_reflected_partition N p hp hodd, sum_fin_succ_eq_Icc]
  simp_rw [monomialReflectedClass_eq_sum]
  rw [add_assoc]

theorem monomialPencil_upperBand_bound (N m R : ℕ) (hp : 5 < p)
    (hm : 0 < m) (hmR : m ≤ R) (hmp : 2 * m < p)
    (hpN : p ≤ N) (hN : N < 3 * p) (hsmall : 2 * N < p ^ 2)
    (hHr : upperHighCount N p ≤ R - m) :
    PolynomialPadicLower p
      (-7 * (upperHighCount N p : ℤ) + 2 * (upperAffectedCount N m p : ℤ) -
        (min (terminalSize N m R p) (R - m - upperHighCount N p) : ℕ))
      (monomialPencil N m (R - m)).det := by
  have hp0 : 0 < p := by omega
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega)
  let Z : Matrix (Fin (R - m)) (Fin (R - m)) ℚ[X] :=
    ∑ i ∈ zeroClassNodes N p, monomialAtom N m (R - m) i
  let Q := quotientPencil N m (R - m) + Z
  let A : Fin ((p - 1) / 2) → Matrix (Fin (R - m)) (Fin (R - m)) ℚ[X] :=
    fun c => monomialReflectedClass N m (R - m) p (c.val + 1)
  let high : Fin ((p - 1) / 2) → ℕ := fun c => (highReflectedNodes N p (c.val + 1)).card
  let pen : Fin ((p - 1) / 2) → ℤ := fun c => reflectedPenalty N m p (c.val + 1)
  have hhigh : (∑ c, high c) = upperHighCount N p := by
    rw [show (∑ c, high c) = ∑ c ∈ Icc 1 ((p - 1) / 2), (highReflectedNodes N p c).card from
      sum_fin_succ_eq_Icc ((p - 1) / 2) (fun c => (highReflectedNodes N p c).card)]
    exact total_highReflectedNodes N p hpN hodd
  have hpen : (∑ c, pen c) = 7 * (upperHighCount N p : ℤ) -
      2 * (upperAffectedCount N m p : ℤ) := by
    rw [show (∑ c, pen c) = ∑ c ∈ Icc 1 ((p - 1) / 2), reflectedPenalty N m p c from
      sum_fin_succ_eq_Icc ((p - 1) / 2) (reflectedPenalty N m p)]
    exact sum_reflectedPenalty N m p hm hpN hmp hodd
  have hZ : ∀ i j, PolynomialPadicLower p 0 (Z i j) := by
    intro i j
    simp only [Z, Matrix.sum_apply]
    apply PolynomialPadicLower.sum
    intro k hk
    obtain ⟨hkI, hpk⟩ := mem_filter.mp hk
    obtain ⟨hk0, hkN⟩ := mem_Ioc.mp hkI
    exact zero_class_atom_integral N m (R - m) k hp hm hk0 hkN hpk hN hsmall i j
  have hQ : MinorLower (p := p) Q (fun a => -(min a (terminalSize N m R p) : ℤ)) := by
    apply minorLower_add_integral _ Z _ hZ
    intro a rows cols
    simpa only [Nat.cast_min] using quotientPencil_minor_padicLower N m R a hp hmR rows cols
  have hA (c : Fin ((p - 1) / 2)) := reflected_class_dual_bounds N m (R - m) (c.val + 1)
    hp (by omega) (by have hc := c.isLt; omega) hpN hN hsmall
  have h := shared_dimension_matrix_bound (p := p) Q A pen high (terminalSize N m R p)
    (by rw [hhigh]; exact hHr) hQ (fun c => (hA c).1) (fun c => (hA c).2)
  have heq : Q + ∑ c, A c = monomialPencil N m (R - m) :=
    (monomialPencil_reflected_decomposition N m (R - m) p hp0 hodd).symm
  rw [heq, hhigh, hpen] at h
  convert h using 1 <;> ring

#print axioms monomialPencil_upperBand_bound

end Zeta5.Arithmetic
