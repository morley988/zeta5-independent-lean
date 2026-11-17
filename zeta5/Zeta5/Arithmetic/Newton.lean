import Zeta5.Reuse.PolynomialValuations
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Newton interpolation over the local integers

The coefficients below are obtained by triangular interpolation at the
nonnegative integers.  This gives the integer-valued criterion without an
additional interpolation assumption.  Integrality at negative integers is
provided by Mathlib's integer binomial coefficients.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue

def binomialPolynomial (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ)⁻¹) * descPochhammer ℚ n

theorem binomialPolynomial_eval_nat (n k : ℕ) :
    (binomialPolynomial n).eval (k : ℚ) = (k.choose n : ℚ) := by
  rw [binomialPolynomial, eval_mul, eval_C,
    Nat.cast_choose_eq_descPochhammer_div ℚ k n]
  ring

theorem binomialPolynomial_eval_int (n : ℕ) (k : ℤ) :
    (binomialPolynomial n).eval (k : ℚ) = (Ring.choose k n : ℤ) := by
  have h : (descPochhammer ℤ n).eval k = (n.factorial : ℤ) * Ring.choose k n := by
    simpa only [eval_eq_smeval, nsmul_eq_mul] using
      Ring.descPochhammer_eq_factorial_smul_choose k n
  rw [binomialPolynomial, eval_mul, eval_C, ← descPochhammer_eval_cast]
  rw [h]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

theorem binomialPolynomial_natDegree (n : ℕ) :
    (binomialPolynomial n).natDegree = n := by
  rw [binomialPolynomial, natDegree_C_mul, descPochhammer_natDegree]
  exact inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)

def newtonCoefficient (g : ℚ[X]) (n : ℕ) : ℚ :=
  g.eval (n : ℚ) - ∑ a : Fin n, newtonCoefficient g a * (n.choose a : ℚ)
termination_by n

theorem newtonCoefficient_eq (g : ℚ[X]) (n : ℕ) :
    newtonCoefficient g n =
      g.eval (n : ℚ) - ∑ a ∈ range n, newtonCoefficient g a * (n.choose a : ℚ) := by
  rw [newtonCoefficient]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun a => newtonCoefficient g a * (n.choose a : ℚ)) n

def newtonExpansion (g : ℚ[X]) (L : ℕ) : ℚ[X] :=
  ∑ a ∈ range (L + 1), C (newtonCoefficient g a) * binomialPolynomial a

theorem newtonExpansion_natDegree_le (g : ℚ[X]) (L : ℕ) :
    (newtonExpansion g L).natDegree ≤ L := by
  apply natDegree_sum_le_of_forall_le
  intro a ha
  exact (natDegree_C_mul_le _ _).trans
    ((binomialPolynomial_natDegree a).le.trans (by simpa using mem_range.mp ha))

theorem newtonExpansion_eval_nat (g : ℚ[X]) {n L : ℕ} (hn : n ≤ L) :
    (newtonExpansion g L).eval (n : ℚ) = g.eval (n : ℚ) := by
  rw [newtonExpansion, eval_finsetSum]
  simp only [eval_mul, eval_C, binomialPolynomial_eval_nat]
  have he : (∑ a ∈ range (L + 1), newtonCoefficient g a * (n.choose a : ℚ)) =
      ∑ a ∈ range (n + 1), newtonCoefficient g a * (n.choose a : ℚ) := by
    symm
    apply sum_subset (range_mono (Nat.succ_le_succ hn))
    intro a ha hna
    have hna' : n < a := by simp only [mem_range] at hna; omega
    rw [Nat.choose_eq_zero_of_lt hna']
    simp
  rw [he, sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one, newtonCoefficient_eq]
  ring

theorem newtonExpansion_eq (g : ℚ[X]) {L : ℕ} (hL : g.natDegree ≤ L) :
    newtonExpansion g L = g := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f := fun n : Fin (L + 1) => (n : ℚ))
    _ _ (fun a b h => Fin.ext (Nat.cast_injective h))
  · intro n
    exact newtonExpansion_eval_nat g (Nat.le_of_lt_succ n.isLt)
  · simpa using And.intro (Nat.lt_succ_of_le (newtonExpansion_natDegree_le g L))
      (Nat.lt_succ_of_le hL)

def IntegerValuedAt (p : ℕ) (g : ℚ[X]) : Prop :=
  ∀ k : ℤ, PadicLower p 0 (g.eval (k : ℚ))

variable {p : ℕ} [Fact p.Prime]

theorem binomialPolynomial_integerValuedAt (n : ℕ) :
    IntegerValuedAt p (binomialPolynomial n) := by
  intro k
  rw [binomialPolynomial_eval_int]
  exact padicLower_int _

theorem newtonCoefficient_padicLower {g : ℚ[X]} (hg : IntegerValuedAt p g) (n : ℕ) :
    PadicLower p 0 (newtonCoefficient g n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [newtonCoefficient_eq, sub_eq_add_neg]
    have hn : PadicLower p 0 (g.eval (n : ℚ)) := by simpa using hg (n : ℤ)
    apply hn.add
    apply PadicLower.neg
    apply padicLower_sum
    intro a ha
    simpa using (ih a (mem_range.mp ha)).mul (padicLower_nat (n.choose a))

theorem integerValuedAt_iff_binomial_expansion (g : ℚ[X]) {L : ℕ}
    (hL : g.natDegree ≤ L) :
    IntegerValuedAt p g ↔ ∃ d : ℕ → ℚ,
      (∀ a ≤ L, PadicLower p 0 (d a)) ∧
      g = ∑ a ∈ range (L + 1), C (d a) * binomialPolynomial a := by
  constructor
  · intro hg
    exact ⟨newtonCoefficient g, fun a _ => newtonCoefficient_padicLower hg a,
      (newtonExpansion_eq g hL).symm⟩
  · rintro ⟨d, hd, rfl⟩ k
    rw [eval_finsetSum]
    apply padicLower_sum
    intro a ha
    simp only [eval_mul, eval_C]
    simpa using (hd a (Nat.le_of_lt_succ (mem_range.mp ha))).mul
      (binomialPolynomial_integerValuedAt (p := p) a k)

end Zeta5.Arithmetic
