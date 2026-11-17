import Zeta5.Arithmetic.AtomicMinors

/-! The atomic minor theorem for an actual finite set of natural nodes. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Allocation
variable {p : ℕ} [Fact p.Prime]

def finsetAtomicMatrix (s : Finset ℕ) (w : ℕ → ℚ[X]) (x : ℕ → ℚ) (r : ℕ) :
    Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => ∑ a ∈ s, w a * C ((x a) ^ (i.val + j.val))

theorem finset_atomic_minorLower (s high : Finset ℕ) (hsub : high ⊆ s)
    (w : ℕ → ℚ[X]) (x : ℕ → ℚ) (r : ℕ) (c : ℚ) (base : ℤ)
    (hc : PadicLower p 0 c)
    (hx : ∀ i ∈ s, PadicLower p 1 (x i - c))
    (hw : ∀ i ∈ s, PolynomialPadicLower p
      (base - 5 * (if i ∈ high then (1 : ℤ) else 0)) (w i)) :
    MinorLower (p := p) (finsetAtomicMatrix s w x r)
      (fun k => (k : ℤ) * (k - 1) + k * base - 5 * (min k high.card : ℕ)) := by
  let e := s.equivFin.symm
  let high' : Finset (Fin s.card) := Finset.univ.filter (fun j => (e j).val ∈ high)
  have hcard : high'.card = high.card := by
    apply Finset.card_bij (fun j _ => (e j).val)
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro i hi j hj hij
      exact e.injective (Subtype.ext hij)
    · intro i hi
      refine ⟨e.symm ⟨i, hsub hi⟩, ?_, ?_⟩
      · simp [high', hi]
      · simp
  have hsum (f : ℕ → ℚ[X]) : (∑ j, f (e j).val) = ∑ i ∈ s, f i := by
    rw [e.sum_comp (fun j : s => f j.val), Finset.sum_coe_sort]
  have hmatrix : atomicMatrix (fun j => w (e j).val) (fun j => x (e j).val) r =
      finsetAtomicMatrix s w x r := by
    funext i j
    exact hsum (fun a => w a * C ((x a) ^ (i.val + j.val)))
  have h := atomic_minorLower r (fun j => w (e j).val) (fun j => x (e j).val)
    c high' base hc (fun j => hx (e j).val (e j).property) (by
      intro j
      simpa only [high', Finset.mem_filter, Finset.mem_univ, true_and] using
        hw (e j).val (e j).property)
  rw [hmatrix, hcard] at h
  exact h

#print axioms finset_atomic_minorLower

end Zeta5.Arithmetic
