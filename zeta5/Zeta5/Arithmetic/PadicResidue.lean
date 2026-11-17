import Zeta5.Arithmetic.LocalDivision
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The residue field of the rational local integers

The construction uses the already verified valuation predicates.  No explicit
identification with `ZMod p` is needed: the ideal of elements of valuation at
least one is maximal because every element outside it has an integral inverse.
-/

noncomputable section
namespace Zeta5.Arithmetic
open OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

def padicMaximalIdeal (p : ℕ) [Fact p.Prime] : Ideal (padicIntegralSubring p) where
  carrier := {x | PadicLower p 1 (x : ℚ)}
  zero_mem' := PadicLower.zero 1
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun a _ hb => by
    simpa using a.property.mul hb

@[simp] theorem mem_padicMaximalIdeal (x : padicIntegralSubring p) :
    x ∈ padicMaximalIdeal p ↔ PadicLower p 1 (x : ℚ) := Iff.rfl

theorem padicIntegral_inv_of_not_lower_one {x : ℚ}
    (hx : PadicLower p 0 x) (h : ¬ PadicLower p 1 x) : PadicLower p 0 x⁻¹ := by
  have hx0 : x ≠ 0 := fun h0 => h (Or.inl h0)
  have hval : padicValRat p x = 0 := by
    have hlo := hx.of_ne_zero hx0
    have hhi : padicValRat p x < 1 := by
      by_contra! hh
      exact h (Or.inr hh)
    omega
  right
  rw [padicValRat.inv, hval]
  rfl

instance padicMaximalIdeal_isMaximal : (padicMaximalIdeal p).IsMaximal := by
  apply Ideal.isMaximal_iff.mpr
  constructor
  · change ¬ PadicLower p 1 (1 : ℚ)
    simp [PadicLower]
  · intro J x hIJ hx hxJ
    let y : padicIntegralSubring p :=
      ⟨(x : ℚ)⁻¹, padicIntegral_inv_of_not_lower_one x.property hx⟩
    have hxy : y * x = 1 := by
      apply Subtype.ext
      exact inv_mul_cancel₀ (fun h0 => hx (Or.inl h0))
    simpa only [hxy] using J.mul_mem_left y hxJ

abbrev PadicResidueField (p : ℕ) [Fact p.Prime] :=
  padicIntegralSubring p ⧸ padicMaximalIdeal p

noncomputable instance : Field (PadicResidueField p) :=
  Ideal.Quotient.field (padicMaximalIdeal p)

abbrev padicReduction (p : ℕ) [Fact p.Prime] :
    padicIntegralSubring p →+* PadicResidueField p :=
  Ideal.Quotient.mk (padicMaximalIdeal p)

@[simp] theorem padicReduction_eq_zero (x : padicIntegralSubring p) :
    padicReduction p x = 0 ↔ PadicLower p 1 (x : ℚ) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem padicReduction_surjective : Function.Surjective (padicReduction p) :=
  Ideal.Quotient.mk_surjective

/-- Any nonzero residue has a lift whose rational inverse is again integral. -/
theorem padicReduction_ne_zero_inv {x : padicIntegralSubring p}
    (hx : padicReduction p x ≠ 0) : PadicLower p 0 ((x : ℚ)⁻¹) :=
  padicIntegral_inv_of_not_lower_one x.property (fun h => hx (padicReduction_eq_zero x |>.mpr h))

end Zeta5.Arithmetic
