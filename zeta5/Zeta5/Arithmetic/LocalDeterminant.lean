import Zeta5.Arithmetic.RestrictionPencil
import Zeta5.Arithmetic.RestrictionDeterminant

/-! Exact removal of the local prime scale from the actual window determinant. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

def unscaledCentralPencil (N m r : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => entry N (m + i.val) (m + j.val)

theorem scaledCentralPencil_det (N m r p : ℕ) :
    (scaledCentralPencil N m r p).det =
      C ((p : ℚ) ^ (localPencilScale N p * r)) * (unscaledCentralPencil N m r).det := by
  change (C ((p : ℚ) ^ localPencilScale N p) • unscaledCentralPencil N m r).det = _
  rw [Matrix.det_smul, Fintype.card_fin, ← C_pow, ← pow_mul]

theorem unscaledCentralPencil_lower_of_scaled (N m r d : ℕ)
    (hdet : PolynomialPadicLower p ((r : ℤ) - (min r d : ℕ)) (scaledCentralPencil N m r p).det) :
    PolynomialPadicLower p
      (-(4 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) - (min r d : ℕ))
      (unscaledCentralPencil N m r).det := by
  have h := (PolynomialPadicLower.constant
    (inverse_prime_power_padicLower (p := p) (localPencilScale N p * r))).mul hdet
  rw [scaledCentralPencil_det, ← mul_assoc, ← C_mul] at h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [inv_mul_cancel₀ (pow_ne_zero _ hp0), C_1, one_mul] at h
  convert h using 1
  simp only [localPencilScale, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem unscaledCentralPencil_window (n : ℕ) :
    unscaledCentralPencil (20 * n) n (24 * n) = windowPencil n := rfl

theorem windowRestrictionIndex_card_explicit (N m r : ℕ) (hp2 : p ≠ 2) :
    Fintype.card (WindowRestrictionIndex N m r p) =
      ((2 * (m + r) - 2) / p + 1) *
        (if 2 * (N % p) < p then N % p else N % p - (p - 1) / 2) := by
  rw [windowRestrictionIndex_card, maximalReflectedClasses_card N p
    ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp2)]
  rfl

theorem windowRestrictionIndex_stage_card (n : ℕ) (hp2 : p ≠ 2) :
    Fintype.card (WindowRestrictionIndex (20 * n) n (24 * n) p) =
      ((50 * n - 2) / p + 1) *
        (if 2 * ((20 * n) % p) < p then (20 * n) % p else (20 * n) % p - (p - 1) / 2) := by
  rw [windowRestrictionIndex_card_explicit (20 * n) n (24 * n) hp2]
  rw [show 2 * (n + 24 * n) = 50 * n by omega]

/-- The manuscript's local determinant estimate, for the actual factorial
window and its actual coefficient restriction matrix. -/
theorem unscaledCentralPencil_restriction_bound (N m r : ℕ) (hp : 5 < p)
    (hN : N ≤ m + r) (hsmall : 4 * (m + r) + 6 < p ^ 2) :
    PolynomialPadicLower p
      (-(4 + ((2 * (N % p) / p : ℕ) : ℤ)) * (r : ℤ) -
        (min r ((restrictionDepth m r p + 1) * (maximalReflectedClasses N p).card) : ℕ))
      (unscaledCentralPencil N m r).det := by
  have h := polynomialPadicLower_det_of_restriction_kernel
    (scaledCentralPencil N m r p) (centralRestrictionMatrix N m r p)
    (scaledCentralPencil_integral N m r hp hN hsmall)
    (centralRestrictionMatrix_integral N m r (by omega) (by omega))
    (scaledCentralPencil_restriction_radical N m r hp hN hsmall)
  rw [Fintype.card_fin, windowRestrictionIndex_card] at h
  exact unscaledCentralPencil_lower_of_scaled N m r _ h

theorem windowDeterminant_local_restriction_bound (n : ℕ) (hp : 5 < p)
    (hsmall : 100 * n + 6 < p ^ 2) :
    PolynomialPadicLower p
      (-(4 + ((2 * ((20 * n) % p) / p : ℕ) : ℤ)) * (24 * n : ℕ) -
        (min (24 * n) (((50 * n - 2) / p + 1) *
          (if 2 * ((20 * n) % p) < p then (20 * n) % p
           else (20 * n) % p - (p - 1) / 2)) : ℕ))
      (windowDeterminant n) := by
  have h := unscaledCentralPencil_restriction_bound (p := p) (20 * n) n (24 * n) hp
    (by omega) (by omega)
  rw [unscaledCentralPencil_window, ← windowDeterminant,
    maximalReflectedClasses_card (20 * n) p
      ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega))] at h
  simpa only [restrictionDepth, show 2 * (n + 24 * n) = 50 * n by omega] using h

end Zeta5.Arithmetic
