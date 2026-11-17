import Zeta5.Analysis.PhysicalMeasureBose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-! # Real coth partial fractions for the Bose kernel -/

noncomputable section
namespace Zeta5.Analysis.PhysicalMeasure
open Real Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators

theorem cauchySeries_summable (x : ℝ) :
    Summable (fun n : ℕ => 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => one_div_le_one_div_of_le (by positivity : 0 < ((n + 1 : ℕ) : ℝ) ^ 2)
      (by nlinarith [sq_nonneg x]))
  exact (summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr (by omega : 1 < 2))

/-- The coth expansion, arranged so all series terms are nonnegative.
The statement follows from Mathlib's verified cotangent partial fractions. -/
theorem x_bose_coth {x : ℝ} (hx : 0 < x) :
    x * bose x = 1 / (2 * Real.pi) - x / 2 +
      x ^ 2 / Real.pi * ∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
  let z : ℂ := (x : ℂ) * Complex.I
  have hz : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, by simpa [z] using hx⟩
  have hexp : Complex.exp (2 * Real.pi * Complex.I * z) =
      (Real.exp (-(2 * Real.pi * x)) : ℂ) := by
    have he : (2 : ℂ) * Real.pi * Complex.I * z = ((-(2 * Real.pi * x) : ℝ) : ℂ) := by
      dsimp [z]
      push_cast
      calc
        _ = 2 * Real.pi * (x : ℂ) * (Complex.I * Complex.I) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    rw [he, Complex.ofReal_exp]
  have hq : Real.exp (-(2 * Real.pi * x)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity))
  have hq0 : 1 - Real.exp (-(2 * Real.pi * x)) ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hcot : (Complex.cot (Real.pi * z)).im =
      -(Real.exp (-(2 * Real.pi * x)) + 1) / (1 - Real.exp (-(2 * Real.pi * x))) := by
    rw [Complex.cot_pi_eq_exp_ratio, hexp]
    simp only [Complex.div_im, Complex.add_re, Complex.ofReal_re, Complex.one_re,
      Complex.add_im, Complex.ofReal_im, Complex.one_im, add_zero, Complex.mul_re,
      Complex.I_re, Complex.sub_re, Complex.zero_re, Complex.mul_im, Complex.I_im,
      Complex.sub_im, zero_sub, zero_mul, one_mul, sub_zero, zero_add, Complex.normSq_apply]
    field_simp
    <;> ring
  have hterm (n : ℕ) :
      (1 / (z - ((n + 1 : ℕ) : ℂ)) + 1 / (z + ((n + 1 : ℕ) : ℂ))).im =
        (-2 * x) * (1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simp only [z, Complex.add_im, Complex.div_im, Complex.one_im, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.mul_im, Complex.sub_im, Complex.natCast_im, Complex.sub_re, Complex.natCast_re,
      Complex.add_re, zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub,
      zero_add, add_zero, Complex.normSq_apply]
    ring
  have h := congrArg Complex.im (cot_series_rep' hz)
  rw [Complex.im_tsum (summable_cotTerm hz)] at h
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, hcot] at h
  have hzInv : (1 / z).im = -(1 / x) := by
    dsimp [z]
    simp only [Complex.div_im, Complex.one_im, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.mul_im,
      zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, zero_add,
      Complex.normSq_apply]
    field_simp
    <;> ring
  rw [hzInv] at h
  have hs : (∑' n : ℕ, (cotTerm z n).im) =
      (-2 * x) * ∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      _ = ∑' n : ℕ, (-2 * x) * (1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)) := by
        apply tsum_congr
        intro n
        simpa only [cotTerm, Nat.cast_add, Nat.cast_one] using hterm n
      _ = _ := tsum_mul_left
  rw [hs] at h
  rw [bose_eq_geometric hx]
  have hpi := Real.pi_ne_zero
  have hx0 := hx.ne'
  generalize hqdef : Real.exp (-(2 * Real.pi * x)) = q at h hq0 ⊢
  field_simp [hq0] at h ⊢
  nlinarith

end Zeta5.Analysis.PhysicalMeasure
