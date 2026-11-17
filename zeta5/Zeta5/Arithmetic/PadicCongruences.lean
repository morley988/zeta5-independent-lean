import Zeta5.Arithmetic.StieltjesValuations

/-! Elementary congruences in the ring of p-integral rational numbers. -/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial OddZeta.FourValue
variable {p : ℕ} [Fact p.Prime]

theorem padicIntegral_pow {x : ℚ} (hx : PadicLower p 0 x) (n : ℕ) :
    PadicLower p 0 (x ^ n) := by
  induction n with
  | zero => simp [PadicLower]
  | succ n ih => simpa [pow_succ] using ih.mul hx

theorem padicLower_mul_sub_mul {a b c d : ℚ}
    (ha : PadicLower p 0 a) (hd : PadicLower p 0 d)
    (hab : PadicLower p 1 (a - b)) (hcd : PadicLower p 1 (c - d)) :
    PadicLower p 1 (a * c - b * d) := by
  have h := (ha.mul hcd).add (hab.mul hd)
  convert h using 1 <;> ring

theorem padicLower_pow_sub_pow {x y : ℚ} (hx : PadicLower p 0 x)
    (hy : PadicLower p 0 y) (hxy : PadicLower p 1 (x - y)) (n : ℕ) :
    PadicLower p 1 (x ^ n - y ^ n) := by
  induction n with
  | zero => simpa using (PadicLower.zero (p := p) 1)
  | succ n ih =>
      simpa [pow_succ] using
        padicLower_mul_sub_mul (padicIntegral_pow hx n) hy ih hxy

theorem padicLower_inv_sub_inv {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxi : PadicLower p 0 x⁻¹) (hyi : PadicLower p 0 y⁻¹)
    (hxy : PadicLower p 1 (x - y)) : PadicLower p 1 (x⁻¹ - y⁻¹) := by
  have h := (hxy.neg).mul (hxi.mul hyi)
  have he : x⁻¹ - y⁻¹ = -(x - y) * (x⁻¹ * y⁻¹) := by
    field_simp
    ring
  rw [he]
  simpa using h

theorem padicLower_inv_add_inv {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxi : PadicLower p 0 x⁻¹) (hyi : PadicLower p 0 y⁻¹)
    (hxy : PadicLower p 1 (x + y)) : PadicLower p 1 (x⁻¹ + y⁻¹) := by
  have h := hxy.mul (hxi.mul hyi)
  have he : x⁻¹ + y⁻¹ = (x + y) * (x⁻¹ * y⁻¹) := by
    field_simp
    ring
  rw [he]
  simpa using h

theorem padicLower_eval_sub_eval {P : ℚ[X]} (hP : PolynomialPadicLower p 0 P)
    {x y : ℚ} (hx : PadicLower p 0 x) (hy : PadicLower p 0 y)
    (hxy : PadicLower p 1 (x - y)) : PadicLower p 1 (P.eval x - P.eval y) := by
  rw [P.as_sum_range_C_mul_X_pow]
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, ← Finset.sum_sub_distrib,
    ← mul_sub]
  apply padicLower_sum
  intro n hn
  simpa using (hP n).mul (padicLower_pow_sub_pow hx hy hxy n)

#print axioms padicLower_inv_sub_inv
#print axioms padicLower_eval_sub_eval

end Zeta5.Arithmetic
