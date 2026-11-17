import Zeta5.Arithmetic.Newton
import Zeta5.Arithmetic.StieltjesValuations

/-!
# Derivatives in the Newton basis

Chu--Vandermonde and the linear coefficient of a falling factorial give
the exact derivative formula.  The resulting integer-value bounds apply
to every prime and every derivative order.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue

theorem binomialPolynomial_eval_choose (n : ℕ) (x : ℚ) :
    (binomialPolynomial n).eval x = Ring.choose x n := by
  rw [binomialPolynomial, eval_mul, eval_C, Ring.choose_eq_smul,
    descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
    descPochhammer_eval_eq_ascPochhammer, smul_eq_mul]

theorem binomialPolynomial_taylor (n : ℕ) (r : ℚ) :
    (binomialPolynomial n).taylor r =
      ∑ ij ∈ antidiagonal n, C ((binomialPolynomial ij.2).eval r) * binomialPolynomial ij.1 := by
  apply Polynomial.funext
  intro x
  simp only [taylor_eval, eval_finsetSum, eval_mul, eval_C, binomialPolynomial_eval_choose]
  simpa only [mul_comm] using Ring.add_choose_eq (r := x) (s := r) n (Commute.all _ _)

theorem descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    ring

theorem binomialPolynomial_coeff_one_zero : (binomialPolynomial 0).coeff 1 = 0 := by
  simp [binomialPolynomial, coeff_one]

theorem binomialPolynomial_coeff_one_succ (n : ℕ) :
    (binomialPolynomial (n + 1)).coeff 1 = (-1 : ℚ) ^ n / (n + 1 : ℕ) := by
  rw [binomialPolynomial, coeff_C_mul, descPochhammer_succ_left]
  have he : (X * (descPochhammer ℚ n).comp (X - 1)).coeff 1 =
      (descPochhammer ℚ n).eval (-1) := by
    rw [show 1 = 0 + 1 by rfl, coeff_X_mul, coeff_zero_eq_eval_zero]
    simp
  rw [he, descPochhammer_eval_neg_one, Nat.factorial_succ, Nat.cast_mul]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [hf]

theorem binomialPolynomial_derivative_antidiagonal (n : ℕ) :
    (binomialPolynomial n).derivative =
      ∑ ij ∈ antidiagonal n, C ((binomialPolynomial ij.1).coeff 1) * binomialPolynomial ij.2 := by
  apply Polynomial.funext
  intro r
  have h := congr_arg (fun P : ℚ[X] => P.coeff 1) (binomialPolynomial_taylor n r)
  rw [taylor_coeff_one, finsetSum_coeff] at h
  simp only [coeff_C_mul] at h
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C]
  simpa only [mul_comm] using h

/-- The manuscript formula with `b = i+1`. -/
theorem binomialPolynomial_derivative (n : ℕ) :
    (binomialPolynomial n).derivative =
      ∑ i ∈ range n, C ((-1 : ℚ) ^ i / (i + 1 : ℕ)) * binomialPolynomial (n - (i + 1)) := by
  rw [binomialPolynomial_derivative_antidiagonal,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  simp only [binomialPolynomial_coeff_one_zero, C_0, zero_mul, add_zero,
    binomialPolynomial_coeff_one_succ]

def IntegerValuedLower (p : ℕ) (w : ℤ) (g : ℚ[X]) : Prop :=
  ∀ k : ℤ, PadicLower p w (g.eval (k : ℚ))

variable {p : ℕ} [Fact p.Prime]

theorem newtonCoefficient_padicLower_weighted {g : ℚ[X]} {w : ℤ}
    (hg : IntegerValuedLower p w g) (n : ℕ) : PadicLower p w (newtonCoefficient g n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [newtonCoefficient_eq, sub_eq_add_neg]
    have hn : PadicLower p w (g.eval (n : ℚ)) := by simpa using hg (n : ℤ)
    apply hn.add
    apply PadicLower.neg
    apply padicLower_sum
    intro a ha
    simpa using (ih a (mem_range.mp ha)).mul (padicLower_nat (n.choose a))

theorem binomialPolynomial_derivative_padicLower {n L : ℕ} {d : ℤ} (hnL : n ≤ L)
    (hden : ∀ b : ℕ, 0 < b → b ≤ L → PadicLower p (-d) ((b : ℚ)⁻¹)) :
    IntegerValuedLower p (-d) (binomialPolynomial n).derivative := by
  intro k
  rw [binomialPolynomial_derivative, eval_finsetSum]
  apply padicLower_sum
  intro i hi
  simp only [eval_mul, eval_C, div_eq_mul_inv]
  have hs : PadicLower p 0 ((-1 : ℚ) ^ i) := by
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ i)
  have hd := hden (i + 1) (by omega) ((Nat.succ_le_of_lt (mem_range.mp hi)).trans hnL)
  have hb := binomialPolynomial_integerValuedAt (p := p) (n - (i + 1)) k
  simpa using (hs.mul hd).mul hb

theorem integerValuedLower_derivative {g : ℚ[X]} {w d : ℤ} {L : ℕ}
    (hg : IntegerValuedLower p w g) (hL : g.natDegree ≤ L)
    (hden : ∀ b : ℕ, 0 < b → b ≤ L → PadicLower p (-d) ((b : ℚ)⁻¹)) :
    IntegerValuedLower p (w - d) g.derivative := by
  intro k
  have he : g = ∑ a ∈ range (L + 1), C (newtonCoefficient g a) * binomialPolynomial a :=
    (newtonExpansion_eq g hL).symm
  rw [he, derivative_sum, eval_finsetSum]
  apply padicLower_sum
  intro a ha
  rw [derivative_C_mul, eval_mul, eval_C]
  have hd := binomialPolynomial_derivative_padicLower (p := p)
    (Nat.le_of_lt_succ (mem_range.mp ha)) hden k
  simpa [sub_eq_add_neg] using (newtonCoefficient_padicLower_weighted hg a).mul hd

theorem integerValuedLower_derivative_log {g : ℚ[X]} {w : ℤ} {L : ℕ}
    (hg : IntegerValuedLower p w g) (hL : g.natDegree ≤ L) :
    IntegerValuedLower p (w - (Nat.log p L : ℤ)) g.derivative := by
  apply integerValuedLower_derivative hg hL
  intro b hb hbL
  right
  rw [padicValRat.inv, padicValRat.of_nat]
  exact neg_le_neg (by exact_mod_cast
    (padicValNat_le_nat_log b).trans (Nat.log_mono_right hbL))

theorem integerValuedLower_derivative_below_square {g : ℚ[X]} {w : ℤ} {L : ℕ}
    (hg : IntegerValuedLower p w g) (hL : g.natDegree ≤ L) (hLp : L < p ^ 2) :
    IntegerValuedLower p (w - 1) g.derivative := by
  apply integerValuedLower_derivative hg hL
  intro b hb hbL
  simpa using reciprocalPower_padicLower (p := p) b 1 hb (hbL.trans_lt hLp)

theorem integerValuedLower_iterate_derivative {g : ℚ[X]} {w d : ℤ} {L : ℕ}
    (hg : IntegerValuedLower p w g) (hL : g.natDegree ≤ L)
    (hden : ∀ b : ℕ, 0 < b → b ≤ L → PadicLower p (-d) ((b : ℚ)⁻¹)) (k : ℕ) :
    IntegerValuedLower p (w - (k : ℤ) * d) (derivative^[k] g) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hd : (derivative^[k] g).natDegree ≤ L :=
      (natDegree_iterate_derivative g k).trans ((Nat.sub_le _ _).trans hL)
    have h := integerValuedLower_derivative ih hd hden
    convert h using 1 <;> push_cast <;> ring

theorem integerValuedLower_iterate_derivative_below_square {g : ℚ[X]} {w : ℤ} {L : ℕ}
    (hg : IntegerValuedLower p w g) (hL : g.natDegree ≤ L) (hLp : L < p ^ 2) (k : ℕ) :
    IntegerValuedLower p (w - (k : ℤ)) (derivative^[k] g) := by
  have h := integerValuedLower_iterate_derivative hg hL (d := 1) (by
    intro b hb hbL
    simpa using reciprocalPower_padicLower (p := p) b 1 hb (hbL.trans_lt hLp)) k
  simpa using h

end Zeta5.Arithmetic
