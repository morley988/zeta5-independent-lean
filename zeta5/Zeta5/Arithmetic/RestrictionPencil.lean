import Zeta5.Arithmetic.LocalFunctional

/-!
# The concrete coefficient restriction matrix and its radical

Rows record the actual coefficients of the central basis polynomials on
maximal reflected residue classes. The resulting kernel condition is
proved to annihilate every coefficient of the scaled window pairing.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

def centralWindowPolynomial (m r : ℕ) (x : Fin r → ℚ) : ℚ[X] :=
  ∑ i : Fin r, C (x i) * centralPolynomial (m + i.val)

theorem centralWindowPolynomial_natDegree_le (m r : ℕ) (x : Fin r → ℚ) :
    (centralWindowPolynomial m r x).natDegree ≤ m + r - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply (natDegree_C_mul_le _ _).trans
  rw [centralPolynomial_natDegree]
  have := i.isLt
  omega

theorem centralWindowPolynomial_squareValued (hp2 : p ≠ 2) (m r : ℕ) (x : Fin r → ℚ)
    (hx : ∀ i, PadicLower p 0 (x i)) : SquareValuedLower p 0 (centralWindowPolynomial m r x) := by
  intro k
  rw [centralWindowPolynomial, eval_finsetSum]
  apply padicLower_sum
  intro i hi
  rw [eval_mul, eval_C]
  have h := centralPolynomial_square_padicLower (p := p) (m + i.val) k
  rw [padicValNat_two_eq_zero hp2] at h
  simpa using (hx i).mul h

theorem centralWindowPolynomial_square_natDegree_le (m r : ℕ) (x : Fin r → ℚ) :
    ((centralWindowPolynomial m r x).comp (X ^ 2)).natDegree ≤ 2 * (m + r) - 2 := by
  rw [natDegree_comp, natDegree_X_pow]
  have := centralWindowPolynomial_natDegree_le m r x
  omega

def restrictionDepth (m r p : ℕ) : ℕ := (2 * (m + r) - 2) / p

abbrev WindowRestrictionIndex (N m r p : ℕ) :=
  {c // c ∈ maximalReflectedClasses N p} × Fin (restrictionDepth m r p + 1)

def centralRestrictionMatrix (N m r p : ℕ) :
    Matrix (WindowRestrictionIndex N m r p) (Fin r) ℚ :=
  fun a i => ((centralPolynomial (m + i.val)).comp ((localAffine p a.1.val) ^ 2)).coeff a.2.val

theorem centralRestrictionMatrix_integral (N m r : ℕ) (hp2 : p ≠ 2)
    (hsmall : 2 * (m + r) - 2 < p ^ 2) :
    ∀ a i, PadicLower p 0 (centralRestrictionMatrix N m r p a i) := by
  intro a i
  have hi := i.isLt
  have h := centralPolynomial_local_integral hp2 (j := m + i.val) (by omega) (a.1.val : ℤ)
  simpa only [centralRestrictionMatrix, comp_assoc, pow_comp, X_comp] using h a.2.val

theorem centralRestrictionMatrix_kernel (N m r : ℕ) (hp2 : p ≠ 2)
    (hsmall : 2 * (m + r) - 2 < p ^ 2) (x : Fin r → ℚ)
    (hx : ∀ i, PadicLower p 0 (x i))
    (hR : ∀ a, PadicLower p 1 (∑ i, centralRestrictionMatrix N m r p a i * x i)) :
    ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 ((centralWindowPolynomial m r x).comp ((localAffine p c) ^ 2)) := by
  intro c hc k
  by_cases hk : k ≤ restrictionDepth m r p
  · have h := hR (⟨c, hc⟩, ⟨k, by omega⟩)
    simp only [centralWindowPolynomial, Polynomial.sum_comp, mul_comp, C_comp,
      finsetSum_coeff, coeff_C_mul]
    simpa only [centralRestrictionMatrix, mul_comm] using h
  · have hI : IntegerValuedAt p ((centralWindowPolynomial m r x).comp (X ^ 2)) := by
      intro z
      simpa only [eval_comp, eval_pow, eval_X] using
        centralWindowPolynomial_squareValued hp2 m r x hx z
    have h := integerValuedAt_local_high_coeff hI (centralWindowPolynomial_square_natDegree_le m r x)
      hsmall (show (2 * (m + r) - 2) / p < k by exact Nat.lt_of_not_ge hk) (c : ℤ)
    simpa only [comp_assoc, pow_comp, X_comp] using h

theorem windowRestrictionIndex_card (N m r p : ℕ) :
    Fintype.card (WindowRestrictionIndex N m r p) =
      (restrictionDepth m r p + 1) * (maximalReflectedClasses N p).card := by
  simp [WindowRestrictionIndex, Fintype.card_prod, Nat.mul_comm]

def localPencilScale (N p : ℕ) : ℕ := 5 + 2 * (N % p) / p

def scaledCentralPencil (N m r p : ℕ) : Matrix (Fin r) (Fin r) ℚ[X] :=
  fun i j => C ((p : ℚ) ^ localPencilScale N p) * entry N (m + i.val) (m + j.val)

theorem entry_eq_normalizedCentralFunctional (N j k : ℕ) :
    entry N j k = normalizedCentralFunctional N (centralPolynomial j * centralPolynomial k) := by
  rw [entry_eq_numeratorFunctional, normalizedCentralFunctional_eq, mul_comp]
  rfl

theorem centralPolynomial_squareValued (hp2 : p ≠ 2) (j : ℕ) :
    SquareValuedLower p 0 (centralPolynomial j) := by
  simpa only [padicValNat_two_eq_zero hp2, Nat.cast_zero, neg_zero] using
    centralPolynomial_square_padicLower (p := p) j

theorem SquareValuedLower.mul {f g : ℚ[X]} {u v : ℤ}
    (hf : SquareValuedLower p u f) (hg : SquareValuedLower p v g) :
    SquareValuedLower p (u + v) (f * g) := by
  intro k
  rw [eval_mul]
  exact (hf k).mul (hg k)

theorem scaledCentralPencil_integral (N m r : ℕ) (hp : 5 < p)
    (hN : N ≤ m + r) (hsmall : 4 * (m + r) + 6 < p ^ 2) :
    ∀ i j, PolynomialPadicLower p 0 (scaledCentralPencil N m r p i j) := by
  intro i j
  have hdeg : (centralPolynomial (m + i.val) * centralPolynomial (m + j.val)).natDegree ≤ 2 * (m + r) := by
    apply natDegree_mul_le.trans
    rw [centralPolynomial_natDegree, centralPolynomial_natDegree]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hg : SquareValuedLower p 0 (centralPolynomial (m + i.val) * centralPolynomial (m + j.val)) := by
    exact (centralPolynomial_squareValued (by omega : p ≠ 2) _).mul (centralPolynomial_squareValued (by omega) _)
  have h := normalizedCentralFunctional_padicLower (N := N) hp hg (by omega)
  have hscaled := (PolynomialPadicLower.constant (prime_power_padicLower (p := p) (localPencilScale N p))).mul h
  rw [scaledCentralPencil, entry_eq_normalizedCentralFunctional]
  convert hscaled using 1 <;> simp [localPencilScale] <;> omega

theorem normalizedCentralFunctional_C_mul (N : ℕ) (a : ℚ) (g : ℚ[X]) :
    normalizedCentralFunctional N (C a * g) = C a * normalizedCentralFunctional N g := by
  unfold normalizedCentralFunctional
  rw [mul_comp, C_comp]
  have he : C ((N.factorial : ℚ) ^ 2) * (C a * g.comp (-X)) =
      a • (C ((N.factorial : ℚ) ^ 2) * g.comp (-X)) := by rw [smul_eq_C_mul]; ring
  rw [he, map_smul, smul_eq_C_mul]

theorem normalizedCentralFunctional_sum {ι : Type*} (N : ℕ) (s : Finset ι) (g : ι → ℚ[X]) :
    normalizedCentralFunctional N (∑ i ∈ s, g i) = ∑ i ∈ s, normalizedCentralFunctional N (g i) := by
  simp only [normalizedCentralFunctional, Polynomial.sum_comp, mul_sum, map_sum]

theorem centralWindow_pairing (N m r : ℕ) (x : Fin r → ℚ) (j : Fin r) :
    normalizedCentralFunctional N (centralWindowPolynomial m r x * centralPolynomial (m + j.val)) =
      ∑ i, C (x i) * entry N (m + i.val) (m + j.val) := by
  have he : centralWindowPolynomial m r x * centralPolynomial (m + j.val) =
      ∑ i : Fin r, C (x i) * (centralPolynomial (m + i.val) * centralPolynomial (m + j.val)) := by
    simp only [centralWindowPolynomial, sum_mul, mul_assoc]
  rw [he, normalizedCentralFunctional_sum]
  apply sum_congr rfl
  intro i hi
  rw [normalizedCentralFunctional_C_mul, entry_eq_normalizedCentralFunctional]

theorem scaledCentralPencil_restriction_radical (N m r : ℕ) (hp : 5 < p)
    (hN : N ≤ m + r) (hsmall : 4 * (m + r) + 6 < p ^ 2)
    (x : Fin r → ℚ) (hx : ∀ i, PadicLower p 0 (x i))
    (hR : ∀ a, PadicLower p 1 (∑ i, centralRestrictionMatrix N m r p a i * x i)) :
    ∀ j, PolynomialPadicLower p 1 (∑ i, C (x i) * scaledCentralPencil N m r p i j) := by
  intro j
  have hp2 : p ≠ 2 := by omega
  have hF := centralWindowPolynomial_squareValued hp2 m r x hx
  have hG := centralPolynomial_squareValued (p := p) hp2 (m + j.val)
  have hg : SquareValuedLower p 0 (centralWindowPolynomial m r x * centralPolynomial (m + j.val)) :=
    hF.mul hG
  have hdeg : (centralWindowPolynomial m r x * centralPolynomial (m + j.val)).natDegree ≤ 2 * (m + r) := by
    have hmul := natDegree_mul_le (p := centralWindowPolynomial m r x) (q := centralPolynomial (m + j.val))
    rw [centralPolynomial_natDegree] at hmul
    have hFdeg := centralWindowPolynomial_natDegree_le m r x
    have hj := j.isLt
    omega
  have hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 ((centralWindowPolynomial m r x * centralPolynomial (m + j.val)).comp
        ((localAffine p c) ^ 2)) := by
    intro c hc
    have hFgain := centralRestrictionMatrix_kernel N m r hp2 (by omega) x hx hR c hc
    have hGlocal := centralPolynomial_local_integral hp2 (j := m + j.val)
      (by have := j.isLt; omega) (c : ℤ)
    rw [mul_comp]
    simpa only [comp_assoc, pow_comp, X_comp, add_zero] using hFgain.mul hGlocal
  have h := normalizedCentralFunctional_padicLower_on_kernel hp hg (by omega) hkernel
  have hscaled := (PolynomialPadicLower.constant
    (prime_power_padicLower (p := p) (localPencilScale N p))).mul h
  have he : (∑ i, C (x i) * scaledCentralPencil N m r p i j) =
      C ((p : ℚ) ^ localPencilScale N p) *
        normalizedCentralFunctional N (centralWindowPolynomial m r x * centralPolynomial (m + j.val)) := by
    rw [centralWindow_pairing, mul_sum]
    apply sum_congr rfl
    intro i hi
    unfold scaledCentralPencil
    ring
  rw [he]
  convert hscaled using 1 <;> simp [localPencilScale] <;> omega

end Zeta5.Arithmetic
