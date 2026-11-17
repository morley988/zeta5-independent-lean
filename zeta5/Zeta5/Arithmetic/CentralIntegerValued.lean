import Zeta5.Arithmetic.LocalNewton

/-!
# The central binomial identity and integer-valued central basis

These statements concern the actual `centralPolynomial` used in the
determinant.  The binomial identity establishes integer values of twice
the central polynomial at every integer square.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue Zeta5.Construction

def symmetricFalling (l : ℕ) : ℚ[X] :=
  (descPochhammer ℚ (2 * l + 1)).comp (X + C (l : ℚ))

theorem symmetricFalling_zero : symmetricFalling 0 = X := by
  simp [symmetricFalling]

theorem symmetricFalling_succ (l : ℕ) :
    symmetricFalling (l + 1) = symmetricFalling l * (X ^ 2 - C ((l + 1 : ℚ) ^ 2)) := by
  have hindex : 2 * (l + 1) + 1 = (2 * l + 1) + 1 + 1 := by omega
  unfold symmetricFalling
  rw [hindex, descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
  have he : (X - 1 : ℚ[X]).comp (X + C ((l + 1 : ℕ) : ℚ)) = X + C (l : ℚ) := by
    simp only [sub_comp, X_comp, one_comp, Nat.cast_add, Nat.cast_one, C_add, C_1]
    ring
  rw [he, descPochhammer_succ_right, mul_comp]
  simp only [sub_comp, X_comp, add_comp, mul_comp, natCast_comp, one_comp,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, C_add, C_1, C_mul]
  simp only [natCast_comp, one_comp, ofNat_comp]
  rw [C_pow, C_add, C_1]
  simp only [C_eq_natCast]
  ring

theorem rootPolynomial_square_symmetric (l : ℕ) :
    (rootPolynomial (l + 1)).comp (X ^ 2) = X * symmetricFalling l := by
  induction l with
  | zero => simp [rootPolynomial, symmetricFalling_zero, pow_two]
  | succ l ih =>
    have hrec : rootPolynomial (l + 1 + 1) =
        rootPolynomial (l + 1) * (X - C (((l + 1 : ℕ) : ℚ) ^ 2)) := by
      exact prod_range_succ _ _
    rw [hrec, mul_comp, sub_comp, X_comp, C_comp, ih, symmetricFalling_succ]
    push_cast
    ring

theorem central_binomial_identity (l : ℕ) :
    C 2 * (centralPolynomial (l + 1)).comp (X ^ 2) =
      (binomialPolynomial (2 * (l + 1))).comp (X + C ((l + 1 : ℕ) : ℚ)) +
      (binomialPolynomial (2 * (l + 1))).comp (X + C (l : ℚ)) := by
  have hindex : 2 * (l + 1) = (2 * l + 1) + 1 := by omega
  have hleft : (descPochhammer ℚ (2 * (l + 1))).comp
      (X + C ((l + 1 : ℕ) : ℚ)) =
      (X + C ((l + 1 : ℕ) : ℚ)) * symmetricFalling l := by
    rw [hindex, descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
    congr 1
    have he : (X - 1 : ℚ[X]).comp (X + C ((l + 1 : ℕ) : ℚ)) = X + C (l : ℚ) := by
      simp only [sub_comp, X_comp, one_comp, Nat.cast_add, Nat.cast_one, C_add, C_1]
      ring
    rw [he]
    rfl
  have hright : (descPochhammer ℚ (2 * (l + 1))).comp (X + C (l : ℚ)) =
      symmetricFalling l * (X - C ((l + 1 : ℕ) : ℚ)) := by
    rw [hindex, descPochhammer_succ_right, mul_comp]
    simp only [sub_comp, X_comp, natCast_comp]
    change symmetricFalling l * (X + C (l : ℚ) - ((2 * l + 1 : ℕ) : ℚ[X])) = _
    congr 1
    push_cast
    simp only [C_add, C_1]
    rw [C_eq_natCast]
    ring
  simp only [centralPolynomial, binomialPolynomial, mul_comp, C_comp]
  rw [rootPolynomial_square_symmetric, hleft, hright]
  norm_num only [map_ofNat]
  ring

theorem centralPolynomial_twice_eval_square_int (l : ℕ) (k : ℤ) :
    2 * (centralPolynomial (l + 1)).eval ((k : ℚ) ^ 2) =
      ((Ring.choose (k + (l + 1)) (2 * (l + 1)) +
        Ring.choose (k + l) (2 * (l + 1)) : ℤ) : ℚ) := by
  have h := congr_arg (Polynomial.eval (k : ℚ)) (central_binomial_identity l)
  simp only [eval_mul, eval_C, eval_comp, eval_pow, eval_X, eval_add] at h
  have h1 : (k : ℚ) + ((l + 1 : ℕ) : ℚ) = ((k + (l + 1) : ℤ) : ℚ) := by push_cast; ring
  have h2 : (k : ℚ) + (l : ℚ) = ((k + l : ℤ) : ℚ) := by push_cast; rfl
  rw [h1, h2, binomialPolynomial_eval_int, binomialPolynomial_eval_int] at h
  simpa only [Int.cast_add] using h

def centralStar (j : ℕ) : ℚ[X] :=
  if j = 0 then 1 else C 2 * centralPolynomial j

theorem centralStar_natDegree (j : ℕ) : (centralStar j).natDegree = j := by
  by_cases hj : j = 0
  · simp [centralStar, hj]
  · simp [centralStar, hj, natDegree_C_mul, centralPolynomial_natDegree]

theorem centralStar_eval_square_zero {i j : ℕ} (hij : i < j) :
    (centralStar j).eval ((i : ℚ) ^ 2) = 0 := by
  have hj : j ≠ 0 := by omega
  simp [centralStar, hj, centralPolynomial_eval_square_eq_zero hij]

theorem centralStar_eval_square_self (j : ℕ) :
    (centralStar j).eval ((j : ℚ) ^ 2) = 1 := by
  cases j with
  | zero => simp [centralStar]
  | succ l =>
    have h := congr_arg (Polynomial.eval ((l + 1 : ℕ) : ℚ)) (central_binomial_identity l)
    simp only [eval_mul, eval_C, eval_comp, eval_pow, eval_X, eval_add] at h
    have h1 : ((l + 1 : ℕ) : ℚ) + ((l + 1 : ℕ) : ℚ) = ((2 * (l + 1) : ℕ) : ℚ) := by
      push_cast
      ring
    have h2 : ((l + 1 : ℕ) : ℚ) + (l : ℚ) = ((2 * l + 1 : ℕ) : ℚ) := by
      push_cast
      ring
    rw [h1, h2, binomialPolynomial_eval_nat, binomialPolynomial_eval_nat,
      Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : 2 * l + 1 < 2 * (l + 1))] at h
    simpa [centralStar] using h

def SquareValuedLower (p : ℕ) (w : ℤ) (g : ℚ[X]) : Prop :=
  ∀ k : ℤ, PadicLower p w (g.eval ((k : ℚ) ^ 2))

variable {p : ℕ} [Fact p.Prime]

theorem centralStar_squareIntegral (j : ℕ) : SquareValuedLower p 0 (centralStar j) := by
  intro k
  cases j with
  | zero => simpa [centralStar] using padicLower_nat (p := p) 1
  | succ l =>
    simp only [centralStar, Nat.succ_ne_zero, ↓reduceIte, eval_mul, eval_C]
    rw [centralPolynomial_twice_eval_square_int]
    exact padicLower_int _

def centralCoefficient (g : ℚ[X]) (n : ℕ) : ℚ :=
  g.eval ((n : ℚ) ^ 2) -
    ∑ a : Fin n, centralCoefficient g a * (centralStar a).eval ((n : ℚ) ^ 2)
termination_by n

theorem centralCoefficient_eq (g : ℚ[X]) (n : ℕ) :
    centralCoefficient g n = g.eval ((n : ℚ) ^ 2) -
      ∑ a ∈ range n, centralCoefficient g a * (centralStar a).eval ((n : ℚ) ^ 2) := by
  rw [centralCoefficient]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun a => centralCoefficient g a * (centralStar a).eval ((n : ℚ) ^ 2)) n

def centralExpansion (g : ℚ[X]) (L : ℕ) : ℚ[X] :=
  ∑ a ∈ range (L + 1), C (centralCoefficient g a) * centralStar a

theorem centralExpansion_natDegree_le (g : ℚ[X]) (L : ℕ) :
    (centralExpansion g L).natDegree ≤ L := by
  apply natDegree_sum_le_of_forall_le
  intro a ha
  exact (natDegree_C_mul_le _ _).trans
    ((centralStar_natDegree a).le.trans (by simpa using mem_range.mp ha))

theorem centralExpansion_eval_square (g : ℚ[X]) {n L : ℕ} (hn : n ≤ L) :
    (centralExpansion g L).eval ((n : ℚ) ^ 2) = g.eval ((n : ℚ) ^ 2) := by
  rw [centralExpansion, eval_finsetSum]
  simp only [eval_mul, eval_C]
  have he : (∑ a ∈ range (L + 1), centralCoefficient g a * (centralStar a).eval ((n : ℚ) ^ 2)) =
      ∑ a ∈ range (n + 1), centralCoefficient g a * (centralStar a).eval ((n : ℚ) ^ 2) := by
    symm
    apply sum_subset (range_mono (Nat.succ_le_succ hn))
    intro a ha hna
    have hna' : n < a := by simp only [mem_range] at hna; omega
    rw [centralStar_eval_square_zero hna', mul_zero]
  rw [he, sum_range_succ, centralStar_eval_square_self, mul_one, centralCoefficient_eq]
  ring

theorem centralExpansion_eq (g : ℚ[X]) {L : ℕ} (hL : g.natDegree ≤ L) :
    centralExpansion g L = g := by
  refine eq_of_natDegree_lt_card_of_eval_eq (f := fun n : Fin (L + 1) => (n : ℚ) ^ 2)
    _ _ (fun a b h => ?_) ?_ ?_
  ·
    apply Fin.ext
    have ha : (0 : ℚ) ≤ (a : ℕ) := Nat.cast_nonneg _
    have hb : (0 : ℚ) ≤ (b : ℕ) := Nat.cast_nonneg _
    have he : (a : ℚ) = (b : ℚ) := by nlinarith
    exact Nat.cast_injective he
  · intro n
    exact centralExpansion_eval_square g (Nat.le_of_lt_succ n.isLt)
  · simpa using And.intro (Nat.lt_succ_of_le (centralExpansion_natDegree_le g L))
      (Nat.lt_succ_of_le hL)

theorem centralCoefficient_padicLower {g : ℚ[X]} {w : ℤ}
    (hg : SquareValuedLower p w g) (n : ℕ) : PadicLower p w (centralCoefficient g n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [centralCoefficient_eq, sub_eq_add_neg]
    have hn : PadicLower p w (g.eval ((n : ℚ) ^ 2)) := by simpa using hg (n : ℤ)
    apply hn.add
    apply PadicLower.neg
    apply padicLower_sum
    intro a ha
    have hb : PadicLower p 0 ((centralStar a).eval ((n : ℚ) ^ 2)) := by
      simpa using centralStar_squareIntegral (p := p) a (n : ℤ)
    simpa using (ih a (mem_range.mp ha)).mul hb

def centralBasisCoefficient (g : ℚ[X]) (n : ℕ) : ℚ :=
  centralCoefficient g n * (if n = 0 then 1 else 2)

theorem centralBasis_expansion (g : ℚ[X]) {L : ℕ} (hL : g.natDegree ≤ L) :
    g = ∑ a ∈ range (L + 1), C (centralBasisCoefficient g a) * centralPolynomial a := by
  calc
    g = centralExpansion g L := (centralExpansion_eq g hL).symm
    _ = _ := ?_
  unfold centralExpansion
  apply sum_congr rfl
  intro a ha
  by_cases ha0 : a = 0
  · subst a
    simp [centralStar, centralBasisCoefficient, centralPolynomial, rootPolynomial]
  · simp only [centralBasisCoefficient, centralStar, ha0, ↓reduceIte, map_mul]
    ring

theorem centralBasisCoefficient_padicLower {g : ℚ[X]} {w : ℤ}
    (hg : SquareValuedLower p w g) (n : ℕ) : PadicLower p w (centralBasisCoefficient g n) := by
  unfold centralBasisCoefficient
  have hc : PadicLower p 0 (if n = 0 then (1 : ℚ) else 2) := by
    split_ifs
    · exact padicLower_nat 1
    · exact padicLower_nat 2
  simpa using (centralCoefficient_padicLower hg n).mul hc

theorem centralPolynomial_square_padicLower (j : ℕ) :
    SquareValuedLower p (-(padicValNat p 2 : ℤ)) (centralPolynomial j) := by
  intro k
  cases j with
  | zero =>
    have h := padicLower_nat (p := p) 1
    simpa [centralPolynomial, rootPolynomial] using h.mono
      (neg_nonpos.mpr (Int.natCast_nonneg (padicValNat p 2)))
  | succ l =>
    have h2 : PadicLower p (-(padicValNat p 2 : ℤ)) ((2 : ℚ)⁻¹) := by
      right
      rw [padicValRat.inv]
      change -(padicValNat p (2 : ℕ) : ℤ) ≤ -padicValRat p ((2 : ℕ) : ℚ)
      rw [padicValRat.of_nat]
    have hi : PadicLower p 0 (2 * (centralPolynomial (l + 1)).eval ((k : ℚ) ^ 2)) := by
      rw [centralPolynomial_twice_eval_square_int]
      exact padicLower_int _
    have h := h2.mul hi
    simpa only [← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℚ) ≠ 0), one_mul, add_zero] using h

theorem centralProduct_square_padicLower (j k : ℕ) :
    SquareValuedLower p (-2 * (padicValNat p 2 : ℤ)) (centralPolynomial j * centralPolynomial k) := by
  intro c
  rw [eval_mul]
  have h := (centralPolynomial_square_padicLower (p := p) j c).mul
    (centralPolynomial_square_padicLower (p := p) k c)
  convert h using 1 <;> ring

/-- The exact product expansion, with only a possible two-adic loss. -/
theorem centralProduct_expansion (j k : ℕ) :
    ∃ d : ℕ → ℚ,
      (∀ a, PadicLower p (-2 * (padicValNat p 2 : ℤ)) (d a)) ∧
      centralPolynomial j * centralPolynomial k =
        ∑ a ∈ range (j + k + 1), C (d a) * centralPolynomial a := by
  refine ⟨centralBasisCoefficient (centralPolynomial j * centralPolynomial k),
    centralBasisCoefficient_padicLower (centralProduct_square_padicLower j k), ?_⟩
  apply centralBasis_expansion
  simpa [centralPolynomial_natDegree] using
    (natDegree_mul_le (p := centralPolynomial j) (q := centralPolynomial k))

theorem padicValNat_two_eq_zero (hp2 : p ≠ 2) : padicValNat p 2 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hp2 h

theorem centralProduct_expansion_odd (hp2 : p ≠ 2) (j k : ℕ) :
    ∃ d : ℕ → ℚ, (∀ a, PadicLower p 0 (d a)) ∧
      centralPolynomial j * centralPolynomial k =
        ∑ a ∈ range (j + k + 1), C (d a) * centralPolynomial a := by
  simpa [padicValNat_two_eq_zero hp2] using centralProduct_expansion (p := p) j k

theorem centralPolynomial_square_integerValuedAt (hp2 : p ≠ 2) (j : ℕ) :
    IntegerValuedAt p ((centralPolynomial j).comp (X ^ 2)) := by
  intro k
  simpa [eval_comp, padicValNat_two_eq_zero hp2] using
    centralPolynomial_square_padicLower (p := p) j k

theorem centralPolynomial_local_integral (hp2 : p ≠ 2) {j : ℕ}
    (hj : 2 * j < p ^ 2) (c : ℤ) :
    PolynomialPadicLower p 0
      (((centralPolynomial j).comp (X ^ 2)).comp (localAffine p c)) := by
  apply integerValuedAt_local_integral (centralPolynomial_square_integerValuedAt hp2 j) _ hj c
  simp [natDegree_comp, centralPolynomial_natDegree, Nat.mul_comm]

theorem centralPolynomial_local_high_coeff (hp2 : p ≠ 2) {j k : ℕ}
    (hj : 2 * j < p ^ 2) (hk : (2 * j) / p < k) (c : ℤ) :
    PadicLower p 1
      ((((centralPolynomial j).comp (X ^ 2)).comp (localAffine p c)).coeff k) := by
  apply integerValuedAt_local_high_coeff
    (centralPolynomial_square_integerValuedAt hp2 j) _ hj hk c
  simp [natDegree_comp, centralPolynomial_natDegree, Nat.mul_comm]

end Zeta5.Arithmetic
