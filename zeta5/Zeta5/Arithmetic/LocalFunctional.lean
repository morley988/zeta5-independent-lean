import Zeta5.Arithmetic.LocalRestriction
import Zeta5.Arithmetic.ReflectedPartition

/-!
# The local bound for the complete fixed-denominator functional

This module combines the genuine central quotient with the retained
central truncation and the physical residue terms. The same coefficient
restriction controls every contribution to the bilinear form.
-/

noncomputable section
namespace Zeta5.Arithmetic
open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {p : ℕ} [Fact p.Prime]

theorem prime_power_padicLower (n : ℕ) : PadicLower p (n : ℤ) ((p : ℚ) ^ n) := by
  right
  simp [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]

theorem polynomialPadicLower_divByMonic_nonpos {P U : ℚ[X]} {n : ℕ}
    (hP : PolynomialPadicLower p (-(n : ℤ)) P)
    (hU : PolynomialPadicLower p 0 U) (hmonic : U.Monic) :
    PolynomialPadicLower p (-(n : ℤ)) (P / U) := by
  have hscaled : PolynomialPadicLower p 0 (C ((p : ℚ) ^ n) * P) := by
    simpa using (PolynomialPadicLower.constant (prime_power_padicLower (p := p) n)).mul hP
  have hdiv := polynomialPadicLower_divByMonic hscaled hU hmonic
  rw [divByMonic_eq_div _ hmonic] at hdiv
  have he : (C ((p : ℚ) ^ n) * P) / U = C ((p : ℚ) ^ n) * (P / U) := by
    simpa only [monicQuotientMap_apply, smul_eq_C_mul] using
      (monicQuotientMap U hmonic).map_smul ((p : ℚ) ^ n) P
  rw [he] at hdiv
  have h := (PolynomialPadicLower.constant (inverse_prime_power_padicLower (p := p) n)).mul hdiv
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simpa only [add_zero, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero n hp0), C_1, one_mul] using h

theorem polynomialMoment_weighted_lower {P : ℚ[X]} {w : ℤ} (hp : 5 < p)
    (hP : PolynomialPadicLower p w P) : PadicLower p (w - 1) (polynomialMoment P) := by
  unfold polynomialMoment
  rw [Polynomial.sum_def]
  apply padicLower_sum
  intro k hk
  simpa only [sub_eq_add_neg] using (hP k).mul (rationalMoment_padicLower (p := p) k hp)

theorem rootPolynomial_integral (j : ℕ) : PolynomialPadicLower p 0 (rootPolynomial j) := by
  have h := PolynomialPadicLower.prod (p := p) (range j)
    (fun a => (X - C ((a : ℚ) ^ 2))) (fun _ => 0) (by
      intro a ha
      have ha' : PadicLower p 0 ((a : ℚ) ^ 2) := by
        simpa only [pow_two, zero_add] using (padicLower_nat (p := p) a).mul (padicLower_nat (p := p) a)
      simpa only [sub_eq_add_neg] using
        polynomialPadicLower_X.add (PolynomialPadicLower.constant ha').neg)
  simpa only [rootPolynomial, sum_const_zero] using h

theorem normalized_centralStar_integral_bound {N a : ℕ} (ha : a ≤ N) (hsmall : 2 * N < p ^ 2) :
    PolynomialPadicLower p (-((2 * (N % p) / p : ℕ) : ℤ))
      (C ((N.factorial : ℚ) ^ 2) * centralStar a) := by
  have hp := (Fact.out : p.Prime).pos
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  by_cases ha0 : a = 0
  · subst a
    rw [show centralStar 0 = (1 : ℚ[X]) by simp [centralStar], mul_one]
    have hf : PadicLower p 0 ((N.factorial : ℚ) ^ 2) := by
      simpa only [pow_two, zero_add] using
        (padicLower_nat (p := p) N.factorial).mul (padicLower_nat (p := p) N.factorial)
    exact (PolynomialPadicLower.constant hf).mono (by omega)
  · have htwoa : 2 * a < p ^ 2 := by omega
    have hscalar := (factorial_square_padicLower (p := p) (N := N) (by omega)).mul
      (inverse_factorial_padicLower (p := p) htwoa)
    have hroot := (PolynomialPadicLower.constant hscalar).mul (rootPolynomial_integral (p := p) a)
    have htwo := (PolynomialPadicLower.constant (padicLower_nat (p := p) 2)).mul hroot
    have hfloor : 2 * N / p = 2 * (N / p) + 2 * (N % p) / p := by
      have hdecomp := Nat.mod_add_div N p
      conv_lhs => rw [← hdecomp]
      rw [mul_add, show 2 * (p * (N / p)) = p * (2 * (N / p)) by ring,
        Nat.add_mul_div_left _ _ hp]
      omega
    have hfloor' : ((2 * N / p : ℕ) : ℤ) =
        2 * ((N / p : ℕ) : ℤ) + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hfloor
    have hle : 2 * a / p ≤ 2 * N / p := Nat.div_le_div_right (by omega)
    have hle' : ((2 * a / p : ℕ) : ℤ) ≤ ((2 * N / p : ℕ) : ℤ) := by exact_mod_cast hle
    have hlower := htwo.mono (show -((2 * (N % p) / p : ℕ) : ℤ) ≤
        0 + (2 * ((N / p : ℕ) : ℤ) + -((2 * a / p : ℕ) : ℤ) + 0) by omega)
    convert hlower using 1 <;> simp only [centralStar, if_neg ha0, centralPolynomial, C_mul] <;> ring

theorem normalized_centralExpansion_integral_bound {N : ℕ} {g : ℚ[X]}
    (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2) :
    PolynomialPadicLower p (-((2 * (N % p) / p : ℕ) : ℤ))
      (C ((N.factorial : ℚ) ^ 2) * centralExpansion g N) := by
  rw [centralExpansion, mul_sum]
  apply PolynomialPadicLower.sum
  intro a ha
  have hc := centralCoefficient_padicLower hg a
  have h := (PolynomialPadicLower.constant hc).mul
    (normalized_centralStar_integral_bound (p := p) (show a ≤ N by simpa using mem_range.mp ha) hsmall)
  convert h using 1 <;> ring

theorem normalized_centralExpansion_quotient_moment_bound {N : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hg : SquareValuedLower p 0 g) (hsmall : 2 * N < p ^ 2) :
    PadicLower p (-1 - ((2 * (N % p) / p : ℕ) : ℤ))
      (polynomialMoment ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) /
        denominator N)) := by
  have hI := (normalized_centralExpansion_integral_bound hg hsmall).comp_integral
    (polynomialPadicLower_X (p := p)).neg
  rw [mul_comp, C_comp] at hI
  have hD : PolynomialPadicLower p 0 (denominator N) := by
    rw [← denominatorInt_map]
    exact polynomialPadicLower_integer_map _
  have h := polynomialMoment_weighted_lower hp
    (polynomialPadicLower_divByMonic_nonpos hI hD (denominator_monic N))
  convert h using 1 <;> omega

def normalizedResidue (N : ℕ) (g : ℚ[X]) (i : ℕ) : ℚ[X] :=
  C ((N.factorial : ℚ) ^ 2 * g.eval ((i : ℚ) ^ 2) /
    (denominator N).derivative.eval (pole i)) * stieltjes i

theorem normalizedResidue_bound {N i : ℕ} {g : ℚ[X]} {w v z : ℤ}
    (hN : N < p ^ 2) (hg : PadicLower p w (g.eval ((i : ℚ) ^ 2)))
    (hden : padicValRat p ((denominator N).derivative.eval (pole i)) ≤ v)
    (hk : PolynomialPadicLower p z (stieltjes i)) :
    PolynomialPadicLower p (2 * ((N / p : ℕ) : ℤ) + w - v + z) (normalizedResidue N g i) := by
  have hinv : PadicLower p (-v) (((denominator N).derivative.eval (pole i))⁻¹) := by
    right
    rw [padicValRat.inv]
    omega
  have hs := ((factorial_square_padicLower hN).mul hg).mul hinv
  simpa only [normalizedResidue, div_eq_mul_inv, sub_eq_add_neg] using
    (PolynomialPadicLower.constant hs).mul hk

theorem normalizedResidue_reflected_bound {N c i : ℕ} {g : ℚ[X]} {w : ℤ}
    (hp : 5 < p) (hc : 0 < c) (hcp : 2 * c < p)
    (hi : i ∈ reflectedNodes N p c) (hsmall : 2 * N < p ^ 2)
    (hg : PadicLower p w (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p (w + 2 * ((N / p : ℕ) : ℤ) - reflectedSize N p c - 4)
      (normalizedResidue N g i) := by
  obtain ⟨hi0, hiN, _⟩ := mem_reflectedNodes.mp hi
  have hd := denominator_derivative_reflected_valuation N c i (by omega) hc hcp hi (by omega)
  have h := normalizedResidue_bound (by omega : N < p ^ 2) hg hd.le
    (stieltjes_polynomial_padicLower i hp hi0 (by omega))
  convert h using 1 <;> omega

theorem denominator_derivative_zero_class_bound {N i : ℕ} (hp : 2 < p)
    (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i) (hsmall : 2 * N < p ^ 2) :
    padicValRat p ((denominator N).derivative.eval (pole i)) ≤ 2 * ((N / p : ℕ) : ℤ) - 2 := by
  have hp0 : 0 < p := by omega
  have hv : 1 ≤ (padicValNat p i : ℤ) := by
    have h := padicLower_nat_of_dvd (p := p) i hpi
    have hiQ : (i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hi)
    simpa only [padicValRat.of_nat] using h.of_ne_zero hiQ
  have hf := reflected_floor_sum N i p hp0 hiN
  rw [Nat.mod_eq_zero_of_dvd hpi] at hf
  simp only [reflectedSize, Nat.zero_le, if_true, Nat.sub_zero,
    if_neg (not_le_of_gt (Nat.mod_lt N hp0)), Nat.add_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hf
  rw [denominator_derivative_valuation N i hp hi hiN (by omega)]
  omega

theorem normalizedResidue_zero_class_integral {N i : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hi : 0 < i) (hiN : i ≤ N) (hpi : p ∣ i)
    (hsmall : 2 * N < p ^ 2) (hg : PadicLower p 0 (g.eval ((i : ℚ) ^ 2))) :
    PolynomialPadicLower p 0 (normalizedResidue N g i) := by
  have h := normalizedResidue_bound (by omega : N < p ^ 2) hg
    (denominator_derivative_zero_class_bound (by omega) hi hiN hpi hsmall)
    (stieltjes_polynomial_multiple_p i hp hi (by omega) hpi)
  exact h.mono (by omega)

theorem square_local_eval_at_reflected {N c i : ℕ} {g : ℚ[X]} {w : ℤ}
    (hc : 0 < c) (hcp : 2 * c < p) (hi : i ∈ reflectedNodes N p c)
    (hg : PolynomialPadicLower p w (g.comp ((localAffine p c) ^ 2))) :
    PadicLower p w (g.eval ((i : ℚ) ^ 2)) := by
  obtain ⟨hi0, hiN, himod⟩ := mem_reflectedNodes.mp hi
  have hs : i - 1 + 1 = i := by omega
  have hnode (b : Bool)
      (hb : if b then i % p = c else i % p = p - c) :
      (⟨i - 1, by omega⟩, b) ∈ divisibleRootIndices p (c : ℤ) Finset.univ (@signedPhysicalRoot N) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    apply (divisible_signedPhysicalRoot_iff hc (by omega) _).mpr
    simpa only [hs] using hb
  rcases himod with himod | himod
  · have hn := hnode true himod
    have h := hg.eval_integral (padicLower_int (physicalLocalLevel p c ((⟨i - 1, by omega⟩ : Fin N), true)))
    simp only [eval_comp, eval_pow, localAffine, eval_add, eval_C, eval_mul, eval_X] at h
    rw [physicalLocalLevel_reconstruct hn] at h
    simpa only [signedPhysicalRoot, ↓reduceIte, hs, Int.cast_natCast] using h
  · have hn := hnode false himod
    have h := hg.eval_integral (padicLower_int (physicalLocalLevel p c ((⟨i - 1, by omega⟩ : Fin N), false)))
    simp only [eval_comp, eval_pow, localAffine, eval_add, eval_C, eval_mul, eval_X] at h
    rw [physicalLocalLevel_reconstruct hn] at h
    simpa only [signedPhysicalRoot, Bool.false_eq_true, ↓reduceIte, hs,
      Int.cast_neg, neg_sq, Int.cast_natCast] using h

theorem normalizedResidue_global_bound {N i : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hi : 0 < i) (hiN : i ≤ N) (hsmall : 2 * N < p ^ 2)
    (hg : SquareValuedLower p 0 g) :
    PolynomialPadicLower p (-5 - ((2 * (N % p) / p : ℕ) : ℤ)) (normalizedResidue N g i) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
    simpa only [Int.cast_natCast] using hg (i : ℤ)
  by_cases hpi : p ∣ i
  · exact (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hgi).mono (by omega)
  · let c := reflectedLabel p i
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
    have hc : 0 < c := Nat.pos_of_ne_zero ((reflectedLabel_eq_zero p i (by omega)).not.mpr hpi)
    have hchalf : c ≤ (p - 1) / 2 := reflectedLabel_le_half p i (by omega) hodd
    have hcp : 2 * c < p := by omega
    have himem : i ∈ reflectedNodes N p c :=
      mem_reflectedNodes.mpr ⟨hi, hiN, (reflectedLabel_eq_iff p i c (by omega) hc hcp).mp rfl⟩
    have hsize := reflectedSize_le_max N p c hodd hc hchalf
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgi).mono (by omega)

theorem normalizedResidue_global_bound_on_kernel {N i : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hi : 0 < i) (hiN : i ≤ N) (hsmall : 2 * N < p ^ 2)
    (hg : SquareValuedLower p 0 g)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p (-4 - ((2 * (N % p) / p : ℕ) : ℤ)) (normalizedResidue N g i) := by
  have heps : 0 ≤ ((2 * (N % p) / p : ℕ) : ℤ) := Int.natCast_nonneg _
  have hgi : PadicLower p 0 (g.eval ((i : ℚ) ^ 2)) := by
    simpa only [Int.cast_natCast] using hg (i : ℤ)
  by_cases hpi : p ∣ i
  · exact (normalizedResidue_zero_class_integral hp hi hiN hpi hsmall hgi).mono (by omega)
  · let c := reflectedLabel p i
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr (by omega : p ≠ 2)
    have hc : 0 < c := Nat.pos_of_ne_zero ((reflectedLabel_eq_zero p i (by omega)).not.mpr hpi)
    have hchalf : c ≤ (p - 1) / 2 := reflectedLabel_le_half p i (by omega) hodd
    have hcp : 2 * c < p := by omega
    have himem : i ∈ reflectedNodes N p c :=
      mem_reflectedNodes.mpr ⟨hi, hiN, (reflectedLabel_eq_iff p i c (by omega) hc hcp).mp rfl⟩
    have hsize := reflectedSize_le_max N p c hodd hc hchalf
    have hsize' : (reflectedSize N p c : ℤ) ≤
        2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hsize
    by_cases hmax : c ∈ maximalReflectedClasses N p
    · have hgain := square_local_eval_at_reflected hc hcp himem (hkernel c hmax)
      exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgain).mono (by omega)
    · have hne : reflectedSize N p c ≠ 2 * (N / p) + 1 + 2 * (N % p) / p := by
        intro he
        exact hmax (mem_filter.mpr ⟨mem_Icc.mpr ⟨hc, hchalf⟩, he⟩)
      have hne' : (reflectedSize N p c : ℤ) ≠
          2 * ((N / p : ℕ) : ℤ) + 1 + ((2 * (N % p) / p : ℕ) : ℤ) := by exact_mod_cast hne
      exact (normalizedResidue_reflected_bound hp hc hcp himem hsmall hgi).mono (by omega)

def normalizedCentralFunctional (N : ℕ) (g : ℚ[X]) : ℚ[X] :=
  numeratorFunctional N (C ((N.factorial : ℚ) ^ 2) * g.comp (-X))

theorem normalizedCentralFunctional_eq (N : ℕ) (g : ℚ[X]) :
    normalizedCentralFunctional N g =
      C ((N.factorial : ℚ) ^ 2) * numeratorFunctional N (g.comp (-X)) := by
  simpa only [normalizedCentralFunctional, smul_eq_C_mul] using
    (numeratorFunctional N).map_smul ((N.factorial : ℚ) ^ 2) (g.comp (-X))

theorem normalizedCentralFunctional_decomposition (N : ℕ) (g : ℚ[X]) :
    normalizedCentralFunctional N g =
      C (polynomialMoment (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)) +
      C (polynomialMoment ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) /
        denominator N)) + ∑ i ∈ range N, normalizedResidue N g (i + 1) := by
  have hsplit : C ((N.factorial : ℚ) ^ 2) * g.comp (-X) =
      C ((N.factorial : ℚ) ^ 2) * centralTail N g +
      C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X) := by
    rw [centralTail, sub_comp]
    ring
  have hq : (C ((N.factorial : ℚ) ^ 2) * g.comp (-X)) / denominator N =
      C ((N.factorial : ℚ) ^ 2) * centralQuotient N g +
      (C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N := by
    have hadd := (monicQuotientMap (denominator N) (denominator_monic N)).map_add
      (C ((N.factorial : ℚ) ^ 2) * centralTail N g)
      (C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X))
    simp only [monicQuotientMap_apply] at hadd
    rw [hsplit, hadd, centralTail_eq_denominator_mul_quotient]
    have hm : C ((N.factorial : ℚ) ^ 2) * (denominator N * centralQuotient N g) =
        (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g) * denominator N := by ring
    rw [hm, mul_div_cancel_right₀ _ (denominator_ne_zero N)]
  rw [normalizedCentralFunctional, numeratorFunctional_apply, hq]
  have hmoment := polynomialMomentMap.map_add
    (C ((N.factorial : ℚ) ^ 2) * centralQuotient N g)
    ((C ((N.factorial : ℚ) ^ 2) * (centralExpansion g N).comp (-X)) / denominator N)
  simp only [polynomialMomentMap_apply] at hmoment
  rw [hmoment, C_add]
  congr 1
  apply sum_congr rfl
  intro i hi
  simp only [normalizedResidue, eval_mul, eval_C, eval_comp, eval_neg, eval_X, pole, neg_neg]

theorem normalizedCentralFunctional_padicLower {N : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 6 < p ^ 2) :
    PolynomialPadicLower p (-5 - ((2 * (N % p) / p : ℕ) : ℤ))
      (normalizedCentralFunctional N g) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  rw [normalizedCentralFunctional_decomposition]
  apply PolynomialPadicLower.add
  · apply PolynomialPadicLower.add
    · exact PolynomialPadicLower.constant (centralQuotient_moment_bound hp hg hsmall)
    · exact (PolynomialPadicLower.constant
        (normalized_centralExpansion_quotient_moment_bound hp hg (by omega))).mono (by omega)
  · apply PolynomialPadicLower.sum
    intro i hi
    exact normalizedResidue_global_bound hp (by omega) (by simpa using mem_range.mp hi) (by omega) hg

theorem normalizedCentralFunctional_padicLower_on_kernel {N : ℕ} {g : ℚ[X]}
    (hp : 5 < p) (hg : SquareValuedLower p 0 g)
    (hsmall : 2 * max g.natDegree N + 6 < p ^ 2)
    (hkernel : ∀ c ∈ maximalReflectedClasses N p,
      PolynomialPadicLower p 1 (g.comp ((localAffine p c) ^ 2))) :
    PolynomialPadicLower p (-4 - ((2 * (N % p) / p : ℕ) : ℤ))
      (normalizedCentralFunctional N g) := by
  have hmax : N ≤ max g.natDegree N := le_max_right _ _
  rw [normalizedCentralFunctional_decomposition]
  apply PolynomialPadicLower.add
  · apply PolynomialPadicLower.add
    · exact PolynomialPadicLower.constant (centralQuotient_moment_bound_on_kernel hp hg hsmall hkernel)
    · exact (PolynomialPadicLower.constant
        (normalized_centralExpansion_quotient_moment_bound hp hg (by omega))).mono (by omega)
  · apply PolynomialPadicLower.sum
    intro i hi
    exact normalizedResidue_global_bound_on_kernel hp (by omega)
      (by simpa using mem_range.mp hi) (by omega) hg hkernel

end Zeta5.Arithmetic
