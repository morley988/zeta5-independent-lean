import Zeta5.Arithmetic.LocalDivision
import Zeta5.Arithmetic.LocalNewton
import Zeta5.Arithmetic.ReflectedClasses

/-!
# Exact local denominator factors

Each linear factor whose constant term is divisible by `p` contributes
one explicit factor of `p` and a monic integral factor.  All remaining
factors have unit constant terms.  The construction is first given for
arbitrary finite indexed integer roots and then applied to `D_N(-x²)`.
-/

noncomputable section
namespace Zeta5.Arithmetic

open Polynomial Finset OddZeta.FourValue Zeta5.Construction

variable {ι : Type*} [DecidableEq ι]

def localLinearFactor (p : ℕ) (c r : ℤ) : ℚ[X] := localAffine p c - C (r : ℚ)

def divisibleRootIndices (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) : Finset ι :=
  s.filter fun i => (p : ℤ) ∣ c - r i

def localMonicFactor (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) : ℚ[X] :=
  ∏ i ∈ divisibleRootIndices p c s r, (X + C (((c - r i) / p : ℤ) : ℚ))

def localUnitFactor (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) : ℚ[X] :=
  ∏ i ∈ s.filter (fun i => ¬(p : ℤ) ∣ c - r i), localLinearFactor p c (r i)

theorem localLinearFactor_extract {p : ℕ} {c r : ℤ} (h : (p : ℤ) ∣ c - r) :
    localLinearFactor p c r = C (p : ℚ) * (X + C (((c - r) / p : ℤ) : ℚ)) := by
  have he : (p : ℚ) * (((c - r) / p : ℤ) : ℚ) = (c : ℚ) - (r : ℚ) := by
    exact_mod_cast Int.mul_ediv_cancel' h
  rw [mul_add, ← C_mul, he, C_sub]
  unfold localLinearFactor localAffine
  ring

theorem local_linear_product_factorization (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    (∏ i ∈ s, localLinearFactor p c (r i)) =
      C ((p : ℚ) ^ (divisibleRootIndices p c s r).card) *
        localMonicFactor p c s r * localUnitFactor p c s r := by
  rw [← prod_filter_mul_prod_filter_not s (fun i => (p : ℤ) ∣ c - r i)]
  have he : (∏ i ∈ s.filter (fun i => (p : ℤ) ∣ c - r i), localLinearFactor p c (r i)) =
      ∏ i ∈ divisibleRootIndices p c s r, C (p : ℚ) * (X + C (((c - r i) / p : ℤ) : ℚ)) := by
    apply prod_congr rfl
    intro i hi
    exact localLinearFactor_extract (mem_filter.mp hi).2
  rw [he, prod_mul_distrib, prod_const, ← map_pow]
  rfl

theorem localMonicFactor_monic (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    (localMonicFactor p c s r).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_add_C _

theorem localMonicFactor_natDegree (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    (localMonicFactor p c s r).natDegree = (divisibleRootIndices p c s r).card := by
  rw [localMonicFactor, natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
  · intro i hi
    exact monic_X_add_C _

theorem localUnitFactor_constant (p : ℕ) (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    (localUnitFactor p c s r).coeff 0 =
      ∏ i ∈ s.filter (fun i => ¬(p : ℤ) ∣ c - r i), ((c - r i : ℤ) : ℚ) := by
  rw [localUnitFactor, coeff_zero_prod]
  apply prod_congr rfl
  intro i hi
  simp [localLinearFactor, localAffine]

variable {p : ℕ} [Fact p.Prime]

theorem inverse_int_integral_of_not_dvd (z : ℤ) (hz : ¬(p : ℤ) ∣ z) :
    PadicLower p 0 ((z : ℚ)⁻¹) := by
  right
  simp [padicValRat.inv, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]

theorem localMonicFactor_integral (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    PolynomialPadicLower p 0 (localMonicFactor p c s r) := by
  have h := PolynomialPadicLower.prod (p := p) (divisibleRootIndices p c s r)
    (fun i => (X + C (((c - r i) / p : ℤ) : ℚ))) (fun _ => 0) (by
      intro i hi
      exact polynomialPadicLower_X.add (PolynomialPadicLower.constant (padicLower_int _)))
  simpa [localMonicFactor] using h

theorem localLinearFactor_integral (c r : ℤ) :
    PolynomialPadicLower p 0 (localLinearFactor p c r) := by
  unfold localLinearFactor
  rw [sub_eq_add_neg]
  exact (localAffine_integral c).add (PolynomialPadicLower.constant (padicLower_int r)).neg

theorem localUnitFactor_integral (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    PolynomialPadicLower p 0 (localUnitFactor p c s r) := by
  have h := PolynomialPadicLower.prod (p := p)
    (s.filter (fun i => ¬(p : ℤ) ∣ c - r i)) (fun i => localLinearFactor p c (r i))
    (fun _ => 0) (fun i _ => localLinearFactor_integral c (r i))
  simpa [localUnitFactor] using h

theorem localUnitFactor_constant_ne_zero (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    (localUnitFactor p c s r).coeff 0 ≠ 0 := by
  rw [localUnitFactor_constant]
  apply prod_ne_zero_iff.mpr
  intro i hi hz
  have hz' : c - r i = 0 := by exact_mod_cast hz
  exact (mem_filter.mp hi).2 (by rw [hz']; exact dvd_zero _)

theorem localUnitFactor_inverse_constant_integral (c : ℤ) (s : Finset ι) (r : ι → ℤ) :
    PadicLower p 0 (((localUnitFactor p c s r).coeff 0)⁻¹) := by
  rw [localUnitFactor_constant, ← prod_inv_distrib]
  have h := padicLower_prod (p := p) (s.filter (fun i => ¬(p : ℤ) ∣ c - r i))
    (fun i => (((c - r i : ℤ) : ℚ))⁻¹) (fun _ => 0)
    (fun i hi => inverse_int_integral_of_not_dvd _ (mem_filter.mp hi).2)
  simpa using h

def signedPhysicalRoot {N : ℕ} (i : Fin N × Bool) : ℤ :=
  if i.2 then (i.1.val + 1 : ℕ) else -((i.1.val + 1 : ℕ) : ℤ)

theorem denominator_local_signed_product (N : ℕ) (c : ℤ) :
    (denominator N).comp (-(localAffine p c) ^ 2) =
      C ((-1 : ℚ) ^ N) * ∏ i : Fin N × Bool, localLinearFactor p c (signedPhysicalRoot i) := by
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, signedPhysicalRoot, ↓reduceIte,
    Bool.false_eq_true, Int.cast_neg, Int.cast_natCast, C_neg, localLinearFactor, sub_neg_eq_add]
  rw [denominator, Polynomial.prod_comp, ← Fin.prod_univ_eq_prod_range]
  simp only [add_comp, X_comp, C_comp]
  have he : ∀ i : Fin N, (-(localAffine p c) ^ 2 + C (((i.val + 1 : ℕ) : ℚ) ^ 2)) =
      C (-1 : ℚ) * ((localAffine p c - C (((i.val + 1 : ℕ) : ℚ))) *
        (localAffine p c + C (((i.val + 1 : ℕ) : ℚ)))) := by
    intro i
    rw [C_pow]
    norm_num
    ring
  simp_rw [he]
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← map_pow]

def physicalLocalMonic (N : ℕ) (p : ℕ) (c : ℤ) : ℚ[X] :=
  localMonicFactor p c Finset.univ (@signedPhysicalRoot N)

def physicalLocalUnit (N : ℕ) (p : ℕ) (c : ℤ) : ℚ[X] :=
  C ((-1 : ℚ) ^ N) * localUnitFactor p c Finset.univ (@signedPhysicalRoot N)

def physicalLocalMultiplicity (N p : ℕ) (c : ℤ) : ℕ :=
  (divisibleRootIndices p c Finset.univ (@signedPhysicalRoot N)).card

theorem denominator_local_factorization (N : ℕ) (c : ℤ) :
    (denominator N).comp (-(localAffine p c) ^ 2) =
      C ((p : ℚ) ^ physicalLocalMultiplicity N p c) *
        physicalLocalMonic N p c * physicalLocalUnit N p c := by
  rw [denominator_local_signed_product, local_linear_product_factorization]
  unfold physicalLocalMultiplicity physicalLocalMonic physicalLocalUnit
  ring

theorem physicalLocalMonic_monic (N : ℕ) (c : ℤ) : (physicalLocalMonic N p c).Monic :=
  localMonicFactor_monic _ _ _ _

theorem physicalLocalMonic_integral (N : ℕ) (c : ℤ) :
    PolynomialPadicLower p 0 (physicalLocalMonic N p c) := localMonicFactor_integral _ _ _

theorem physicalLocalMonic_natDegree (N : ℕ) (c : ℤ) :
    (physicalLocalMonic N p c).natDegree = physicalLocalMultiplicity N p c :=
  localMonicFactor_natDegree _ _ _ _

theorem physicalLocalUnit_integral (N : ℕ) (c : ℤ) :
    PolynomialPadicLower p 0 (physicalLocalUnit N p c) := by
  have hs : PadicLower p 0 ((-1 : ℚ) ^ N) := by
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ N)
  simpa [physicalLocalUnit] using (PolynomialPadicLower.constant hs).mul
    (localUnitFactor_integral (p := p) c Finset.univ (@signedPhysicalRoot N))

theorem physicalLocalUnit_constant_ne_zero (N : ℕ) (c : ℤ) :
    (physicalLocalUnit N p c).coeff 0 ≠ 0 := by
  rw [physicalLocalUnit, coeff_C_mul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (localUnitFactor_constant_ne_zero _ _ _)

theorem physicalLocalUnit_inverse_constant_integral (N : ℕ) (c : ℤ) :
    PadicLower p 0 (((physicalLocalUnit N p c).coeff 0)⁻¹) := by
  rw [physicalLocalUnit, coeff_C_mul, mul_inv_rev]
  have hs : PadicLower p 0 (((-1 : ℚ) ^ N)⁻¹) := by
    rw [← inv_pow]
    norm_num only [inv_neg, inv_one]
    simpa using padicLower_int (p := p) ((-1 : ℤ) ^ N)
  simpa using (localUnitFactor_inverse_constant_integral (p := p) c Finset.univ
    (@signedPhysicalRoot N)).mul hs

theorem int_dvd_sub_nat_iff_mod_eq (i c p : ℕ) (hcp : c < p) :
    (p : ℤ) ∣ (c : ℤ) - (i : ℤ) ↔ i % p = c := by
  rw [← Int.modEq_iff_dvd]
  change (i : ℤ) % p = (c : ℤ) % p ↔ _
  rw [← Int.natCast_emod, ← Int.natCast_emod, Nat.mod_eq_of_lt hcp]
  exact_mod_cast (Iff.rfl : i % p = c ↔ i % p = c)

theorem int_dvd_add_nat_iff_mod_eq (i c p : ℕ) (hc : 0 < c) (hcp : c < p) :
    (p : ℤ) ∣ (c : ℤ) + (i : ℤ) ↔ i % p = p - c := by
  rw [← int_dvd_sub_nat_iff_mod_eq i (p - c) p (by omega)]
  rw [Nat.cast_sub hcp.le]
  constructor <;> intro h
  · have hd := dvd_sub (dvd_refl (p : ℤ)) h
    simpa only [sub_add_eq_sub_sub] using hd
  · have hd := dvd_sub (dvd_refl (p : ℤ)) h
    have he : (p : ℤ) - ((p : ℤ) - c - i) = (c : ℤ) + i := by ring
    rwa [he] at hd

theorem divisible_signedPhysicalRoot_iff {N p c : ℕ} (hc : 0 < c) (hcp : c < p)
    (i : Fin N × Bool) :
    (p : ℤ) ∣ (c : ℤ) - signedPhysicalRoot i ↔
      if i.2 then (i.1.val + 1) % p = c else (i.1.val + 1) % p = p - c := by
  rcases i with ⟨i, b⟩
  cases b
  · simpa only [signedPhysicalRoot, Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add] using
      int_dvd_add_nat_iff_mod_eq (i.val + 1) c p hc hcp
  · simpa only [signedPhysicalRoot, ↓reduceIte] using int_dvd_sub_nat_iff_mod_eq (i.val + 1) c p hcp

theorem physicalLocalMultiplicity_eq_reflectedSize (N p c : ℕ) (hc : 0 < c) (hcp : 2 * c < p) :
    physicalLocalMultiplicity N p c = reflectedSize N p c := by
  rw [← reflectedNodes_card N p c hc hcp]
  unfold physicalLocalMultiplicity
  apply card_bij (fun i _ => i.1.val + 1)
  · intro i hi
    have hdiv := (mem_filter.mp hi).2
    have hm := (divisible_signedPhysicalRoot_iff hc (by omega) i).mp hdiv
    apply mem_reflectedNodes.mpr
    refine ⟨by omega, by have := i.1.isLt; omega, ?_⟩
    cases hbi : i.2 <;> simp only [hbi, Bool.false_eq_true, ↓reduceIte] at hm
    · exact Or.inr hm
    · exact Or.inl hm
  · rintro ⟨i, bi⟩ hi ⟨j, bj⟩ hj he
    change i.val + 1 = j.val + 1 at he
    have hij : i = j := Fin.ext (by omega)
    subst j
    have hmi := (divisible_signedPhysicalRoot_iff hc (by omega) (i, bi)).mp (mem_filter.mp hi).2
    have hmj := (divisible_signedPhysicalRoot_iff hc (by omega) (i, bj)).mp (mem_filter.mp hj).2
    apply congr_arg (fun b : Bool => (i, b))
    cases bi <;> cases bj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hmi hmj ⊢ <;> omega
  · intro i hi
    obtain ⟨hi0, hiN, hm⟩ := mem_reflectedNodes.mp hi
    have his : i - 1 + 1 = i := by omega
    rcases hm with hm | hm
    · refine ⟨(⟨i - 1, by omega⟩, true), ?_, his⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      apply (divisible_signedPhysicalRoot_iff hc (by omega) _).mpr
      simpa only [↓reduceIte, his] using hm
    · refine ⟨(⟨i - 1, by omega⟩, false), ?_, his⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      apply (divisible_signedPhysicalRoot_iff hc (by omega) _).mpr
      simpa only [Bool.false_eq_true, ↓reduceIte, his] using hm

theorem divisible_signedPhysicalRoot_zero_iff {N p : ℕ} (i : Fin N × Bool) :
    (p : ℤ) ∣ (0 : ℤ) - signedPhysicalRoot i ↔ p ∣ i.1.val + 1 := by
  rcases i with ⟨i, b⟩
  cases b
  · change (p : ℤ) ∣ 0 - -((i.val + 1 : ℕ) : ℤ) ↔ p ∣ i.val + 1
    rw [zero_sub, neg_neg, Int.natCast_dvd_natCast]
  · change (p : ℤ) ∣ 0 - ((i.val + 1 : ℕ) : ℤ) ↔ p ∣ i.val + 1
    rw [zero_sub, Int.dvd_neg, Int.natCast_dvd_natCast]

theorem physicalLocalMultiplicity_zero (N p : ℕ) :
    physicalLocalMultiplicity N p 0 = 2 * (N / p) := by
  have hc : (divisibleRootIndices p 0 Finset.univ (@signedPhysicalRoot N)).card =
      (((Ioc 0 N).filter (fun i => p ∣ i)) ×ˢ (Finset.univ : Finset Bool)).card := by
    apply card_bij (fun i _ => (i.1.val + 1, i.2))
    · intro i hi
      apply mem_product.mpr
      refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by have := i.1.isLt; omega⟩, ?_⟩, mem_univ _⟩
      exact (divisible_signedPhysicalRoot_zero_iff i).mp (mem_filter.mp hi).2
    · rintro ⟨i, bi⟩ hi ⟨j, bj⟩ hj he
      change (i.val + 1, bi) = (j.val + 1, bj) at he
      have he1 : i.val + 1 = j.val + 1 := congr_arg Prod.fst he
      have he2 : bi = bj := congr_arg Prod.snd he
      exact Prod.ext (Fin.ext (Nat.add_right_cancel he1)) he2
    · rintro ⟨i, b⟩ hi
      obtain ⟨hi, _⟩ := mem_product.mp hi
      obtain ⟨hi, hd⟩ := mem_filter.mp hi
      obtain ⟨hi0, hiN⟩ := mem_Ioc.mp hi
      have his : i - 1 + 1 = i := by omega
      refine ⟨(⟨i - 1, by omega⟩, b), ?_, ?_⟩
      · apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        apply (divisible_signedPhysicalRoot_zero_iff _).mpr
        simpa only [his] using hd
      · exact Prod.ext his rfl
  rw [physicalLocalMultiplicity, hc, card_product, Nat.Ioc_filter_dvd_card_eq_div]
  simp [Nat.mul_comm]

end Zeta5.Arithmetic
