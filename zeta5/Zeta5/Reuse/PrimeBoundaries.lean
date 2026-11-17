import Zeta5.Reuse.PrimePiecewise

/-! # Exact finite endpoint strips and their negligible prime charge -/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise
open Filter Finset
open scoped Topology BigOperators

def endpointPrimeStrip (a : ℝ) (width N : ℕ) : Finset ℕ :=
  (Finset.Icc (⌊a * N⌋₊ - width) (⌊a * N⌋₊ + width + 1)).filter Nat.Prime

theorem endpointPrimeStrip_card_le (a : ℝ) (width N : ℕ) :
    (endpointPrimeStrip a width N).card ≤ 2 * width + 2 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Nat.card_Icc]
  omega

theorem mem_endpointPrimeStrip_of_abs_le {a : ℝ} (ha : 0 ≤ a)
    {width N p : ℕ} (hp : p.Prime) (hnear : |(p : ℝ) - a * N| ≤ width) :
    p ∈ endpointPrimeStrip a width N := by
  have hf := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg N))
  have hl := Nat.lt_floor_add_one (a * N)
  obtain ⟨hleft, hright⟩ := abs_le.mp hnear
  have hlo : ⌊a * N⌋₊ ≤ p + width := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith
  have hhi : p ≤ ⌊a * N⌋₊ + width + 1 := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hhi⟩, hp⟩

theorem endpointPrimeStrip_upper {a A : ℝ} (ha : 0 ≤ a) (haA : a ≤ A)
    {width N p : ℕ} (hN : 0 < N) (hp : p ∈ endpointPrimeStrip a width N) :
    (p : ℝ) ≤ (A + width + 2) * N := by
  have hmem := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp' : (p : ℝ) ≤ (⌊a * N⌋₊ : ℝ) + width + 1 := by exact_mod_cast hmem
  have hf := Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg N))
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : (0 : ℝ) ≤ width := Nat.cast_nonneg _
  have han := mul_le_mul_of_nonneg_right haA (Nat.cast_nonneg N)
  nlinarith

/-- A finite union of fixed-width strips has a uniform cardinality bound. -/
def exceptionalPrimes {ι : Type*} [Fintype ι] (a : ι → ℝ) (width N : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => endpointPrimeStrip (a i) width N)

theorem exceptionalPrimes_card_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (width N : ℕ) :
    (exceptionalPrimes a width N).card ≤ Fintype.card ι * (2 * width + 2) := by
  classical
  calc
    (exceptionalPrimes a width N).card ≤ ∑ i : ι, (endpointPrimeStrip (a i) width N).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, (2 * width + 2) :=
      Finset.sum_le_sum (fun i _ => endpointPrimeStrip_card_le (a i) width N)
    _ = _ := by simp

theorem exceptionalPrimes_upper {ι : Type*} [Fintype ι] {a : ι → ℝ} {A : ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) {width N p : ℕ}
    (hN : 0 < N) (hp : p ∈ exceptionalPrimes a width N) :
    (p : ℝ) ≤ (A + width + 2) * N := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  exact endpointPrimeStrip_upper (ha i) (haA i) hN hi

def primeSetCharge (S : Finset ℕ) (N : ℕ) : ℝ := (N : ℝ) * ∑ p ∈ S, Real.log p

theorem primeSetCharge_nonneg (S : Finset ℕ) (N : ℕ) : 0 ≤ primeSetCharge S N := by
  unfold primeSetCharge
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro p hp
  exact Real.log_natCast_nonneg p

theorem primeSetCharge_le {S : Finset ℕ} {N M : ℕ} {C : ℝ}
    (hS : ∀ p ∈ S, p.Prime) (hM : S.card ≤ M) (hCN : 1 ≤ C * N)
    (hpC : ∀ p ∈ S, (p : ℝ) ≤ C * N) :
    primeSetCharge S N ≤ (M : ℝ) * N * Real.log (C * N) := by
  have hlog : 0 ≤ Real.log (C * N) := Real.log_nonneg hCN
  have hsum : (∑ p ∈ S, Real.log p) ≤ (M : ℝ) * Real.log (C * N) := by
    calc
      (∑ p ∈ S, Real.log p) ≤ ∑ _p ∈ S, Real.log (C * N) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log (by exact_mod_cast (hS p hp).pos) (hpC p hp)
      _ = (S.card : ℝ) * Real.log (C * N) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hlog
  have hh := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa [primeSetCharge, mul_assoc, mul_left_comm] using hh

theorem exceptionalPrimeCharge_le {ι : Type*} [Fintype ι] {a : ι → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) {width N : ℕ}
    (hN : 0 < N) :
    primeSetCharge (exceptionalPrimes a width N) N ≤
      (Fintype.card ι * (2 * width + 2) : ℕ) * (N : ℝ) * Real.log ((A + width + 2) * N) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply primeSetCharge_le _ (exceptionalPrimes_card_le a width N) _ _
  · intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hi).2
  · have hw : (0 : ℝ) ≤ width := Nat.cast_nonneg _
    nlinarith
  · exact fun p hp => exceptionalPrimes_upper ha haA hN hp

/-- Even an O(N) charge at every exceptional prime is o(N²). -/
theorem exceptionalPrimeCharge_limit {ι : Type*} [Fintype ι] {a : ι → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (width : ℕ) :
    Tendsto (fun N => primeSetCharge (exceptionalPrimes a width N) N / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hC : 0 < A + width + 2 := by positivity
  have ht := (nat_log_linear_over_sq_limit (A + width + 2) hC).const_mul
    ((Fintype.card ι * (2 * width + 2) : ℕ) : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => div_nonneg
    (primeSetCharge_nonneg _ _) (sq_nonneg _))) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have h := div_le_div_of_nonneg_right (exceptionalPrimeCharge_le (width := width) hA ha haA hN)
    (sq_nonneg (N : ℝ))
  simpa only [mul_assoc, mul_div_assoc] using h

end Zeta5.Reuse.PrimePiecewise
