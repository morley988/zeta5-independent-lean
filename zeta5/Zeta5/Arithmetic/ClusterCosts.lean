import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reflected-class costs and the shared dimension inequality

These are the finite combinatorial inequalities used in the manuscript's
common-root gain proposition.  They do not assert the p-adic hypotheses:
the valuation of atom weights, the Vandermonde divisibility, and quotient
support must be supplied separately.
-/

namespace Zeta5.Arithmetic

/-- Upper cost for selecting `l` atoms from a class with `h` high nodes. -/
def clusterCost (h l : ℕ) : ℤ :=
  5 * (min l h : ℕ) + (l : ℤ) * ((h : ℤ) + 2 - l)

/-- The corresponding upper cost after the common-root gain. -/
def affectedClusterCost (h l : ℕ) : ℤ :=
  5 * (min l h : ℕ) + (l : ℤ) * ((h : ℤ) - l)

/-- Unaffected classes have maximum cost `7h`; every missing high atom
reduces this upper bound by at least one. -/
theorem clusterCost_le_with_deficit (h l : ℕ)
    (hh : 1 ≤ h) (hh4 : h ≤ 4) (hl : l ≤ h + 2) :
    clusterCost h l ≤ 7 * (h : ℤ) - (h - l : ℕ) := by
  interval_cases h <;> interval_cases l <;> norm_num [clusterCost] at *

/-- Affected classes have maximum cost `5h`, with the same deficit bound. -/
theorem affectedClusterCost_le_with_deficit (h l : ℕ)
    (hh : 1 ≤ h) (hh4 : h ≤ 4) (hl : l ≤ h + 1) :
    affectedClusterCost h l ≤ 5 * (h : ℤ) - (h - l : ℕ) := by
  interval_cases h <;> interval_cases l <;> norm_num [affectedClusterCost] at *

/-- Larger selections already have a nonpositive quadratic term. Thus
the same envelope is valid without an upper bound on the selected size. -/
theorem clusterCost_le_with_deficit_all (h l : ℕ) (hh : 1 ≤ h) (hh4 : h ≤ 4) :
    clusterCost h l ≤ 7 * (h : ℤ) - (h - l : ℕ) := by
  by_cases hl : l ≤ h + 2
  · exact clusterCost_le_with_deficit h l hh hh4 hl
  have hhl : h ≤ l := by omega
  rw [clusterCost, min_eq_right hhl, Nat.sub_eq_zero_of_le hhl, Nat.cast_zero, sub_zero]
  have hprod : (l : ℤ) * ((h : ℤ) + 2 - l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  omega

theorem affectedClusterCost_le_with_deficit_all (h l : ℕ)
    (hh : 1 ≤ h) (hh4 : h ≤ 4) :
    affectedClusterCost h l ≤ 5 * (h : ℤ) - (h - l : ℕ) := by
  by_cases hl : l ≤ h + 1
  · exact affectedClusterCost_le_with_deficit h l hh hh4 hl
  have hhl : h ≤ l := by omega
  rw [affectedClusterCost, min_eq_right hhl, Nat.sub_eq_zero_of_le hhl,
    Nat.cast_zero, sub_zero]
  have hprod : (l : ℤ) * ((h : ℤ) - l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  omega

theorem clusterCost_at_all_high (h : ℕ) : clusterCost h h = 7 * (h : ℤ) := by
  simp only [clusterCost, min_self]
  ring

theorem affectedClusterCost_at_all_high (h : ℕ) :
    affectedClusterCost h h = 5 * (h : ℤ) := by
  simp only [affectedClusterCost, min_self]
  ring

/-- The actual cost with `b` selected high atoms is bounded by the
worst admissible selection at fixed `l`. -/
theorem actual_cluster_cost_le (h l b : ℕ) (hbl : b ≤ l) (hbh : b ≤ h) :
    5 * (b : ℤ) + (l : ℤ) * ((h : ℤ) + 2 - l) ≤ clusterCost h l := by
  have hb : b ≤ min l h := le_min hbl hbh
  unfold clusterCost
  have hb' : (b : ℤ) ≤ (min l h : ℕ) := by exact_mod_cast hb
  omega

theorem actual_affected_cost_le (h l b : ℕ) (hbl : b ≤ l) (hbh : b ≤ h) :
    5 * (b : ℤ) + (l : ℤ) * ((h : ℤ) - l) ≤ affectedClusterCost h l := by
  have hb : b ≤ min l h := le_min hbl hbh
  unfold affectedClusterCost
  have hb' : (b : ℤ) ≤ (min l h : ℕ) := by exact_mod_cast hb
  omega

/-- Quotient and atom contributions share the matrix dimension. -/
theorem shared_dimension_bound (t r H l : ℕ) (hHr : H ≤ r) :
    (min t (r - l) : ℤ) - (H - l : ℕ) ≤ (min t (r - H) : ℕ) := by
  omega

/-- Combining a total atom cost with the quotient minor cost. -/
theorem shared_total_cost (t r H l : ℕ) (M A : ℤ)
    (hHr : H ≤ r) (hA : A ≤ M - (H - l : ℕ)) :
    A + (min t (r - l) : ℕ) ≤ M + (min t (r - H) : ℕ) := by
  have hb := shared_dimension_bound t r H l hHr
  omega

/-- Missing-node deficits can be summed before using the shared dimension. -/
theorem sum_deficits_ge_total_deficit {ι : Type*} (s : Finset ι)
    (h l : ι → ℕ) :
    (∑ i ∈ s, h i) - (∑ i ∈ s, l i) ≤ ∑ i ∈ s, (h i - l i) := by
  exact Nat.sub_le_iff_le_add.mpr (by
    calc
      (∑ i ∈ s, h i) ≤ ∑ i ∈ s, ((h i - l i) + l i) :=
        Finset.sum_le_sum (fun i _ => by omega)
      _ = (∑ i ∈ s, (h i - l i)) + ∑ i ∈ s, l i := Finset.sum_add_distrib)

/-- The exact common-root saving in the classwise maximum. -/
theorem root_gain_accounting (H A : ℤ) :
    7 * (H - A) + 5 * A = 7 * H - 2 * A := by ring

end Zeta5.Arithmetic
