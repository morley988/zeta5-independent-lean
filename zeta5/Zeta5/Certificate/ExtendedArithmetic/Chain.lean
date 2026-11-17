import Zeta5.Certificate.ExtendedArithmetic.Core
import Zeta5.Reuse.PrimePiecewise

/-! # Finite chain coverage and actual prime sums for capped arithmetic cells -/

noncomputable section
namespace Zeta5.Certificate.ExtendedArithmetic
open Zeta5.Reuse.PrimePiecewise Filter
open scoped Topology

theorem cappedChainEnd_append (a : ℚ) (xs ys : List (ArithmeticCell × ℚ)) :
    cappedChainEnd a (xs ++ ys) = cappedChainEnd (cappedChainEnd a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa [cappedChainEnd] using ih x.1.hi

theorem cappedChainUpper_append (xs ys : List (ArithmeticCell × ℚ)) :
    cappedChainUpper (xs ++ ys) = cappedChainUpper xs + cappedChainUpper ys := by
  induction xs with
  | nil => simp [cappedChainUpper]
  | cons x xs ih => simp [cappedChainUpper, ih, add_assoc]

theorem cappedChainFits_append {a : ℚ} {xs ys : List (ArithmeticCell × ℚ)}
    (hx : cappedChainFits a xs) (hy : cappedChainFits (cappedChainEnd a xs) ys) :
    cappedChainFits a (xs ++ ys) := by
  induction xs generalizing a with
  | nil => exact hy
  | cons x xs ih =>
      exact ⟨hx.1, hx.2.1, hx.2.2.1, ih hx.2.2.2 hy⟩

theorem cappedChain_valid {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) : ∀ x ∈ xs, x.1.Valid := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h.2.1
      · exact ih h.2.2.2 y hy

theorem cappedChain_end_ge {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) : a ≤ cappedChainEnd a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      have hh := ih h.2.2.2
      change a ≤ cappedChainEnd x.1.hi xs
      exact (h.1 ▸ h.2.1.2.1.le).trans hh

theorem cappedChain_mem_bounds {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) {x : ArithmeticCell × ℚ} (hx : x ∈ xs) :
    a ≤ x.1.lo ∧ x.1.hi ≤ cappedChainEnd a xs := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨h.1.ge, cappedChain_end_ge h.2.2.2⟩
      · have ht := ih h.2.2.2 hx
        exact ⟨(h.1 ▸ h.2.1.2.1.le).trans ht.1, ht.2⟩

theorem cappedChain_pairwise {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) :
    xs.Pairwise (fun x y => x.1.hi ≤ y.1.lo) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      apply List.pairwise_cons.mpr
      exact ⟨fun y hy => (cappedChain_mem_bounds h.2.2.2 hy).1, ih h.2.2.2⟩

/-- Every point of the right-closed total interval lies in a cell. -/
theorem cappedChain_cover {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) {β : ℝ} (ha : (a : ℝ) < β)
    (hb : β ≤ (cappedChainEnd a xs : ℝ)) :
    ∃ x ∈ xs, (x.1.lo : ℝ) < β ∧ β ≤ (x.1.hi : ℝ) := by
  induction xs generalizing a with
  | nil => simp only [cappedChainEnd] at hb; linarith
  | cons x xs ih =>
      by_cases hx : β ≤ (x.1.hi : ℝ)
      · exact ⟨x, by simp, by simpa only [h.1] using ha, hx⟩
      · obtain ⟨y, hy, hyl, hyr⟩ := ih h.2.2.2 (lt_of_not_ge hx) hb
        exact ⟨y, by simp [hy], hyl, hyr⟩

theorem cappedChain_cover_open {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) {β : ℝ} (ha : (a : ℝ) < β)
    (hb : β ≤ (cappedChainEnd a xs : ℝ))
    (hne : ∀ x ∈ xs, β ≠ (x.1.hi : ℝ)) :
    ∃ x ∈ xs, (x.1.lo : ℝ) < β ∧ β < (x.1.hi : ℝ) := by
  obtain ⟨x, hx, hxl, hxr⟩ := cappedChain_cover h ha hb
  exact ⟨x, hx, hxl, lt_of_le_of_ne hxr (hne x hx)⟩

def cappedChainArea (xs : List (ArithmeticCell × ℚ)) : ℚ :=
  (xs.map (fun x => x.1.area)).sum

theorem cappedChainArea_le_upper {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) : cappedChainArea xs ≤ cappedChainUpper xs := by
  induction xs generalizing a with
  | nil => simp [cappedChainArea, cappedChainUpper]
  | cons x xs ih =>
      simpa [cappedChainArea, cappedChainUpper] using add_le_add h.2.2.1 (ih h.2.2.2)

def cellPrimePiece (c : ArithmeticCell) : AffinePiece :=
  ⟨c.lo, c.hi, c.intercept, c.slope⟩

theorem cellPrimePiece_valid {c : ArithmeticCell} (hc : c.Valid) : (cellPrimePiece c).Valid := by
  change 0 < (c.lo : ℝ) ∧ (c.lo : ℝ) ≤ (c.hi : ℝ)
  constructor
  · exact_mod_cast hc.1
  · exact_mod_cast hc.2.1.le

theorem cellPrimePiece_area (c : ArithmeticCell) : (cellPrimePiece c).area = (c.area : ℝ) := by
  simp only [cellPrimePiece, AffinePiece.area, ArithmeticCell.area, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  ring

def chainPrimePieces (xs : List (ArithmeticCell × ℚ)) : List AffinePiece :=
  xs.map (fun x => cellPrimePiece x.1)

theorem chainPrimePieces_valid {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) : ∀ c ∈ chainPrimePieces xs, c.Valid := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  exact cellPrimePiece_valid (cappedChain_valid h x hx)

theorem chainPrimePieces_area (xs : List (ArithmeticCell × ℚ)) :
    finiteArea (chainPrimePieces xs) = (cappedChainArea xs : ℝ) := by
  induction xs with
  | nil => simp [chainPrimePieces, finiteArea, cappedChainArea]
  | cons x xs ih =>
      simp only [chainPrimePieces, List.map_cons, finiteArea, List.sum_cons,
        cappedChainArea, Rat.cast_add, cellPrimePiece_area] at ih ⊢
      rw [ih]

theorem chainPrimeMass_limit {a : ℚ} {xs : List (ArithmeticCell × ℚ)}
    (h : cappedChainFits a xs) :
    Tendsto (fun N => finitePrimeMass (chainPrimePieces xs) N / (N : ℝ) ^ 2)
      atTop (𝓝 (cappedChainArea xs : ℝ)) := by
  rw [← chainPrimePieces_area]
  exact finitePrimeMass_limit _ (chainPrimePieces_valid h)

/-- A compact append certificate keeps the 3,060-cell assembly modular. -/
def CappedChainCertificate (a b u : ℚ) (xs : List (ArithmeticCell × ℚ)) : Prop :=
  cappedChainFits a xs ∧ cappedChainEnd a xs = b ∧ cappedChainUpper xs = u

theorem CappedChainCertificate.append {a b c u v : ℚ} {xs ys : List (ArithmeticCell × ℚ)}
    (hx : CappedChainCertificate a b u xs) (hy : CappedChainCertificate b c v ys) :
    CappedChainCertificate a c (u + v) (xs ++ ys) := by
  refine ⟨cappedChainFits_append hx.1 (by simpa only [hx.2.1] using hy.1), ?_, ?_⟩
  · rw [cappedChainEnd_append, hx.2.1, hy.2.1]
  · rw [cappedChainUpper_append, hx.2.2, hy.2.2]

end Zeta5.Certificate.ExtendedArithmetic
