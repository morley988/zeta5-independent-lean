import Zeta5.Certificate.ExtendedArithmetic.AllCells
import Zeta5.Arithmetic.UpperProfileComparison

/-!
# The complete finite arithmetic prime profile

The middle cells are the exact certified chain. Seven upper rows and two
large-prime rows complete the interval from `1/512` to `5/2`. All coefficients
are cast from their original exact rational definitions.
-/

noncomputable section
namespace Zeta5.Certificate
open Zeta5.Reuse.PrimePiecewise ExtendedArithmetic

/-- The real affine piece associated with one exact rational table row. -/
def rowPrimePiece (row : AffineRow) : AffinePiece :=
  ⟨row.lo, row.hi, row.intercept, row.slope⟩

lemma rowPrimePiece_valid {row : AffineRow} (hlo : 0 < row.lo) (hle : row.lo ≤ row.hi) :
    (rowPrimePiece row).Valid := by
  change 0 < (row.lo : ℝ) ∧ (row.lo : ℝ) ≤ (row.hi : ℝ)
  constructor <;> exact_mod_cast ‹_›

lemma rowPrimePiece_area (row : AffineRow) :
    (rowPrimePiece row).area = (row.area : ℝ) := by
  simp only [rowPrimePiece, AffinePiece.area, AffineRow.area, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  ring

lemma finiteArea_map_rowPrimePiece (rows : List AffineRow) :
    finiteArea (rows.map rowPrimePiece) = ((rows.map AffineRow.area).sum : ℚ) := by
  induction rows with
  | nil => simp [finiteArea]
  | cons row rows ih =>
      simp only [List.map_cons, finiteArea, List.sum_cons, Rat.cast_add,
        rowPrimePiece_area] at ih ⊢
      rw [ih]

lemma upperRows_piece_valid {row : AffineRow} (hrow : row ∈ upperRows) :
    (rowPrimePiece row).Valid := by
  simp only [upperRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rowPrimePiece, AffinePiece.Valid]

lemma largeRows_piece_valid {row : AffineRow} (hrow : row ∈ Zeta5.Arithmetic.largeRows) :
    (rowPrimePiece row).Valid := by
  simp only [Zeta5.Arithmetic.largeRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> norm_num [rowPrimePiece, AffinePiece.Valid]

lemma upperRows_piece_bounds {row : AffineRow} (hrow : row ∈ upperRows) :
    (1/512 : ℝ) ≤ (rowPrimePiece row).lo ∧ (rowPrimePiece row).hi ≤ 5/2 := by
  simp only [upperRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [rowPrimePiece]

lemma largeRows_piece_bounds {row : AffineRow} (hrow : row ∈ Zeta5.Arithmetic.largeRows) :
    (1/512 : ℝ) ≤ (rowPrimePiece row).lo ∧ (rowPrimePiece row).hi ≤ 5/2 := by
  simp only [Zeta5.Arithmetic.largeRows, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> norm_num [rowPrimePiece]

def allPrimePieces : List AffinePiece :=
  chainPrimePieces allCells ++ upperRows.map rowPrimePiece ++
    Zeta5.Arithmetic.largeRows.map rowPrimePiece

/-- Classification retains the original exact data row, so its proved local
valuation bound can be applied directly. -/
theorem allPrimePieces_mem {c : AffinePiece} (hc : c ∈ allPrimePieces) :
    (∃ x ∈ allCells, c = cellPrimePiece x.1) ∨
    (∃ row ∈ upperRows, c = rowPrimePiece row) ∨
    (∃ row ∈ Zeta5.Arithmetic.largeRows, c = rowPrimePiece row) := by
  simp only [allPrimePieces, List.mem_append] at hc
  rcases hc with (hmid | hu) | hl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmid
    exact Or.inl ⟨x, hx, rfl⟩
  · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hu
    exact Or.inr (Or.inl ⟨row, hrow, rfl⟩)
  · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hl
    exact Or.inr (Or.inr ⟨row, hrow, rfl⟩)

theorem allPrimePieces_valid : ∀ c ∈ allPrimePieces, c.Valid := by
  intro c hc
  rcases allPrimePieces_mem hc with ⟨x, hx, rfl⟩ | ⟨row, hrow, rfl⟩ | ⟨row, hrow, rfl⟩
  · exact cellPrimePiece_valid (allCells_valid x hx)
  · exact upperRows_piece_valid hrow
  · exact largeRows_piece_valid hrow

theorem allPrimePieces_bounds {c : AffinePiece} (hc : c ∈ allPrimePieces) :
    (1/512 : ℝ) ≤ c.lo ∧ c.hi ≤ 5/2 := by
  rcases allPrimePieces_mem hc with ⟨x, hx, rfl⟩ | ⟨row, hrow, rfl⟩ | ⟨row, hrow, rfl⟩
  · obtain ⟨hlo, hhi⟩ := allCells_bounds hx
    have hlo' : (1/512 : ℝ) ≤ (x.1.lo : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using Rat.cast_mono (K := ℝ) hlo
    have hhi' : (x.1.hi : ℝ) ≤ (9/20 : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using Rat.cast_mono (K := ℝ) hhi
    exact ⟨hlo', hhi'.trans (by norm_num)⟩
  · exact upperRows_piece_bounds hrow
  · exact largeRows_piece_bounds hrow

theorem allPrimePieces_area :
    finiteArea allPrimePieces = (cappedChainArea allCells : ℝ)+901/600+19/16 := by
  unfold allPrimePieces
  simp only [finiteArea, List.map_append, List.sum_append]
  change finiteArea (chainPrimePieces allCells)+
    finiteArea (upperRows.map rowPrimePiece)+
      finiteArea (Zeta5.Arithmetic.largeRows.map rowPrimePiece) = _
  rw [chainPrimePieces_area, finiteArea_map_rowPrimePiece, finiteArea_map_rowPrimePiece,
    upperRows_area, Zeta5.Arithmetic.largeRows_area]
  push_cast
  ring

theorem allPrimePieces_area_le :
    finiteArea allPrimePieces ≤ (areaUpper : ℝ)+901/600+19/16 := by
  rw [allPrimePieces_area]
  have h : (cappedChainArea allCells : ℝ) ≤ (areaUpper : ℝ) := by
    exact_mod_cast allCells_area_le
  linarith

theorem allPrimePieces_area_le_rat :
    finiteArea allPrimePieces ≤ ((areaUpper+901/600+19/16 : ℚ) : ℝ) := by
  push_cast
  exact allPrimePieces_area_le

end Zeta5.Certificate
