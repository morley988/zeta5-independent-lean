import Zeta5.Certificate.Constants
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-! Exact rational integration of the seven upper-prime affine rows. -/

namespace Zeta5.Certificate

structure AffineRow where
  lo : ℚ
  hi : ℚ
  intercept : ℚ
  slope : ℚ

def AffineRow.area (r : AffineRow) : ℚ :=
  (r.hi - r.lo) * (r.intercept + r.slope * (r.lo + r.hi) / 2)

def upperRows : List AffineRow :=
  [⟨9 / 20, 1 / 2, 81 / 5, -24⟩,
   ⟨1 / 2, 21 / 40, 139 / 10, -15⟩,
   ⟨21 / 40, 5 / 8, 16, -19⟩,
   ⟨5 / 8, 3 / 4, 27 / 2, -15⟩,
   ⟨3 / 4, 5 / 6, 12, -13⟩,
   ⟨5 / 6, 19 / 20, 19 / 2, -10⟩,
   ⟨19 / 20, 1, 38 / 5, -8⟩]

theorem upperRows_length : upperRows.length = 7 := rfl

theorem upperRows_area : (upperRows.map AffineRow.area).sum = 901 / 600 := by
  norm_num [upperRows, AffineRow.area]

theorem upperRows_contiguous :
    (upperRows.zip upperRows.tail).all (fun p => decide (p.1.hi = p.2.lo)) = true := by
  norm_num [upperRows]

end Zeta5.Certificate
