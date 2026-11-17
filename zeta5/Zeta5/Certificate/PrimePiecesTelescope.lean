import Zeta5.Certificate.AllPrimePieces
import Zeta5.Certificate.ExtendedArithmetic.PrimeIntervals

/-! # The exact telescope across every finite arithmetic prime piece -/

noncomputable section
namespace Zeta5.Reuse.PrimePiecewise

def pieceWeightedSum (cells : List AffinePiece) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (cells.map (fun c : AffinePiece => primeWeightedSum f ⌊c.lo * (N : ℝ)⌋₊ ⌊c.hi * (N : ℝ)⌋₊)).sum

theorem pieceWeightedSum_append (xs ys : List AffinePiece) (f : ℕ → ℝ) (N : ℕ) :
    pieceWeightedSum (xs ++ ys) f N = pieceWeightedSum xs f N + pieceWeightedSum ys f N := by
  simp [pieceWeightedSum]

end Zeta5.Reuse.PrimePiecewise

namespace Zeta5.Certificate
open Zeta5.Reuse.PrimePiecewise ExtendedArithmetic

theorem middlePieces_weightedSum (f : ℕ → ℝ) (N : ℕ) :
    pieceWeightedSum (chainPrimePieces allCells) f N =
      primeWeightedSum f ⌊(1 / 512 : ℝ) * N⌋₊ ⌊(9 / 20 : ℝ) * N⌋₊ := by
  have h := chainWeightedSum_telescope allCells_fits f N
  rw [allCells_endpoint] at h
  simpa [pieceWeightedSum, chainWeightedSum, chainPrimePieces, cellPrimePiece,
    List.map_map, Function.comp_def] using h

theorem upperPieces_weightedSum (f : ℕ → ℝ) (N : ℕ) :
    pieceWeightedSum (upperRows.map rowPrimePiece) f N =
      primeWeightedSum f ⌊(9 / 20 : ℝ) * N⌋₊ ⌊(1 : ℝ) * N⌋₊ := by
  simp only [upperRows, pieceWeightedSum, rowPrimePiece, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one, one_mul]
  simp only [← add_assoc]
  rw [primeWeightedSum_floor_add f (a := (9 / 20 : ℝ)) (b := 1 / 2) (c := 21 / 40)
    (by norm_num) (by norm_num) N]
  rw [primeWeightedSum_floor_add f (a := (9 / 20 : ℝ)) (b := 21 / 40) (c := 5 / 8)
    (by norm_num) (by norm_num) N]
  rw [primeWeightedSum_floor_add f (a := (9 / 20 : ℝ)) (b := 5 / 8) (c := 3 / 4)
    (by norm_num) (by norm_num) N]
  rw [primeWeightedSum_floor_add f (a := (9 / 20 : ℝ)) (b := 3 / 4) (c := 5 / 6)
    (by norm_num) (by norm_num) N]
  rw [primeWeightedSum_floor_add f (a := (9 / 20 : ℝ)) (b := 5 / 6) (c := 19 / 20)
    (by norm_num) (by norm_num) N]
  simpa only [one_mul] using primeWeightedSum_floor_add f
    (a := (9 / 20 : ℝ)) (b := 19 / 20) (c := 1) (by norm_num) (by norm_num) N

theorem largePieces_weightedSum (f : ℕ → ℝ) (N : ℕ) :
    pieceWeightedSum (Zeta5.Arithmetic.largeRows.map rowPrimePiece) f N =
      primeWeightedSum f ⌊(1 : ℝ) * N⌋₊ ⌊(5 / 2 : ℝ) * N⌋₊ := by
  simp only [Zeta5.Arithmetic.largeRows, pieceWeightedSum, rowPrimePiece, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one]
  exact primeWeightedSum_floor_add f (by norm_num) (by norm_num) N

/-- Every actual signed prime charge on the finite profile band is accounted
for exactly once, including every right endpoint. -/
theorem allPrimePieces_weightedSum (f : ℕ → ℝ) (N : ℕ) :
    pieceWeightedSum allPrimePieces f N =
      primeWeightedSum f ⌊(1 / 512 : ℝ) * N⌋₊ ⌊(5 / 2 : ℝ) * N⌋₊ := by
  rw [allPrimePieces, pieceWeightedSum_append, pieceWeightedSum_append,
    middlePieces_weightedSum, upperPieces_weightedSum, largePieces_weightedSum]
  rw [primeWeightedSum_floor_add f (a := (1 / 512 : ℝ))
    (b := 9 / 20) (c := 1) (by norm_num) (by norm_num) N]
  exact primeWeightedSum_floor_add f (by norm_num) (by norm_num) N

end Zeta5.Certificate
