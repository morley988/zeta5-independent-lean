"""Exact fixed-cutoff arithmetic certificate, with outward rational area bounds.

The resulting Lean files prove each selected floor/branch on the whole open
cell and bound its exact integral. No floating-point arithmetic is used.
The cutoff 512 gives a total below 5.412 even with the uniform remaining tail.
"""
from fractions import Fraction as F
from pathlib import Path
import json

BASE = Path(__file__).resolve().parents[1]
OUT = BASE / "Zeta5/Certificate/ExtendedArithmetic"
OUT.mkdir(parents=True, exist_ok=True)
Q, BLOCK, SCALE = 512, 128, 10**12
RHO, DELTA = F(5, 4), F(6, 5)
LEFT, RIGHT = F(1, Q), F(9, 20)


def rat(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator} / {x.denominator})"


points = {LEFT, RIGHT}
for q in range(1, Q + 1):
    points.update((F(1, q), F(2, 2*q + 1)))
for k in range(1, 5*Q//2 + 2):
    points.add(2*RHO/k)
points = sorted(x for x in points if LEFT <= x <= RIGHT)
cells = []
for a, b in zip(points, points[1:]):
    mid = (a+b)/2
    q, d = 1//mid, (2*RHO)//mid
    e = int(2*(1-q*mid) >= mid)
    crossing = (d+1-DELTA)/((d+1)*(q+F(e, 2)))
    cuts = [a, crossing, b] if a < crossing < b else [a, b]
    for lo, hi in zip(cuts, cuts[1:]):
        sat = (d+1)*(1-(q+F(e, 2))*(lo+hi)/2) >= DELTA
        intercept = (5+e)*DELTA if sat else (4+e)*DELTA+d+1
        slope = F(0) if sat else -(d+1)*(q+F(e, 2))
        area = (hi-lo)*(intercept+slope*(lo+hi)/2)
        cap = F(-(-area.numerator*SCALE//area.denominator), SCALE)
        assert 0 < lo < hi
        assert q*hi <= 1 <= (q+1)*lo
        assert (2*q+1)*hi <= 2 if e else 2 <= (2*q+1)*lo
        assert d*hi <= 2*RHO <= (d+1)*lo
        assert DELTA <= (d+1)*(1-(q+F(e, 2))*hi) if sat else (d+1)*(1-(q+F(e, 2))*lo) <= DELTA
        assert area <= cap and cap-area < F(1, SCALE)
        cells.append((lo, hi, q, e, d, sat, area, cap))
assert len(cells) == 3060
assert cells[0][0] == LEFT and cells[-1][1] == RIGHT
assert all(a[1] == b[0] for a, b in zip(cells, cells[1:]))

blocks = [cells[j:j+BLOCK] for j in range(0, len(cells), BLOCK)]
caps = []
for number, block in enumerate(blocks):
    name = f"Block{number:02}"
    start, end = block[0][0], block[-1][1]
    cap = sum((cell[-1] for cell in block), F(0))
    caps.append(cap)
    lines = ["import Zeta5.Certificate.ExtendedArithmetic.Core\n",
             "namespace Zeta5.Certificate.ExtendedArithmetic\n",
             f"namespace {name}\n",
             "set_option maxRecDepth 8192\nset_option maxHeartbeats 8000000\n",
             "def cells : List (ArithmeticCell × ℚ) := ["]
    rows = []
    for lo, hi, q, e, d, sat, area, upper in block:
        rows.append(f"  (⟨{rat(lo)}, {rat(hi)}, {q}, {str(bool(e)).lower()}, {d}, {str(sat).lower()}⟩, {rat(upper)})")
    lines.append(",\n".join(rows) + "]\n")
    lines.append(f"theorem fits : cappedChainFits {rat(start)} cells := by\n  unfold cells")
    for _ in block:
        lines.append("  refine ⟨rfl, ?_, ?_, ?_⟩")
        lines.append("  · norm_num [ArithmeticCell.Valid, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]")
        lines.append("  · norm_num [ArithmeticCell.area, ArithmeticCell.intercept, ArithmeticCell.slope, ArithmeticCell.widthSlope, ArithmeticCell.eps, delta, rho, s]")
    lines.append("  trivial\n")
    lines.append(f"theorem endpoint : cappedChainEnd {rat(start)} cells = {rat(end)} := by rfl\n")
    lines.append(f"theorem upper : cappedChainUpper cells = {rat(cap)} := by\n  norm_num [cappedChainUpper, cells]\n")
    lines.append(f"theorem bound :\n    IntervalIntegrable middleRankProfile MeasureTheory.volume ({rat(start)} : ℝ) ({rat(end)} : ℝ) ∧\n    (∫ β in ({rat(start)} : ℝ)..({rat(end)} : ℝ), middleRankProfile β) ≤ ({rat(cap)} : ℝ) := by\n  have h := integrate_cappedChain fits\n  rw [endpoint, upper] at h\n  norm_num at h ⊢\n  exact h\n")
    lines.append(f"end {name}\nend Zeta5.Certificate.ExtendedArithmetic\n")
    (OUT / f"{name}.lean").write_text("\n".join(lines))

area_upper = sum(caps, F(0))
total_upper = area_upper + 6*DELTA/Q + F(901, 600) + F(19, 16)
assert total_upper == F(202930490737, 37500000000)
assert total_upper < F(5412, 1000)
lines = [f"import Zeta5.Certificate.ExtendedArithmetic.Block{j:02}" for j in range(len(blocks))]
lines += ["\nset_option maxHeartbeats 0\n",
          "\nnamespace Zeta5.Certificate.ExtendedArithmetic\n",
          """theorem append_real_profile_bounds {a b c A B : ℝ}
    (h1 : IntervalIntegrable middleRankProfile MeasureTheory.volume a b ∧
      (∫ β in a..b, middleRankProfile β) ≤ A)
    (h2 : IntervalIntegrable middleRankProfile MeasureTheory.volume b c ∧
      (∫ β in b..c, middleRankProfile β) ≤ B) :
    IntervalIntegrable middleRankProfile MeasureTheory.volume a c ∧
      (∫ β in a..c, middleRankProfile β) ≤ A + B := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1]
  exact add_le_add h1.2 h2.2
""",
          f"def areaUpper : ℚ := {rat(area_upper)}\n",
          f"def totalUpper : ℚ := {rat(total_upper)}\n",
          "theorem extended_profile_bound :\n    IntervalIntegrable middleRankProfile MeasureTheory.volume (1 / 512 : ℝ) (9 / 20 : ℝ) ∧\n    (∫ β in (1 / 512 : ℝ)..(9 / 20 : ℝ), middleRankProfile β) ≤ (areaUpper : ℝ) := by",
          "  have h0 := Block00.bound"]
for j in range(1, len(blocks)):
    lines.append(f"  have h{j} := append_real_profile_bounds h{j-1} Block{j:02}.bound")
lines += [f"  norm_num [areaUpper] at h{len(blocks)-1} ⊢",
          f"  exact h{len(blocks)-1}\n",
          "theorem totalUpper_decomposition :\n    areaUpper + (36 : ℚ) / (5 * 512) + 901 / 600 + 19 / 16 = totalUpper := by\n  norm_num [areaUpper, totalUpper]\n",
          "theorem totalUpper_lt : totalUpper < (5412 : ℚ) / 1000 := by\n  norm_num [totalUpper]\n",
          "#print axioms extended_profile_bound\n#print axioms totalUpper_lt\n",
          "end Zeta5.Certificate.ExtendedArithmetic\n"]
(BASE / "Zeta5/Certificate/ExtendedArithmetic.lean").write_text("\n".join(lines))
report = {"cutoff": Q, "cells": len(cells), "blocks": len(blocks), "area_upper": str(area_upper),
          "total_upper": str(total_upper), "strict_target": "5412/1000", "rounding_scale": SCALE,
          "note": "Exact rational generation; Lean compilation is a separate verification step."}
(BASE / "evidence/extended_arithmetic_certificate.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps(report))
