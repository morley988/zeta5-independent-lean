"""Generate proofs assembling the already-certified 228 arithmetic cells."""
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
out=BASE/'Zeta5/Certificate/ArithmeticPartition.lean'
lines=['''import Zeta5.Certificate.ArithmeticIntegral

/-! Generated partition assembly; see `scripts/generate_arithmetic_partition.py`. -/

namespace Zeta5.Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem arithmeticCells_chain : arithmeticChainFits (1 / 40) arithmeticCells := by
  unfold arithmeticCells
''']
for j in range(228):
    lines.append(f'  refine ⟨rfl, arithmeticCell{j:03}_valid, ?_⟩\n')
lines.append('  trivial\n')
lines.append('set_option maxRecDepth 4096 in\ntheorem arithmeticCells_endpoint : arithmeticChainEnd (1 / 40) arithmeticCells = 9 / 20 := by rfl\n')
lines.append('set_option maxRecDepth 4096 in\nset_option maxHeartbeats 4000000 in\ntheorem arithmeticCells_area_sum : (arithmeticCells.map ArithmeticCell.area).sum = middleArea := by\n')
lines.append('  have h : (arithmeticCells.map ArithmeticCell.area).sum = '+ ' + '.join(f'middleAreaBlock{j:02}' for j in range(15))+' := by\n')
lines.append('    simp only [arithmeticCells, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]\n')
lines.append('    unfold '+' '.join(f'middleAreaBlock{j:02}' for j in range(15))+'\n')
lines.append('    ring\n  exact h.trans middleArea_blocks\n')
lines.append('''
theorem middleRankProfile_integrable :
    IntervalIntegrable middleRankProfile MeasureTheory.volume (1 / 40 : ℝ) (9 / 20 : ℝ) := by
  have h := (integrate_arithmeticChain arithmeticCells_chain).1
  rw [arithmeticCells_endpoint] at h
  norm_num at h ⊢
  exact h

theorem middleRankProfile_integral :
    (∫ β in (1 / 40 : ℝ)..(9 / 20 : ℝ), middleRankProfile β) = (middleArea : ℝ) := by
  have h := (integrate_arithmeticChain arithmeticCells_chain).2
  rw [arithmeticCells_endpoint, arithmeticCells_area_sum] at h
  norm_num at h ⊢
  exact h

end Zeta5.Certificate
''')
out.write_text('\n'.join(lines))
print(out)
