"""Generate a pure-integer Lean certificate equivalent to the manuscript program.

All data are untrusted witnesses. The emitted Lean check uses `decide`, not
`native_decide`, on explicit arithmetic predicates. The Python equality checks
also compare every node with the independently extracted Fraction program.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json
import certificate_explicit as original

BASE=Path(__file__).resolve().parents[1]
M=10**30
GRID=2048
SPACING=96156889*M//(10**8*GRID)
assert SPACING*10**8*GRID==96156889*M


def lognum(z):
    z2=z*z//M
    p,total=z,0
    for j in range(24):
        total+=2*p//(2*j+1)
        p=p*z2//M
    return total


LOG2=lognum(M//3)


def logbound(num,den):
    exponent=0
    while num > 2*den:
        den*=2
        exponent+=1
    assert den<=num<=2*den
    z=(num-den)*M//(num+den)
    n=lognum(z)+exponent*LOG2
    return exponent,z,n


nodes=[]
total=0
prev_upper=0
prev_g=M//5*LOG2
for j in range(1,GRID+1):
    b=j*SPACING
    a=isqrt(M*M+b*b)
    c=isqrt(M*M//400+b*b)
    ulo=b+9*M//10+2*c-a-1
    uhi=ulo+3
    vn=M//10+ulo
    l1=logbound(2*vn,b)
    l2=logbound(2*vn,M//20+c+1)
    l3=logbound(M+a,2*M)
    g=2*ulo*l1[2]+M//5*l2[2]+2*M*l3[2]
    ol,ou,og=original.u_and_g_lower(F(b,M))
    assert (F(ulo,2*M),F(uhi,2*M),F(g,M*M))==(ol,ou,og)
    assert ulo>prev_upper
    total+=(ulo-prev_upper)*(g+prev_g)
    nodes.append((a,c,l1,l2,l3,ulo,uhi,g))
    prev_upper,prev_g=uhi,g
assert F(total,4*M**3)==original.exact_analytic_lower()
assert prev_upper*5<12*M
assert total*10**10>54133705070*4*M**3


def tuple_log(t):
    return '⟨'+', '.join(map(str,t))+'⟩'


def tuple_node(t):
    a,c,l1,l2,l3,*_=t
    return '⟨'+', '.join([str(a),str(c),tuple_log(l1),tuple_log(l2),tuple_log(l3)])+'⟩'


header='''import Zeta5.Certificate.GridDefinitions

/-! Generated exact finite witnesses. See `scripts/generate_analytic_grid.py`.
No axiom or native-evaluation oracle is used by these checks. -/

namespace Zeta5.Certificate

'''
lines=[header]
for j,node in enumerate(nodes,1):
    lines.append(f'def analyticNode{j:04} : AnalyticNode := {tuple_node(node)}\n')
lines.append('def analyticNodes : List AnalyticNode := [\n'+',\n'.join(f'  analyticNode{j:04}' for j in range(1,GRID+1))+']\n')
lines.append('set_option maxRecDepth 32768 in\ntheorem analyticNodes_length : analyticNodes.length = 2048 := by decide\n')
lines.append('set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\ntheorem analyticNodes_all_checks : checkAnalyticNodes 1 0 analyticNodes = true := by decide\n')
lines.append(f'def analyticTotalNumerator : ℕ := {total}\n')
lines.append('set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\ntheorem analyticTotalNumerator_exact :\n    trapezoidNumerator 1 0 initialGNumerator analyticNodes = analyticTotalNumerator := by decide\n')
lines.append('theorem analyticLast_lt_delta : analyticNode2048.uUpper 2048 * 5 < 12 * fixedScale := by decide\n')
lines.append('theorem analyticTotalNumerator_gt_displayed :\n    analyticTotalNumerator * 10 ^ 10 > 54133705070 * (4 * fixedScale ^ 3) := by decide\n')
lines.append('theorem analyticTotalNumerator_gt_threshold :\n    analyticTotalNumerator * 10000 > 54133 * (4 * fixedScale ^ 3) := by decide\n')
lines.append('\nend Zeta5.Certificate\n')
out=BASE/'Zeta5/Certificate/AnalyticGrid.lean'
out.write_text('\n'.join(lines))

bench=[header]
for j,node in enumerate(nodes[:32],1):
    bench.append(f'def benchmarkNode{j:04} : AnalyticNode := {tuple_node(node)}\n')
bench.append('def benchmarkNodes : List AnalyticNode := ['+', '.join(f'benchmarkNode{j:04}' for j in range(1,33))+']\n')
bench.append('set_option maxRecDepth 8192 in\nset_option maxHeartbeats 0 in\ntheorem benchmarkNodes_checks : checkAnalyticNodes 1 0 benchmarkNodes = true := by decide\n')
bench.append('\nend Zeta5.Certificate\n')
(BASE/'Zeta5/Certificate/GridBenchmark.lean').write_text('\n'.join(bench))
(BASE/'evidence/analytic_grid_data.json').write_text(json.dumps({'scale':str(M),'count':GRID,'spacing':str(SPACING),'log2Numerator':str(LOG2),'totalNumerator':str(total),'totalDenominator':str(4*M**3),'matched_original_each_node':True,'matched_original_total':True},indent=2)+'\n')
print(out, 'nodes',len(nodes), 'bytes',out.stat().st_size,'total numerator',total)
