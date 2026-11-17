import Zeta5.Certificate.LogTwo

/-!
# Integer representation of the 2048-node certificate

The grid spacing divides `10^30`, so square roots, logarithm lower bounds,
and the final trapezoid sum can all be checked using natural numbers. The
square-root intervals have denominator `M`, the `u` intervals denominator
`2*M`, the `g` lower bounds denominator `M^2`, and the trapezoid sum
denominator `4*M^3`, where `M = fixedScale`.

The predicates below are finite arithmetic predicates. Their connection to
real logarithms is given by `DirectedBounds` and the range-reduction lemma;
their connection to the potential integral also needs the analytic lemmas.
-/

namespace Zeta5.Certificate

def gridSize : ℕ := 2048
def gridSpacing : ℕ := 96156889 * fixedScale / (10 ^ 8 * gridSize)
def gridB (j : ℕ) : ℕ := j * gridSpacing

structure LogBound where
  exponent : ℕ
  z : ℕ
  numerator : ℕ
  deriving Repr

def LogBound.Valid (c : LogBound) (num den : ℕ) : Prop :=
  0 < den ∧
  den * 2 ^ c.exponent ≤ num ∧ num ≤ 2 * (den * 2 ^ c.exponent) ∧
  c.z * (num + den * 2 ^ c.exponent) ≤
    fixedScale * (num - den * 2 ^ c.exponent) ∧
  c.numerator = roundedLogNumerator fixedScale c.z 24 + c.exponent * logTwoNumerator

instance (c : LogBound) (num den : ℕ) : Decidable (c.Valid num den) := by
  unfold LogBound.Valid
  infer_instance

structure AnalyticNode where
  sqrtA : ℕ
  sqrtC : ℕ
  logOne : LogBound
  logTwo : LogBound
  logThree : LogBound
  deriving Repr

namespace AnalyticNode

def uLower (j : ℕ) (c : AnalyticNode) : ℕ :=
  gridB j + 9 * fixedScale / 10 + 2 * c.sqrtC - (c.sqrtA + 1)

def uUpper (j : ℕ) (c : AnalyticNode) : ℕ :=
  gridB j + 9 * fixedScale / 10 + 2 * (c.sqrtC + 1) - c.sqrtA

def vNumerator (j : ℕ) (c : AnalyticNode) : ℕ := fixedScale / 10 + c.uLower j

def gNumerator (j : ℕ) (c : AnalyticNode) : ℕ :=
  2 * c.uLower j * c.logOne.numerator + fixedScale / 5 * c.logTwo.numerator +
    2 * fixedScale * c.logThree.numerator

def Valid (j : ℕ) (c : AnalyticNode) : Prop :=
  c.sqrtA ^ 2 ≤ fixedScale ^ 2 + (gridB j) ^ 2 ∧
  fixedScale ^ 2 + (gridB j) ^ 2 ≤ (c.sqrtA + 1) ^ 2 ∧
  c.sqrtC ^ 2 ≤ fixedScale ^ 2 / 400 + (gridB j) ^ 2 ∧
  fixedScale ^ 2 / 400 + (gridB j) ^ 2 ≤ (c.sqrtC + 1) ^ 2 ∧
  c.sqrtA + 1 ≤ gridB j + 9 * fixedScale / 10 + 2 * c.sqrtC ∧
  0 < c.uLower j ∧ c.uUpper j = c.uLower j + 3 ∧
  c.logOne.Valid (2 * c.vNumerator j) (gridB j) ∧
  c.logTwo.Valid (2 * c.vNumerator j) (fixedScale / 20 + c.sqrtC + 1) ∧
  c.logThree.Valid (fixedScale + c.sqrtA) (2 * fixedScale) ∧
  0 < c.gNumerator j

instance (j : ℕ) (c : AnalyticNode) : Decidable (c.Valid j) := by
  unfold Valid
  infer_instance

end AnalyticNode

def initialGNumerator : ℕ := fixedScale / 5 * logTwoNumerator

/-- Check every node and the strictly positive gap to its predecessor. -/
def checkAnalyticNodes (start previousUpper : ℕ) : List AnalyticNode → Bool
  | [] => true
  | node :: rest =>
    decide (node.Valid start) && decide (previousUpper < node.uLower start) &&
      checkAnalyticNodes (start + 1) (node.uUpper start) rest

/-- The exact numerator of the sum of the lower trapezoids. -/
def trapezoidNumerator (start previousUpper previousG : ℕ) : List AnalyticNode → ℕ
  | [] => 0
  | node :: rest =>
    (node.uLower start - previousUpper) * (node.gNumerator start + previousG) +
      trapezoidNumerator (start + 1) (node.uUpper start) (node.gNumerator start) rest

theorem gridSpacing_exact : gridSpacing * (10 ^ 8 * gridSize) = 96156889 * fixedScale := by
  decide

end Zeta5.Certificate
