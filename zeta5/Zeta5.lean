import Zeta5.Construction.PartialFractions
import Zeta5.Arithmetic.ClusterCosts
import Zeta5.Arithmetic.QuotientSupport
import Zeta5.Endpoint.ConcreteCriterion
import Zeta5.Reuse.Transcendental
import Zeta5.Reuse.PrimeAffine
import Zeta5.Certificate.Constants
import Zeta5.Certificate.ArithmeticCells
import Zeta5.Certificate.AnalyticGrid
import Zeta5.Analysis.ProfileInverse
import Zeta5.Analysis.GridIntegral
import Zeta5.Construction.ResidueDecomposition
import Zeta5.Arithmetic.SharedAllocation
import Zeta5.Arithmetic.EvaluationMinors
import Zeta5.Arithmetic.LocalNewton
import Zeta5.Certificate.ArithmeticPartition
import Zeta5.Analysis.PhysicalMeasurePencil
import Zeta5.Analysis.TrialPolynomial
import Zeta5.Endpoint.PhysicalCriterion
import Zeta5.Reuse.PrimeNumberTheorem
import Zeta5.Arithmetic.CentralIntegerValued
import Zeta5.Arithmetic.LocalDivision
import Zeta5.Arithmetic.ReflectedCounts
import Zeta5.Arithmetic.ReflectedMinors
import Zeta5.Arithmetic.PadicCongruences
import Zeta5.Analysis.AuxiliarySmallBall
import Zeta5.Endpoint.AnalyticCriterion
import Zeta5.Arithmetic.NormalizerBounds
import Zeta5.Arithmetic.FactorialFloorSum
import Zeta5.Arithmetic.LargePrimes
import Zeta5.Arithmetic.LocalDeterminant
import Zeta5.Arithmetic.RankProfileComparison
import Zeta5.Arithmetic.SmallPrimeEntries
import Zeta5.Certificate.ExtendedArithmetic
import Zeta5.Endpoint.Verified

/-!
# Verified irrationality endpoint for ζ(5)

The theorem `Zeta5.irrational_zeta_five` is unconditional. Its target is
Mathlib's `Irrational (riemannZeta 5).re`. Physical positivity, both global
rates, the finite arithmetic and analytic certificates, and the endpoint
contradiction are all discharged. Its transitive axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.
-/
