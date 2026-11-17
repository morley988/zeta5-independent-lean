import Zeta5.Endpoint.Verified

-- Explicit root qualification rules out accidental local notation or
-- declaration shadowing at the theorem's public target.
example : _root_.Irrational ((_root_.riemannZeta (5 : ℂ)).re) :=
  Zeta5.irrational_zeta_five

#check @Zeta5.irrational_zeta_five
#print Zeta5.irrational_zeta_five
#print axioms Zeta5.irrational_zeta_five
#print axioms Zeta5.Arithmetic.windowNormalizer_arithmetic_rate
#print axioms Zeta5.Arithmetic.windowNormalizer_log_le_arithmeticMajorant_eventually
#print axioms Zeta5.Analysis.exists_analytic_rate_error
#print axioms Zeta5.Analysis.PhysicalMeasure.windowDeterminant_realZetaFive_pos
#print axioms Zeta5.Certificate.ExtendedArithmetic.allCells_certificate
#print axioms Zeta5.Certificate.analyticIntegral_gt_displayed
#print axioms Zeta5.Reuse.PrimeNumberTheorem.theta_ratio_limit
