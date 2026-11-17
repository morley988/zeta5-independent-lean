import Zeta5.Endpoint.Verified

/-! Independent final-target audit. The example uses the root Mathlib names,
so it cannot silently refer to a local replacement of zeta or irrationality. -/
example : _root_.Irrational ((_root_.riemannZeta (5 : ℂ)).re) :=
  Zeta5.irrational_zeta_five

set_option pp.fullNames true in
#check @Zeta5.irrational_zeta_five
set_option pp.fullNames true in
#print Zeta5.irrational_zeta_five
#print axioms Zeta5.irrational_zeta_five
#print axioms Zeta5.Analysis.exists_analytic_rate_error
#print axioms Zeta5.Arithmetic.windowNormalizer_log_le_arithmeticMajorant_eventually
#print axioms Zeta5.Certificate.allPrimePieces_area_le
#print axioms Zeta5.Certificate.analyticIntegral_gt_displayed
