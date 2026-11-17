/- Fresh declaration dependency audit for the extracted/reworked endpoint modules. -/
import Zeta5.Reuse.PadicMinors
import Zeta5.Reuse.Transcendental
import Zeta5.Reuse.ThetaAsymptotic
import Zeta5.Endpoint.IntegerPolynomial
import Zeta5.Endpoint.PrimitiveNormalization
import Zeta5.Endpoint.ZetaBridge
import Zeta5.Endpoint.ConcreteCriterion

import Zeta5.Reuse.PrimeAffine
import Zeta5.Analysis.PhysicalMeasureStieltjes
import Zeta5.Endpoint.PhysicalCriterion
import Zeta5.Reuse.PrimeNumberTheorem
import Zeta5.Arithmetic.BernoulliDistribution
import Zeta5.Arithmetic.BernoulliMoments
import Zeta5.Analysis.DeterminantRate
import Zeta5.Arithmetic.RestrictionDeterminant

#print axioms OddZeta.FourValue.PadicLower
#print axioms OddZeta.FourValue.PadicLower.zero
#print axioms OddZeta.FourValue.PadicLower.mono
#print axioms OddZeta.FourValue.PadicLower.of_ne_zero
#print axioms OddZeta.FourValue.PadicLower.neg
#print axioms OddZeta.FourValue.PadicLower.add
#print axioms OddZeta.FourValue.PadicLower.mul
#print axioms OddZeta.FourValue.padicLower_sum
#print axioms OddZeta.FourValue.padicLower_prod
#print axioms OddZeta.FourValue.PadicLower.sign_smul
#print axioms OddZeta.FourValue.padicLower_det_weighted
#print axioms OddZeta.FourValue.padicVal_det_weighted
#print axioms OddZeta.FourValue.Transcendental.atanPoly
#print axioms OddZeta.FourValue.Transcendental.atan_remainder_deriv
#print axioms OddZeta.FourValue.Transcendental.atan_remainder_bound
#print axioms OddZeta.FourValue.Transcendental.log_enclosure
#print axioms OddZeta.FourValue.Transcendental.atanRat
#print axioms OddZeta.FourValue.Transcendental.logRat
#print axioms OddZeta.FourValue.Transcendental.atanRat_cast
#print axioms OddZeta.FourValue.Transcendental.logRat_enclosure
#print axioms OddZeta.FourValue.Transcendental.atanRat_enclosure
#print axioms OddZeta.FourValue.Transcendental.atan_reduce_quarter
#print axioms OddZeta.FourValue.Transcendental.atan_reduce_inverse
#print axioms OddZeta.FourValue.Transcendental.pi_enclosure
#print axioms OddZeta.FourValue.Transcendental.log_rat_check
#print axioms OddZeta.FourValue.Transcendental.atan_rat_check
#print axioms OddZeta.FourValue.Transcendental.log_range_reduction
#print axioms OddZeta.FourValue.Transcendental.log_inverse_enclosure
#print axioms Zeta5.Reuse.ThetaAsymptotic.scaled_limit
#print axioms Zeta5.Reuse.ThetaAsymptotic.interval_limit
#print axioms Zeta5.Reuse.ThetaAsymptotic.weighted_intervals
#print axioms Zeta5.Reuse.ThetaAsymptotic.weighted_intervals_nat
#print axioms Zeta5.Endpoint.scaledEvalInt
#print axioms Zeta5.Endpoint.scaledEvalInt_cast
#print axioms Zeta5.Endpoint.positive_integer_values_not_tendsto_zero
#print axioms Zeta5.Endpoint.irrational_of_integer_polynomial_decay
#print axioms Zeta5.Endpoint.integral_scaling_of_primitive
#print axioms Zeta5.Endpoint.IsPrimitiveNormalization
#print axioms Zeta5.Endpoint.exists_primitive_normalization
#print axioms Zeta5.Endpoint.primitive_normalization_ratio_integer
#print axioms Zeta5.Endpoint.primitive_normalization_minimal
#print axioms Zeta5.Endpoint.primitive_normalization_unique
#print axioms Zeta5.Endpoint.primitiveNormalizer
#print axioms Zeta5.Endpoint.primitiveNormalizer_spec
#print axioms Zeta5.Endpoint.primitiveNormalizer_pos
#print axioms Zeta5.Endpoint.normalizedPolynomial
#print axioms Zeta5.Endpoint.normalizedPolynomial_map
#print axioms Zeta5.Endpoint.normalizedPolynomial_isPrimitive
#print axioms Zeta5.Endpoint.normalizedPolynomial_natDegree
#print axioms Zeta5.Endpoint.normalizedPolynomial_eval_real
#print axioms Zeta5.Endpoint.realZeta
#print axioms Zeta5.Endpoint.realZeta_cast
#print axioms Zeta5.Endpoint.realZeta_eq_re
#print axioms Zeta5.Endpoint.irrational_realZeta_five_iff
#print axioms Zeta5.Endpoint.windowValue
#print axioms Zeta5.Endpoint.windowNormalizer
#print axioms Zeta5.Endpoint.windowIntegerPolynomial
#print axioms Zeta5.Endpoint.windowScale
#print axioms Zeta5.Endpoint.windowNormalizer_pos
#print axioms Zeta5.Endpoint.windowIntegerPolynomial_degree
#print axioms Zeta5.Endpoint.windowIntegerPolynomial_eval
#print axioms Zeta5.Endpoint.irrational_zeta5_of_normalized_decay
#print axioms Zeta5.Endpoint.linear_over_windowScale_limit
#print axioms Zeta5.Endpoint.irrational_zeta5_of_log_rate_bounds

#print axioms Zeta5.Reuse.PrimeAffine.theta_scaled_integral_limit
#print axioms Zeta5.Reuse.PrimeAffine.primeAffineSum_identity
#print axioms Zeta5.Reuse.PrimeAffine.primeAffineSum_limit_of_theta
#print axioms Zeta5.Reuse.PrimeAffine.finite_primeAffineSum_limit_of_theta
#print axioms Zeta5.Analysis.PhysicalMeasure.density_pos
#print axioms Zeta5.Analysis.PhysicalMeasure.density_measurable
#print axioms Zeta5.Analysis.PhysicalMeasure.density_moment_integrable
#print axioms Zeta5.Analysis.PhysicalMeasure.density_moment_zeta
#print axioms Zeta5.Analysis.PhysicalMeasure.density_moment
#print axioms Zeta5.Analysis.PhysicalMeasure.polynomial_density_integrable
#print axioms Zeta5.Analysis.PhysicalMeasure.momentFunctional_square_pos
#print axioms Zeta5.Analysis.PhysicalMeasure.momentFunctional_zero_rational
#print axioms Zeta5.Analysis.PhysicalMeasure.physical_scaled_window_gram_det_pos
#print axioms Zeta5.Analysis.PhysicalMeasure.physicalMeasure_mass
#print axioms Zeta5.Analysis.PhysicalMeasure.physicalMeasure_moment
#print axioms Zeta5.Analysis.PhysicalMeasure.physicalMeasure_ae_pos
#print axioms Zeta5.Analysis.PhysicalMeasure.physicalMeasure_stieltjes_integrable
#print axioms Zeta5.Analysis.PhysicalMeasure.real_partialFractions
#print axioms Zeta5.Analysis.PhysicalMeasure.momentFunctional_eq_numeratorFunctional
#print axioms Zeta5.Analysis.PhysicalMeasure.entry_eval_eq_physical_gram
#print axioms Zeta5.Analysis.PhysicalMeasure.windowDeterminant_pos_of_stieltjes
#print axioms Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero_of_stieltjes
#print axioms Zeta5.Analysis.PhysicalMeasure.stieltjesTransform_hurwitz
#print axioms Zeta5.Analysis.PhysicalMeasure.stieltjesTransform_nat
#print axioms Zeta5.Analysis.PhysicalMeasure.stieltjesAtPositiveIntegers_realZetaFive
#print axioms Zeta5.Analysis.PhysicalMeasure.momentFunctional_eq_numeratorFunctional_realZetaFive
#print axioms Zeta5.Analysis.PhysicalMeasure.windowDeterminant_realZetaFive_pos
#print axioms Zeta5.Analysis.PhysicalMeasure.windowDeterminant_ne_zero
#print axioms Zeta5.Endpoint.windowValue_pos
#print axioms Zeta5.Endpoint.irrational_zeta5_of_physical_normalized_decay
#print axioms Zeta5.Endpoint.irrational_zeta5_of_two_log_rate_bounds
#print axioms Zeta5.Reuse.PrimeNumberTheorem.theta_ratio_limit
#print axioms Zeta5.Reuse.PrimeNumberTheorem.primeAffineSum_limit
#print axioms Zeta5.Arithmetic.bernoulliFunctional_binomialPolynomial
#print axioms Zeta5.Arithmetic.bernoulliFunctional_difference
#print axioms Zeta5.Arithmetic.bernoulliFunctional_distribution
#print axioms Zeta5.Arithmetic.bernoulliFunctional_iterate_derivative_below_square
#print axioms Zeta5.Arithmetic.bernoulliFunctional_iterate_derivative_log
#print axioms Zeta5.Arithmetic.polynomialMoment_eq_bernoulliFunctional
#print axioms Zeta5.Arithmetic.polynomialMoment_padicLower_of_integerValuedNumerator
#print axioms Zeta5.Arithmetic.polynomialMoment_padicLower_log

#print axioms OddZeta.FourValue.log_factorial_main_error
#print axioms OddZeta.FourValue.factorial_row_main_upper
#print axioms Zeta5.Analysis.PhysicalMeasure.exists_density_exponential_bound
#print axioms Zeta5.Analysis.exists_uniform_windowSquaredNorm_bound
#print axioms Zeta5.Analysis.log_rowNormUpper_le_profile
#print axioms Zeta5.Analysis.exists_windowValue_log_bound
#print axioms Zeta5.Analysis.exists_analytic_rate_error

#print axioms Zeta5.Arithmetic.padicMaximalIdeal_isMaximal
#print axioms Zeta5.Arithmetic.exists_kernel_row_basis
#print axioms Zeta5.Arithmetic.polynomialPadicLower_det_of_restriction_kernel
