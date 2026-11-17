import Zeta5.Arithmetic.PrimeAssembly

/-! The independent zeta(5) endpoint with all analytic, arithmetic,
and finite numerical obligations discharged. -/

namespace Zeta5

theorem irrational_zeta_five : Irrational (riemannZeta 5).re :=
  Analysis.irrational_zeta5_of_allPrimePieces_majorant
    Arithmetic.primeErrorCoefficient Arithmetic.endpointErrorCoefficient
    Arithmetic.windowNormalizer_log_le_arithmeticMajorant_eventually

#check irrational_zeta_five
#print axioms irrational_zeta_five

end Zeta5
