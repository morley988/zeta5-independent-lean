import Zeta5.Endpoint.Verified
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
# Independent audit of the closed ζ(5) endpoint

This module checks the fully qualified Mathlib target and the actual transitive
constant dependencies of the final checked theorem. The audit code adds no
mathematical assumption or proof oracle.
-/

example : _root_.Irrational
    (_root_.Complex.re (_root_.riemannZeta (5 : _root_.Complex))) :=
  _root_.Zeta5.irrational_zeta_five

set_option pp.fullNames true in
#check _root_.Zeta5.irrational_zeta_five

#print axioms Zeta5.irrational_zeta_five

open Lean Elab Command in
run_cmd do
  let axs ← Lean.collectAxioms ``Zeta5.irrational_zeta_five
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axs do
    unless allowed.contains ax do
      throwError "Unexpected transitive axiom: {ax}"
  let env ← getEnv
  let mut pending := #[``Zeta5.irrational_zeta_five]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        for dep in ci.getUsedConstantsAsSet.toList do
          unless seen.contains dep do
            pending := pending.push dep
  let required := #[
    ``Zeta5.Certificate.analyticNodes_all_checks,
    ``Zeta5.Certificate.ExtendedArithmetic.Block00.fits,
    ``Zeta5.Certificate.ExtendedArithmetic.Block23.fits,
    ``Zeta5.Reuse.PrimeNumberTheorem.theta_ratio_limit,
    ``chebyshev_asymptotic,
    ``Zeta5.Analysis.exists_analytic_rate_error,
    ``Zeta5.Arithmetic.polynomialPadicLower_det_of_restriction_kernel,
    ``OddZeta.FourValue.ProductFormula.rational_log_product_formula]
  for n in required do
    unless seen.contains n do
      throwError "Required checked bridge absent from final dependency closure: {n}"
  for i in List.range 24 do
    let pad := if i < 10 then "0" else ""
    for suffix in #["fits", "upper"] do
      let n := (s!"Zeta5.Certificate.ExtendedArithmetic.Block{pad}{i}.{suffix}").toName
      unless seen.contains n do
        throwError "Checked arithmetic block absent from final dependency closure: {n}"
  let forbidden := #[``sorryAx, ``prelim_decay_2, ``prelim_decay_3]
  for n in forbidden do
    if seen.contains n then
      throwError "Admitted declaration occurs in final dependency closure: {n}"
  let names := seen.toArray.qsort Name.lt
  let manifest := Json.mkObj [
    ("theorem", toJson "Zeta5.irrational_zeta_five"),
    ("axioms", toJson (axs.map Name.toString)),
    ("constant_count", toJson names.size),
    ("constants", toJson (names.map Name.toString))]
  let auditDir : System.FilePath := "evidence"
  liftIO <| IO.FS.createDirAll auditDir
  liftIO <| IO.FS.writeFile (auditDir / "final_constant_closure.json") manifest.pretty
  logInfo m!"Closed theorem audited: {names.size} transitive constants; axioms {axs}."
  logInfo "Checked analytic grid, all 24 arithmetic block fits and upper bounds, actual analytic rate, restriction determinant and PNT are present; both admitted Fourier lemmas and sorryAx are absent."
