import Zeta5.Endpoint.Verified
import Lean.Util.CollectAxioms

-- This separate audit does not modify the archived proof.
example : _root_.Irrational
    (_root_.Complex.re (_root_.riemannZeta (5 : _root_.Complex))) :=
  _root_.Zeta5.irrational_zeta_five

open Lean Elab Command in
run_cmd do
  let ci ← getConstInfo ``Zeta5.irrational_zeta_five
  unless ci matches .thmInfo _ do
    throwError "The release target is not a theorem declaration"
  unless ci.levelParams.isEmpty do
    throwError "Unexpected universe parameters on the closed theorem"
  liftTermElabM do
    let expected ← Term.elabType
      (← `(_root_.Irrational
        (_root_.Complex.re (_root_.riemannZeta (5 : _root_.Complex)))))
    unless ← Meta.isDefEq ci.type expected do
      throwError "The declaration has a different type or additional hypotheses"
  let actual ← Lean.collectAxioms ``Zeta5.irrational_zeta_five
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == expected.size && expected.all actual.contains do
    throwError "Unexpected axiom set: {actual}"
  logInfo m!"RELEASE AUDIT PASSED: closed Mathlib target; exact axioms {actual}"

#print Zeta5.irrational_zeta_five
#print axioms Zeta5.irrational_zeta_five
