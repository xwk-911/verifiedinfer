import Lean
import Lean.Util.CollectAxioms

/-! Metadata tooling evaluated in a temporary Lean file by proof_audit.py.
It adds no proof axioms. Temporary holes are detected through actual proof
dependencies, including uses through auxiliary lemmas. -/
namespace ProofAudit
open Lean Elab Command Meta

private def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

private def declaration (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  let axioms ← collectAxioms name
  let statement ← liftTermElabM do
    return (← ppExpr info.type).pretty
  let prop ← liftTermElabM (isProp info.type)
  let result := Json.mkObj [
    ("name",toJson name.toString),("kind",toJson (kind info)),("is_prop",toJson prop),
    ("statement",toJson statement),("type_repr",toJson (reprStr info.type)),
    ("axioms",toJson (axioms.map Name.toString))]
  logInfo m!"PTX_PROOF_DECL {result.compress}"

elab "proof_decl " target:ident : command => declaration target.getId

elab "proof_inventory" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array String)) fun acc name info =>
    match info with
    | .axiomInfo _ => acc.push name.toString
    | _ => acc
  logInfo m!"PTX_PROOF_AXIOMS {(toJson names).compress}"

end ProofAudit
