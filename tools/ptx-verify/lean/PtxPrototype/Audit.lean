import Lean
import Lean.Util.CollectAxioms

/-! Audit tooling only. It adds no proof axioms or verification rules. The
type dependency walk expands project definitions/opaque bodies and constructor
types so naming a forbidden VC through a definition or structure is detected.
It is a structural guard, not a decision procedure for semantic equivalence
or consistency of arbitrary unproved mathematical propositions. -/
namespace PtxPrototype.Audit
open Lean Elab Command Meta

private def projectName (env : Environment) (name : Name) : Bool :=
  if name.toString.startsWith "Ptx." || name.toString.startsWith "PtxPrototype." then true else
  match env.getModuleIdxFor? name with
  | none => true -- Current-file aliases may use an arbitrary namespace.
  | some index =>
    let moduleName := env.header.moduleNames[index]!
    moduleName.toString.startsWith "Ptx." || moduleName.toString.startsWith "PtxPrototype"

private partial def typeDependencies (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | name::rest =>
    if seen.contains name then typeDependencies env rest seen else
    let seen := seen.insert name
    if !projectName env name then typeDependencies env rest seen else
    match env.find? name with
    | none => typeDependencies env rest seen
    | some info =>
      let extra := info.type.getUsedConstants.toList
      let extra := match info with
        | .defnInfo value => value.value.getUsedConstants.toList ++ extra
        | .opaqueInfo value => value.value.getUsedConstants.toList ++ extra
        | .inductInfo value => value.ctors ++ extra
        | _ => extra
      typeDependencies env (extra++rest) seen

private def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

private def declaration (name : Name) (reference : Option Name) : CommandElabM Unit := do
  let env ← getEnv
  let info ← getConstInfo name
  let axioms ← collectAxioms name
  let dependencies := typeDependencies env info.type.getUsedConstants.toList {}
  let statement ← liftTermElabM do
    return (← ppExpr info.type).pretty
  let prop ← liftTermElabM (isProp info.type)
  let sameType ← match reference with
    | none => pure true
    | some other =>
      let target ← getConstInfo other
      liftTermElabM (isDefEq info.type target.type)
  let result := Json.mkObj [
    ("name",toJson name.toString),("kind",toJson (kind info)),("is_prop",toJson prop),
    ("statement",toJson statement),("type_repr",toJson (reprStr info.type)),
    ("axioms",toJson (axioms.map Name.toString)),("matches_reference",toJson sameType),
    ("type_dependencies",toJson (dependencies.toArray.map Name.toString))]
  logInfo m!"PTX_PROTOTYPE_DECL {result.compress}"

elab "prototype_decl " target:ident : command => declaration target.getId none
elab "prototype_vc " target:ident " against " reference:ident : command =>
  declaration target.getId (some reference.getId)

elab "prototype_aux_guard " target:ident " against " reference:ident : command => do
  let actual ← getConstInfo target.getId
  let protectedInfo ← getConstInfo reference.getId
  let sameType ← liftTermElabM (isDefEq actual.type protectedInfo.type)
  let result := Json.mkObj [("assumption",toJson target.getId.toString),
    ("reference",toJson reference.getId.toString),("same_type",toJson sameType)]
  logInfo m!"PTX_PROTOTYPE_AUX_TYPE {result.compress}"

elab "prototype_inventory" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array String)) fun acc name info =>
    match info with
    | .axiomInfo _ => acc.push name.toString
    | _ => acc
  logInfo m!"PTX_PROTOTYPE_AXIOMS {(toJson names).compress}"

end PtxPrototype.Audit
