import LiLiuGoldbach
import Lean

open Lean Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private def origin (env : Environment) (modules : Array Name) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => modules[i]!
  | none => env.mainModule

private def kind (i : ConstantInfo) : String :=
  match i with
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quotient"

run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  let localNames := env.constants.toList.toArray.filterMap fun (n, _) =>
    if "LiLiuGoldbach".isPrefixOf (origin env modules n).toString then some n else none
  let mut todo := localNames
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut missing : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | missing := missing.push n.toString; continue
    let typeRefs := info.type.getUsedConstants
    let valueRefs := (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    let ctorRefs := match info with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    todo := todo ++ typeRefs ++ valueRefs ++ ctorRefs
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("module", toJson (origin env modules n).toString),
      ("kind", toJson (kind info)),
      ("private", toJson (isPrivateName n)),
      ("type_refs", toJson (typeRefs.map Name.toString)),
      ("value_refs", toJson (valueRefs.map Name.toString)),
      ("constructor_refs", toJson (ctorRefs.map Name.toString))]
  let out := Json.mkObj [
    ("method", toJson "Transitive constant dependencies through declaration types and opaque-inclusive values; inductive constructors are included as in Lean.collectAxioms. Origins use Environment.getModuleIdxFor?."),
    ("imported_modules", toJson (modules.map Name.toString)),
    ("local_roots", toJson (localNames.map Name.toString)),
    ("missing", toJson missing),
    ("declarations", Json.arr rows)]
  liftIO <| IO.FS.writeFile "verification/publication/declaration-audit/declaration-graph.json" out.compress
  liftIO <| IO.FS.writeFile "verification/publication/declaration-audit/imported-modules.json"
    (toJson (modules.map Name.toString)).pretty
  logInfo m!"Audited {localNames.size} local declarations and {rows.size} reachable declarations; {missing.size} missing."
