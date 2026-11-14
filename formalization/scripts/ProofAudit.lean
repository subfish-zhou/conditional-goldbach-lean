import ConditionalGoldbach
import Lean

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := modules[index]!
    unless origin == `ConditionalGoldbach || (`ConditionalGoldbach).isPrefixOf origin do continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo d => if d.hints.isAbbrev then "abbrev" else "def"
      | .inductInfo _ => if isStructure env name then "structure" else "inductive"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | _ => "generated"
    let range ← findDeclarationRanges? name
    let source := match range with
      | some r => Json.mkObj [
        ("start_line", toJson r.range.pos.line), ("start_column", toJson r.range.pos.column),
        ("end_line", toJson r.range.endPos.line), ("end_column", toJson r.range.endPos.column),
        ("name_line", toJson r.selectionRange.pos.line),
        ("name_column", toJson r.selectionRange.pos.column),
        ("name_end_line", toJson r.selectionRange.endPos.line),
        ("name_end_column", toJson r.selectionRange.endPos.column)]
      | none => Json.null
    let value := info.value? (allowOpaque := true)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson origin.toString),
      ("kind", toJson kind), ("source_range", source),
      ("private", toJson (isPrivateName name || name.isInternal)),
      ("axioms", toJson ((← Lean.collectAxioms name).map Name.toString)),
      ("type_constants", toJson (info.type.getUsedConstants.map Name.toString)),
      ("value_constants", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("contains_sorry_directly", toJson ((value.map Expr.hasSorry).getD false))]
  liftIO <| IO.FS.writeFile "proof-status-raw.json" (Json.arr rows).pretty
