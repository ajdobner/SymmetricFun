import SymmetricFunctions
import SymmetricFun
import Lean.Elab.Command

/-! Generate the deterministic local index of accepted declarations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`SymmetricFun).isPrefixOf moduleName || (`SymmetricFunctions).isPrefixOf moduleName ||
          (`LambdaRing).isPrefixOf moduleName then
        unless name.isInternal || name.hasMacroScopes do
          let kind := match info with
            | .thmInfo _ => "theorem"
            | .defnInfo _ => "definition"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
            | .opaqueInfo _ => "opaque"
            | .axiomInfo _ => "axiom"
            | .quotInfo _ => "quotient"
          rows := rows.push s!"{moduleName}\t{name}\t{kind}"
  let sortedRows := rows.qsort (fun a b => a < b)
  liftIO <| IO.FS.writeFile "docs/declarations.tsv"
    ("module\tdeclaration\tkind\n" ++ String.intercalate "\n" sortedRows.toList ++ "\n")
  logInfo m!"Indexed {rows.size} noninternal accepted declarations."
