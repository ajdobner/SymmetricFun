import SymmetricFunctions
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`SymmetricFunctions).isPrefixOf moduleName || (`LambdaRing).isPrefixOf moduleName then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "{name} depends on unapproved axiom {axiomName}"
        checked := checked + 1
  if checked == 0 then
    throwError "No accepted declarations were audited"
  logInfo m!"Audited transitive axioms of {checked} accepted declarations."
