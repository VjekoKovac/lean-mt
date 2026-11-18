module

import MT
import Solution
meta import Lean
/-! Inspect the transitive axiom sets for every exported theorem and axiom in
    the imported local modules. The tower also has a dedicated upstream dependency audit. -/
open Lean

run_cmd
  let env ← getEnv
  let allow := #[`propext, `Classical.choice, `Quot.sound]
  let mut statements : Nat := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    if mod == `Solution || (`MT).isPrefixOf mod then
      for info in data.constants do
        if info.isTheorem || info.isAxiom then
          let axs ← Lean.collectAxioms info.name
          for ax in axs do
            unless allow.contains ax do
              throwError "Unpermitted axiom {ax} in {info.name}"
          statements := statements + 1
  if statements == 0 then throwError "No project theorem declarations found"
  logInfo m!"Checked {statements} exported project theorem and axiom declarations against the three-axiom allowlist."
