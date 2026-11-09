import PrimeNumberTheoremAnd.IEANTN.Varlamov.Main
import Lean.Util.CollectAxioms

/-!
Transitive axiom audit of every public declaration in the local namespace.
Literature inputs remain ordinary theorem parameters and are visible in the
signatures; their absence from an axiom list does not prove those inputs.
An unexpected axiom, including sorryAx or native_decide's evaluation axiom,
is a hard compile error. The standard three axioms are explicitly allowed.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (`Varlamov).isPrefixOf name then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  logInfo m!"AXIOM AUDIT PASSED: {count} declarations; only propext, Classical.choice, Quot.sound"
