import Ramsey.Bounds
import Ramsey.Examples.R413Data

open Ramsey

def r413Main : IO UInt32 := do
  let graph := Ramsey.Examples.r413Graph
  IO.println "Processing Lean-defined example R_4_13_ge_139"
  IO.println s!"  claim: R({Ramsey.Examples.r413ClaimR}, {Ramsey.Examples.r413ClaimS}) >= {Ramsey.Examples.r413ClaimNPlus1}"
  IO.println s!"  vertices: {graph.size}"
  IO.println s!"  valid simple graph: {graph.isSimpleUndirected}"
  IO.println s!"  edges: {graph.edgeCount}"

  let result := verifyLowerBound graph Ramsey.Examples.r413ClaimR Ramsey.Examples.r413ClaimS
  match result.cliqueWitness with
  | some witness =>
      IO.println s!"  found forbidden clique: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no {Ramsey.Examples.r413ClaimR}-clique found"

  match result.independentSetWitness with
  | some witness =>
      IO.println s!"  found forbidden independent set: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no independent set of size {Ramsey.Examples.r413ClaimS} found"

  IO.println "  lower-bound check passed"
  return 0

def main : IO UInt32 :=
  r413Main
