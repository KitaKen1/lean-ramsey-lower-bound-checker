import Ramsey.Bounds
import Ramsey.Examples.R313Data

open Ramsey

def r313Main : IO UInt32 := do
  let graph := Ramsey.Examples.r313Graph
  IO.println "Processing Lean-defined example R_3_13_ge_61"
  IO.println s!"  claim: R({Ramsey.Examples.r313ClaimR}, {Ramsey.Examples.r313ClaimS}) >= {Ramsey.Examples.r313ClaimNPlus1}"
  IO.println s!"  vertices: {graph.size}"
  IO.println s!"  valid simple graph: {graph.isSimpleUndirected}"
  IO.println s!"  edges: {graph.edgeCount}"

  let result := verifyLowerBound graph Ramsey.Examples.r313ClaimR Ramsey.Examples.r313ClaimS
  match result.cliqueWitness with
  | some witness =>
      IO.println s!"  found forbidden clique: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no {Ramsey.Examples.r313ClaimR}-clique found"

  match result.independentSetWitness with
  | some witness =>
      IO.println s!"  found forbidden independent set: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no independent set of size {Ramsey.Examples.r313ClaimS} found"

  IO.println "  lower-bound check passed"
  return 0

def main : IO UInt32 :=
  r313Main
