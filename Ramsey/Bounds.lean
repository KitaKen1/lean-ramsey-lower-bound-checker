import Ramsey.BitGraph

namespace Ramsey

structure LowerBoundResult where
  cliqueWitness : Option (List Nat)
  independentSetWitness : Option (List Nat)
  deriving Repr

def LowerBoundResult.holds (result : LowerBoundResult) : Bool :=
  result.cliqueWitness.isNone && result.independentSetWitness.isNone

def colorSort (g : BitGraph) (candidates : BitSet) : Array (Nat × Nat) := Id.run do
  let mut colored : Array (Nat × Nat) := #[]
  let mut uncolored := candidates
  let mut color := 0
  while !uncolored.isEmpty do
    color := color + 1
    let mut colorClass := uncolored
    while !colorClass.isEmpty do
      match colorClass.firstSetBit? with
      | none =>
          colorClass := BitSet.empty colorClass.size
      | some v =>
          colored := colored.push (v, color)
          uncolored := uncolored.clearBit v
          colorClass := colorClass.clearBit v
          colorClass := colorClass.diff (g.rows[v]!)
  return colored

partial def cliqueWitness? (g : BitGraph) (target : Nat) : Option (List Nat) :=
  let rec go (fuel : Nat) (chosenRev : List Nat) (chosen : Nat) (candidates : BitSet) : Option (List Nat) :=
    if chosen >= target then
      some chosenRev.reverse
    else if fuel == 0 then
      none
    else if chosen + candidates.popcount < target then
      none
    else
      let colored := colorSort g candidates
      let rec loop (idx : Nat) (remaining : BitSet) : Option (List Nat) :=
        match idx with
        | 0 => none
        | idx' + 1 =>
            let (v, color) := colored[idx']!
            if chosen + color < target then
              none
            else
              let nextChosenRev := v :: chosenRev
              let nextChosen := chosen + 1
              let nextCandidates := remaining.inter (g.rows[v]!)
              if nextChosen >= target then
                some nextChosenRev.reverse
              else
                match go (fuel - 1) nextChosenRev nextChosen nextCandidates with
                | some witness => some witness
                | none => loop idx' (remaining.clearBit v)
      loop colored.size candidates
  go target [] 0 (BitSet.full g.size)

def independentSetWitness? (g : BitGraph) (target : Nat) : Option (List Nat) :=
  cliqueWitness? g.complement target

def verifyLowerBound (g : BitGraph) (r s : Nat) : LowerBoundResult :=
  {
    cliqueWitness := cliqueWitness? g r
    independentSetWitness := independentSetWitness? g s
  }

end Ramsey
