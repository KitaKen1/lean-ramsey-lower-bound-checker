import Std

namespace RamseyWeb

/- Source adjacency matrix:
https://github.com/google-research/google-research/blob/master/ramsey_number_bounds/improved_bounds/R(3,%2013)%20%3E=%2061.txt
-/

def fullMask (size : Nat) : Nat :=
  if size == 0 then
    0
  else
    (1 <<< size) - 1

def bitMask (i : Nat) : Nat :=
  1 <<< i

structure BitSet where
  size : Nat
  mask : Nat
  deriving Repr, Inhabited

def BitSet.empty (size : Nat) : BitSet :=
  { size := size, mask := 0 }

def BitSet.full (size : Nat) : BitSet :=
  { size := size, mask := fullMask size }

def BitSet.ofNatMask (size : Nat) (mask : Nat) : BitSet :=
  { size := size, mask := mask &&& (fullMask size) }

def BitSet.setBit (s : BitSet) (i : Nat) : BitSet :=
  if i < s.size then
    { s with mask := s.mask ||| (bitMask i) }
  else
    s

def BitSet.clearBit (s : BitSet) (i : Nat) : BitSet :=
  if i < s.size then
    let keep := (fullMask s.size) ^^^ (bitMask i)
    { s with mask := s.mask &&& keep }
  else
    s

def BitSet.hasBit (s : BitSet) (i : Nat) : Bool :=
  if i < s.size then
    (((s.mask >>> i) &&& 1) == 1)
  else
    false

def BitSet.isEmpty (s : BitSet) : Bool :=
  s.mask == 0

def BitSet.popcount (s : BitSet) : Nat := Id.run do
  let mut x := s.mask
  let mut count := 0
  while x != 0 do
    x := x &&& (x - 1)
    count := count + 1
  return count

def BitSet.firstSetBit? (s : BitSet) : Option Nat := Id.run do
  let mut i := 0
  while i < s.size do
    if s.hasBit i then
      return some i
    i := i + 1
  return none

def BitSet.inter (a b : BitSet) : BitSet :=
  let size := Nat.min a.size b.size
  { size := size, mask := (a.mask &&& b.mask) &&& (fullMask size) }

def BitSet.complement (s : BitSet) : BitSet :=
  let m := s.mask &&& (fullMask s.size)
  { size := s.size, mask := (fullMask s.size) ^^^ m }

def BitSet.diff (a b : BitSet) : BitSet :=
  a.inter b.complement

def BitSet.ofIndices (size : Nat) (indices : List Nat) : BitSet := Id.run do
  let mut s := BitSet.empty size
  for i in indices do
    s := s.setBit i
  return s

structure BitGraph where
  size : Nat
  rows : Array BitSet
  deriving Repr

def BitGraph.ofPackedRows (size : Nat) (rows : Array Nat) : BitGraph :=
  let bitRows := rows.map (fun row => BitSet.ofNatMask size row)
  { size := size, rows := bitRows }

def BitGraph.ofNeighborLists (size : Nat) (neighbors : Array (List Nat)) : BitGraph :=
  let bitRows := neighbors.map (fun row => BitSet.ofIndices size row)
  { size := size, rows := bitRows }

def BitGraph.hasEdge (g : BitGraph) (i j : Nat) : Bool :=
  (g.rows[i]!).hasBit j

def BitGraph.isSimpleUndirected (g : BitGraph) : Bool := Id.run do
  if g.rows.size != g.size then
    return false
  let mut ok := true
  let mut i := 0
  while ok && i < g.size do
    let row := g.rows[i]!
    if row.size != g.size then
      ok := false
    if row.mask > fullMask g.size then
      ok := false
    if g.hasEdge i i then
      ok := false
    let mut j := 0
    while ok && j < g.size do
      if g.hasEdge i j != g.hasEdge j i then
        ok := false
      j := j + 1
    i := i + 1
  return ok

def BitGraph.edgeCount (g : BitGraph) : Nat := Id.run do
  let mut total := 0
  let mut i := 0
  while i < g.size do
    total := total + (g.rows[i]!).popcount
    i := i + 1
  return total / 2

def BitGraph.complement (g : BitGraph) : BitGraph :=
  let rows := Id.run do
    let mut out : Array BitSet := #[]
    let mut i := 0
    while i < g.size do
      let row := (g.rows[i]!).complement.clearBit i
      out := out.push row
      i := i + 1
    return out
  { size := g.size, rows := rows }

def formatVertices (vertices : List Nat) : String :=
  match vertices.map (fun v => toString (v + 1)) with
  | [] => "[]"
  | first :: rest =>
      let body := rest.foldl (fun acc item => acc ++ ", " ++ item) first
      "[" ++ body ++ "]"

structure LowerBoundResult where
  cliqueWitness : Option (List Nat)
  independentSetWitness : Option (List Nat)
  deriving Repr

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

def claimR : Nat := 3
def claimS : Nat := 13
def claimNPlus1 : Nat := 61

def r313Rows : Array Nat :=
  #[
    (299771004825109056 : Nat),
    (581809086117446816 : Nat),
    (163537579981932800 : Nat),
    (597009662629384832 : Nat),
    (58549269207983392 : Nat),
    (227431783329712722 : Nat),
    (594485047021573281 : Nat),
    (190312268930484554 : Nat),
    (650770148302672532 : Nat),
    (79169669342505 : Nat),
    (158339338685010 : Nat),
    (864691145636222116 : Nat),
    (633357354740040 : Nat),
    (577727467012903440 : Nat),
    (288511988577117472 : Nat),
    (5066858837920320 : Nat),
    (721702458800378880 : Nat),
    (18297110514706688 : Nat),
    (40534870703362560 : Nat),
    (216177730227840000 : Nat),
    (18024294737594369 : Nat),
    (36048589475188738 : Nat),
    (72097178950377476 : Nat),
    (79169824899081 : Nat),
    (158339649798162 : Nat),
    (290482195916193924 : Nat),
    (633358599192648 : Nat),
    (577727469501808656 : Nat),
    (288512010734796928 : Nat),
    (5066868793541184 : Nat),
    (721702478711620608 : Nat),
    (18297150337188128 : Nat),
    (40534950348329472 : Nat),
    (216177889517773824 : Nat),
    (18024613317445633 : Nat),
    (36049226634924034 : Nat),
    (72098453269848068 : Nat),
    (81718463840265 : Nat),
    (163436927680530 : Nat),
    (297282974285103108 : Nat),
    (653747710722120 : Nat),
    (577768247724867600 : Nat),
    (299852566249340928 : Nat),
    (5229981685776960 : Nat),
    (730754428774122496 : Nat),
    (21201401686261888 : Nat),
    (41839853486215680 : Nat),
    (227513420071576576 : Nat),
    (72097178872594447 : Nat),
    (190322164837158914 : Nat),
    (74962504966545540 : Nat),
    (41838616493687081 : Nat),
    (227510950851543058 : Nat),
    (23244225566998689 : Nat),
    (297272779107074140 : Nat),
    (867576285623484560 : Nat),
    (294282165465121056 : Nat),
    (293455265071169700 : Nat),
    (270220925746563073 : Nat),
    (36048589436299594 : Nat)
  ]

def r313Graph : BitGraph :=
  BitGraph.ofPackedRows 60 r313Rows

def main : IO UInt32 := do
  IO.println "Processing single-file Lean4web example R_3_13_ge_61"
  IO.println s!"  claim: R({claimR}, {claimS}) >= {claimNPlus1}"
  IO.println s!"  vertices: {r313Graph.size}"
  IO.println s!"  valid simple graph: {r313Graph.isSimpleUndirected}"
  IO.println s!"  edges: {r313Graph.edgeCount}"

  let result := verifyLowerBound r313Graph claimR claimS
  match result.cliqueWitness with
  | some witness =>
      IO.println s!"  found forbidden clique: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no {claimR}-clique found"

  match result.independentSetWitness with
  | some witness =>
      IO.println s!"  found forbidden independent set: {formatVertices witness}"
      return 1
  | none =>
      IO.println s!"  no independent set of size {claimS} found"

  IO.println "  lower-bound check passed"
  return 0

end RamseyWeb

#eval RamseyWeb.main
