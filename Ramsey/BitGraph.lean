import Std

namespace Ramsey

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

def BitGraph.neighbors (g : BitGraph) (i : Nat) : List Nat := Id.run do
  let mut out : List Nat := []
  let mut j := g.size
  while j > 0 do
    let k := j - 1
    if g.hasEdge i k then
      out := k :: out
    j := k
  return out

def formatVertices (vertices : List Nat) : String :=
  match vertices.map (fun v => toString (v + 1)) with
  | [] => "[]"
  | first :: rest =>
      let body := rest.foldl (fun acc item => acc ++ ", " ++ item) first
      "[" ++ body ++ "]"

end Ramsey
