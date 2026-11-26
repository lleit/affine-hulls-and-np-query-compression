module

public import Splitter
meta import Splitter

public section

namespace Splitter.Tests

def first : Space :=
  ⟨[true, false, true], [[true, false, false], [true, true, false],
    [false, true, false], [false, false, false]]⟩

def second : Space := ⟨[false, true, false], [[true, false, true], [false, false, true]]⟩
def third : Space := ⟨[true, false, false], [[false, true, true], [false, false, true]]⟩

def planes : List Space := [first, second, third]

#guard split 0 [] == []
#guard split 3 [] == [false, false, false]
#guard split 3 planes == [false, true, true]
#guard planes.all (fun s => s.dimension 3 == 2)

example : (split 3 planes).length = 3 ∧ ∀ s ∈ planes, s.splitBy (split 3 planes) := by
  apply split_spec 3 2 planes
  · intro s hs
    simp only [planes, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp [Space.WellFormed, first, second, third]
  · intro s hs
    simp only [planes, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide
  · decide

private def unit (width pivot : Nat) : Word :=
  (List.range width).map (· == pivot)

private def wideSpaces (width count : Nat) : List Space :=
  (List.range count).map fun i =>
    let basis := (List.range 7).map fun j => unit width ((3 * i + 13 * j) % width)
    let dependent := add (basis.headD []) (basis.getD 1 [])
    ⟨unit width i, dependent :: basis⟩

def run : IO Unit := do
  let width := 260
  let spaces := wideSpaces width 80
  unless spaces.all (fun s => s.dimension width == 7) do
    throw (IO.userError "The wide-space test returned an incorrect rank")
  let z := split width spaces
  unless z.length == width && spaces.all (fun s => s.directions.any (dot · z)) do
    throw (IO.userError "The wide-space test returned an invalid splitting mask")
  IO.println s!"Verified a common {width}-bit mask for {spaces.length} affine spaces"

end Splitter.Tests

def main : IO Unit := Splitter.Tests.run

#print axioms Splitter.split_spec
#print axioms Splitter.split_work_bound
#print axioms Splitter.split_counter_bound
