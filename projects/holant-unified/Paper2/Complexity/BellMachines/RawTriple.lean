import Paper2.BellReduction.RawOccurrence

/-! A literal raw-record implementation of selecting three designated Bell
rows. The equality tests compare serialized natural labels and ordered endpoint
lists. The semantic bridge to sequential popMarked is proved separately using
positive-row uniqueness; invalid inputs still have a total raw result. -/
namespace Paper2.Complexity.BellMachines.RawTriple
open Paper2.BellReduction.RawOccurrence

def marked (G : RawClosedNetwork) : List RawVertex :=
  G.vertices.filter (fun v => v.1 == 0)

def selected (G : RawClosedNetwork) (i : ℕ) : RawVertex :=
  (marked G).getD i (0, [])

def keep (p q r v : RawVertex) : Bool :=
  (v != p) && (v != q) && (v != r)

def rest (G : RawClosedNetwork) : List RawVertex :=
  G.vertices.filter (keep (selected G 0) (selected G 1) (selected G 2))

def split (G : RawClosedNetwork) : Split :=
  ⟨(selected G 0).2, (selected G 1).2, (selected G 2).2, rest G⟩

def transform (coreLabel : ℕ) (G : RawClosedNetwork) : RawClosedNetwork :=
  perform G coreLabel (split G)

end Paper2.Complexity.BellMachines.RawTriple
