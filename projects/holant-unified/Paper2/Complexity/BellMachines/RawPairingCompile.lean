import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.BellReduction.RawPairing

/-! The three fixed endpoint reconnections compile to actual original graph
byte programs. The selected ordered ports and all retained rows are read from
the input; the mode is finite program data. No boundary graph is assumed. -/
namespace Paper2.Complexity.BellMachines.RawPairing
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler RawClosedNetwork
namespace Specification
abbrev rest := Paper2.BellReduction.RawPairing.rest
abbrev endpoint := Paper2.BellReduction.RawPairing.endpoint
abbrev rows := Paper2.BellReduction.RawPairing.rows
abbrev query := Paper2.BellReduction.RawPairing.query
end Specification
open Specification
noncomputable section

abbrev rawEncoding := RawClosedNetwork.encoding
abbrev rowsEncoding := framedListEncoding vertexEncoding
abbrev endsEncoding := framedListEncoding endpointEncoding

 def restComputes : Computes rawEncoding rowsEncoding rest := by
  let test := (pairComputes (RawTriple.unequalSelectedComputes 0)
    (RawTriple.unequalSelectedComputes 1)).andThen RawTriple.andComputes
  exact (pairComputes (identityComputes rawEncoding) RawTriple.verticesComputes).andThen
    (Lists.filterComputes rawEncoding vertexEncoding
      (fun G v => v != RawTriple.selected G 0 && v != RawTriple.selected G 1) test)

 def endpointComputes (i j : ℕ) : Computes rawEncoding endpointEncoding (fun G => endpoint G i j) :=
  (RawTriple.selectedEndsComputes i).andThen (getDComputes endpointEncoding j (0,false))

 def twoEndsComputes (a b : ℕ × ℕ) : Computes rawEncoding endsEncoding
    (fun G => [endpoint G a.1 a.2,endpoint G b.1 b.2]) := by
  let f (G : RawClosedNetwork) (side : Bool) :=
    if side then endpoint G b.1 b.2 else endpoint G a.1 a.2
  let cell (side : Bool) : Computes rawEncoding endpointEncoding (fun G => f G side) := by
    cases side
    · exact endpointComputes a.1 a.2
    · exact endpointComputes b.1 b.2
  exact congrComputes (fixedListComputes rawEncoding endpointEncoding f cell [false,true]) (fun _ => rfl)

 def rowComputes (a b : ℕ × ℕ) : Computes rawEncoding vertexEncoding
    (fun G => (0,[endpoint G a.1 a.2,endpoint G b.1 b.2])) :=
  recode (pairComputes (constantComputes rawEncoding encodingNatBool 0) (twoEndsComputes a b))
    id (fun _ => rfl) (fun _ => rfl)

 def pairs (mode : Fin 3) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  if mode.val=0 then [((0,0),(0,1)),((1,0),(1,1))] else
  if mode.val=1 then [((0,0),(1,0)),((0,1),(1,1))] else
    [((0,0),(1,1)),((0,1),(1,0))]

 def prefixComputes (mode : Fin 3) : Computes rawEncoding rowsEncoding
    (fun G => rows mode (endpoint G 0 0) (endpoint G 0 1)
      (endpoint G 1 0) (endpoint G 1 1) []) :=
  congrComputes (fixedListComputes rawEncoding vertexEncoding
    (fun G pq => (0,[endpoint G pq.1.1 pq.1.2,endpoint G pq.2.1 pq.2.2]))
    (fun pq => rowComputes pq.1 pq.2) (pairs mode))
    (fun G => by fin_cases mode <;> rfl)

 def computes (mode : Fin 3) : Computes rawEncoding rawEncoding (query mode) := by
  let vertices := (pairComputes (prefixComputes mode) restComputes).andThen
    (Lists.appendListsComputes vertexEncoding)
  apply recode (pairComputes vertices RawTriple.edgesComputes) id (fun _ => rfl)
  intro G
  have he : rows mode (endpoint G 0 0) (endpoint G 0 1)
      (endpoint G 1 0) (endpoint G 1 1) [] ++ rest G =
      rows mode (endpoint G 0 0) (endpoint G 0 1)
        (endpoint G 1 0) (endpoint G 1 1) (rest G) := by
    fin_cases mode <;> rfl
  change (pairEncoding rowsEncoding (framedListEncoding encodingNatBool)).encode
    (_,G.edges) = (pairEncoding rowsEncoding (framedListEncoding encodingNatBool)).encode (_,G.edges)
  congr 1
  exact Prod.ext he rfl

end
end Paper2.Complexity.BellMachines.RawPairing
