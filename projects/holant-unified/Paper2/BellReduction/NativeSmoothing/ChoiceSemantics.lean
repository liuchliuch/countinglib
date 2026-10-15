import Paper2.BellReduction.NativeSmoothing.Endpoints

/-! Literal raw-record native-X evaluation by one Boolean choice per edge.
This is proved equal to the original decoded Network.denote; it is used only
for semantic surgery and is not charged as a polynomial-time evaluator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction.NativeSmoothing.Surgery.Choice
open Complexity RawClosedNetwork
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

abbrev Table (K : Type*) := ℕ → List Bool → K

def extend {m : ℕ} (c : Fin m → Bool) (i : ℕ) : Bool := if hi : i<m then c ⟨i,hi⟩ else false

def bit (c : ℕ → Bool) (p : RawEndpoint) : Bool := if p.2 then !(c p.1) else c p.1

def rowValue (F : Table K) (c : ℕ → Bool) (row : RawVertex) : K :=
  F row.1 (row.2.map (bit c))

def weight (F : Table K) (c : ℕ → Bool) (rows : List RawVertex) : K :=
  (rows.map (rowValue F c)).prod

def evaluate (F : Table K) (m : ℕ) (rows : List RawVertex) : K :=
  ∑c : Fin m → Bool,weight F (extend c) rows

 theorem weight_perm (F : Table K) (c : ℕ → Bool) {a b : List RawVertex}
    (h : a.Perm b) : weight F c a=weight F c b := (h.map _).prod_eq

 theorem weight_cons (F : Table K) (c : ℕ → Bool) (row : RawVertex) (rows : List RawVertex) :
    weight F c (row::rows)=rowValue F c row*weight F c rows := rfl

end Paper2.BellReduction.NativeSmoothing.Surgery.Choice
