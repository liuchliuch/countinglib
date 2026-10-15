import Paper2.Certificates.DihedralSupport.AtlasGeometryCore
import Paper2.Certificates.DihedralSupport.AtlasGeometryData
import Paper2.Certificates.DihedralSupport.AtlasVectors

/-! Kernel checking of exact cyclotomic minor witnesses. The generated
payload names a formulaic rich line or a nonzero three-by-three minor. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
open AtlasCounts AtlasVectors AtlasGeometry CyclotomicArithmetic AtlasGeometryData
set_option synthInstance.maxSize 10000
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def pointLabel (i : ℕ) : PointLabel := pointList.getD i (single 0 0)
def point (i : ℕ) (x : Coordinate) : Scalar :=
  (vectors.getD i []).getD (2*x.1.val + if x.2 then 1 else 0) 0

def coordinate (i : ℕ) : Coordinate :=
  (⟨(i/2)%4,Nat.mod_lt _ (by decide)⟩,decide (i%2=1))

def rowPairs (i : ℕ) : List (ℕ × ℕ) := (List.range 66).flatMap fun j =>
  if i < j then ((List.range 66).filter (fun k => decide (j<k))).map (j,·) else []

def richLabel (i : ℕ) : RichLabel := richList.getD i (.inl 0)

def richIndex (r : RichLabel) (j : Fin 3) : ℕ := pointList.idxOf (richPoints r j)

def checkRich (i : ℕ) : Bool :=
  let r := richLabel i
  let code := richPairCodes.getD i 0
  let a := coordinate (code/8)
  let b := coordinate (code%8)
  decide (minor2 (point (richIndex r 0)) (point (richIndex r 1)) a b ≠ 0) &&
    (List.range 8).all (fun c => decide (minor3 (point (richIndex r 0))
      (point (richIndex r 1)) (point (richIndex r 2)) a b (coordinate c) = 0))

def checkRichLines : Bool := (List.range 202).all checkRich

theorem coordinate_encode (x : Coordinate) :
    coordinate (2*x.1.val + if x.2 then 1 else 0) = x := by
  rcases x with ⟨p,b⟩
  fin_cases p <;> cases b <;> rfl

theorem coordinate_index_lt (x : Coordinate) :
    2*x.1.val + (if x.2 then 1 else 0) < 8 := by
  rcases x with ⟨p,b⟩
  fin_cases p <;> cases b <;> decide

theorem checkRich_sound {i : ℕ} (h : checkRich i = true) :
    OnLine (point (richIndex (richLabel i) 0)) (point (richIndex (richLabel i) 1))
      (point (richIndex (richLabel i) 2)) := by
  obtain ⟨hn,hz⟩ := Bool.and_eq_true_iff.mp h
  apply onLine_of_minor3_zero (of_decide_eq_true hn)
  intro c
  have hh := List.all_eq_true.mp hz
    (2*c.1.val + if c.2 then 1 else 0) (List.mem_range.mpr (coordinate_index_lt c))
  simpa only [coordinate_encode] using (of_decide_eq_true hh)

def checkTriple (i j k code : ℕ) : Bool :=
  if code < 202 then
    decide (richSet (richLabel code) = {pointLabel i,pointLabel j,pointLabel k})
  else
    decide (minor3 (point i) (point j) (point k)
      (coordinate ((code-202)/64)) (coordinate (((code-202)/8)%8))
        (coordinate ((code-202)%8)) ≠ 0)

def checkRow (i : ℕ) : Bool :=
  decide ((rowCodes i).length = (rowPairs i).length) &&
    ((rowPairs i).zip (rowCodes i)).all (fun e => checkTriple i e.1.1 e.1.2 e.2)

theorem checkTriple_sound {i j k code : ℕ} (h : checkTriple i j k code = true)
    (hz : ∀ a b c, minor3 (point i) (point j) (point k) a b c = 0) :
    ∃ r : RichLabel, richSet r = {pointLabel i,pointLabel j,pointLabel k} := by
  unfold checkTriple at h
  split_ifs at h with hc
  · exact ⟨richLabel code,of_decide_eq_true h⟩
  · exact False.elim ((of_decide_eq_true h) (hz _ _ _))

private theorem zip_exists {A B : Type*} {xs : List A} {ys : List B}
    (hlen : xs.length = ys.length) {x : A} (hx : x ∈ xs) :
    ∃ y, (x,y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨b,by simp⟩
      · obtain ⟨y,hy⟩ := ih (by simpa using hlen) hx
        exact ⟨y,by simp [hy]⟩

theorem checkRow_sound {i j k : ℕ} (h : checkRow i = true)
    (hij : i < j) (hjk : j < k) (hk : k < 66)
    (hz : ∀ a b c, minor3 (point i) (point j) (point k) a b c = 0) :
    ∃ r : RichLabel, richSet r = {pointLabel i,pointLabel j,pointLabel k} := by
  obtain ⟨hlen,hall⟩ := Bool.and_eq_true_iff.mp h
  have hmem : (j,k) ∈ rowPairs i := by
    simp only [rowPairs,List.mem_flatMap]
    refine ⟨j,List.mem_range.mpr (by omega),?_⟩
    simp [hij,hjk,hk]
  obtain ⟨code,hcode⟩ := zip_exists (of_decide_eq_true hlen).symm hmem
  have hc : checkTriple i j k code = true :=
    List.all_eq_true.mp hall ((j,k),code) hcode
  exact @checkTriple_sound i j k code hc hz

def pairGood (i j : ℕ) : Bool := (List.range 8).any fun a =>
  (List.range 8).any fun b => decide (minor2 (point i) (point j)
    (coordinate a) (coordinate b) ≠ 0)

def checkPairs : Bool := (List.range 66).all fun i => (List.range 66).all fun j =>
  if i < j then pairGood i j else true

theorem checkPairs_sound (h : checkPairs = true) {i j : ℕ}
    (hij : i < j) (hj : j < 66) :
    ∃ a b, minor2 (point i) (point j) a b ≠ 0 := by
  have hi : i < 66 := lt_trans hij hj
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
    j (List.mem_range.mpr hj)
  simp only [ite_eq_left hij] at hh
  obtain ⟨a,_,ha⟩ := List.any_eq_true.mp hh
  obtain ⟨b,_,hb⟩ := List.any_eq_true.mp ha
  exact ⟨coordinate a,coordinate b,of_decide_eq_true hb⟩

end Paper2.Certificates.DihedralSupport.AtlasGeometryCheck
