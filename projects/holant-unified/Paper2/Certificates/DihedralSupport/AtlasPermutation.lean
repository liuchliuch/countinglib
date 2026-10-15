import Paper2.Certificates.DihedralSupport.AtlasParityFrame
import Paper2.Certificates.DihedralSupport.CyclotomicArithmeticField

/-! Permuting the four actual ports preserves the literal 66-point atlas.
An oriented complement block either retains its phase or doubles it, and
reversing the two ordered blocks contributes one common minus sign. Exact
quadratic-field checks are interpreted by a genuine characteristic-zero
field homomorphism; no finite-field specialization is used. -/
namespace Paper2.Certificates.DihedralSupport.AtlasPermutation
open AtlasCounts AtlasVectors AtlasParityFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance permutationFintype : Fintype (Equiv.Perm (Fin 4)) := fintypePerm

def transportedCoordinate (epsilon : Bool) (e : Equiv.Perm (Fin 4))
    (c : Coordinate) : Coordinate :=
  coordinates (fun i => word epsilon c (e.symm i))

def transportedBlock (epsilon : Bool) (e : Equiv.Perm (Fin 4)) (p : Block) : Block :=
  (transportedCoordinate epsilon e (p,false)).1

def transportedPhase (epsilon : Bool) (e : Equiv.Perm (Fin 4))
    (p : Block) (r : Phase) : Phase :=
  if (transportedCoordinate epsilon e (p,false)).2 then 2*r else r

theorem transportedBlock_injective : ∀ epsilon e,
    Function.Injective (transportedBlock epsilon e) := by
  decide +kernel


def relabel (epsilon : Bool) (e : Equiv.Perm (Fin 4)) : PointLabel → PointLabel
  | .inl (p,r) => single (transportedBlock epsilon e p) (transportedPhase epsilon e p r)
  | .inr (p,r,t) =>
      let a := transportedBlock epsilon e p.1.1
      let b := transportedBlock epsilon e p.1.2
      let r' := transportedPhase epsilon e p.1.1 r
      let t' := transportedPhase epsilon e p.1.2 t
      if h : a<b then twoBlock ⟨(a,b),h⟩ r' t'
      else twoBlock ⟨(b,a),by
        apply lt_of_le_of_ne (le_of_not_gt h)
        intro he
        exact (ne_of_lt p.2) ((transportedBlock_injective epsilon e) he.symm)⟩ t' r'

def negative (epsilon : Bool) (e : Equiv.Perm (Fin 4)) : PointLabel → Bool
  | .inl _ => false
  | .inr (p,_,_) => decide (transportedBlock epsilon e p.1.2<
      transportedBlock epsilon e p.1.1)

def sign {K : Type*} [Field K] (epsilon : Bool) (e : Equiv.Perm (Fin 4))
    (l : PointLabel) : K := if negative epsilon e l then -1 else 1

theorem sign_ne_zero {K : Type*} [Field K]
    (epsilon : Bool) (e : Equiv.Perm (Fin 4)) (l : PointLabel) :
    sign (K := K) epsilon e l≠0 := by
  unfold sign
  split <;> simp

/-- All literal port permutations, parity frames, atlas points, and words
are checked in the exact characteristic-zero quadratic field Q(ω). -/
theorem table_permutation_checked : ∀ epsilon (e : Equiv.Perm (Fin 4)) l x,
    table CyclotomicArithmetic.omega epsilon l (fun i => x (e i)) =
      sign epsilon e l * table CyclotomicArithmetic.omega epsilon (relabel epsilon e l) x := by
  intro epsilon e
  fin_cases epsilon <;> fin_cases e <;> decide +kernel

variable {K L : Type} [Field K] [Field L]

theorem singleVector_map (phi : K →+* L) (omega : K) (p : Block)
    (r : Phase) (x : Coordinate) :
    phi (singleVector omega p r x)=singleVector (phi omega) p r x := by
  cases hb : x.2 <;> by_cases hp : x.1=p <;> simp [singleVector,hp,hb]

theorem table_map (phi : K →+* L) (omega : K) (epsilon : Bool) (l : PointLabel)
    (x : Fin 4 → Bool) :
    phi (table omega epsilon l x)=table (phi omega) epsilon l x := by
  by_cases hp : Paper2.HeightOne.parity x=epsilon.toNat
  · cases l with
    | inl l =>
      rcases l with ⟨p,r⟩
      simp [table,extendVector,hp,vector,singleVector_map]
    | inr l =>
      rcases l with ⟨p,r,t⟩
      simp [table,extendVector,hp,vector,singleVector_map]
  · simp [table,extendVector,hp]

variable [CharZero K]

/-- Literal equality up to the explicit common sign, over the actual
semantic field and with the original four ports permuted. -/
theorem table_permutation (omega : K) (hpoly : omega^2+omega+1=0)
    (epsilon : Bool) (e : Equiv.Perm (Fin 4)) (l : PointLabel)
    (x : Fin 4 → Bool) :
    table omega epsilon l (fun i => x (e i)) =
      sign epsilon e l * table omega epsilon (relabel epsilon e l) x := by
  let phi := CyclotomicArithmetic.embedField omega hpoly
  have h := congrArg phi (table_permutation_checked epsilon e l x)
  rw [map_mul,table_map,table_map] at h
  cases hn : negative epsilon e l <;> simpa [phi,sign,hn] using h

theorem admissible_reindex (omega : K) (hpoly : omega^2+omega+1=0)
    (epsilon : Bool) (f : Signature K 4) (hf : Admissible omega epsilon f)
    (e : Equiv.Perm (Fin 4)) : Admissible omega epsilon (Tensor.reindex e f) := by
  rcases hf with rfl | ⟨l,c,hc,rfl⟩
  · exact Or.inl (by funext x; rfl)
  · refine Or.inr ⟨relabel epsilon e l,c*sign epsilon e l,
      mul_ne_zero hc (sign_ne_zero epsilon e l),?_⟩
    funext x
    change c*table omega epsilon l (fun i => x (e i)) =
      (c*sign epsilon e l)*table omega epsilon (relabel epsilon e l) x
    rw [table_permutation omega hpoly]
    exact (mul_assoc _ _ _).symm

theorem admissible_reindex_iff (omega : K) (hpoly : omega^2+omega+1=0)
    (epsilon : Bool) (f : Signature K 4) (e : Equiv.Perm (Fin 4)) :
    Admissible omega epsilon (Tensor.reindex e f) ↔ Admissible omega epsilon f := by
  constructor
  · intro h
    have hh := admissible_reindex omega hpoly epsilon _ h e.symm
    simpa only [Tensor.reindex_symm] using hh
  · intro h
    exact admissible_reindex omega hpoly epsilon f h e

end Paper2.Certificates.DihedralSupport.AtlasPermutation

