import Paper2.Certificates.DihedralSupport.AtlasVectors
import Paper2.Certificates.DihedralSupport.AtlasGeometryCore

/-! Literal Segre factors of every atlas ruling.  The four coefficients are
placed in a concrete two-by-two matrix on the two original complement blocks.
The ruling with r+t fixed has its second factor fixed; the ruling with r−t
fixed has its first factor fixed.  The full linear span is covered. -/
namespace Paper2.Certificates.DihedralSupport.AtlasRulingFactors
open AtlasCounts AtlasVectors
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

def placement (p : Pair) (i j : Bool) : Coordinate :=
  if i then (if j then (p.1.1,true) else (p.1.2,false))
  else (if j then (p.1.2,true) else (p.1.1,false))

def rulingMatrix (p : Pair) (v : Coordinate → K) : Bool → Bool → K :=
  fun i j => v (placement p i j)

/-- The fixed factor depends only on the ruling label, never on the
linear-combination coefficients or the varying phase point. -/
def fixedFactor (ω : K) (c : Phase) : Bool → K :=
  fun i => if i then -ω^(2*c.val) else 1

def varyingFactor (p : Pair) (orientation : Bool) (v : Coordinate → K) : Bool → K :=
  fun i => if i then v (p.1.2,orientation) else v (p.1.1,false)

def FixedRuling (ω : K) (l : RulingLabel) (v : Coordinate → K) : Prop :=
  (∀ x, x.1≠l.1.1.1 → x.1≠l.1.1.2 → v x=0) ∧
    ∃ u : Bool → K, ∀ i j,
      rulingMatrix l.1 v i j =
        if l.2.1 then fixedFactor ω l.2.2 i*u j
        else u i*fixedFactor ω l.2.2 j

theorem fixedFactor_ne_zero (ω : K) (c : Phase) : fixedFactor ω c≠0 := by
  intro h
  have h0 := congrFun h false
  simp [fixedFactor] at h0

theorem placement_injective (p : Pair) :
    Function.Injective (fun z : Bool × Bool => placement p z.1 z.2) := by
  have hp : p.1.1≠p.1.2 := ne_of_lt p.2
  rintro ⟨i,j⟩ ⟨k,t⟩ h
  cases i <;> cases j <;> cases k <;> cases t <;>
    simp_all [placement,Prod.mk.injEq]

theorem placement_range (p : Pair) (x : Coordinate) :
    (∃ i j, placement p i j=x) ↔ x.1=p.1.1 ∨ x.1=p.1.2 := by
  rcases x with ⟨q,b⟩
  constructor
  · rintro ⟨i,j,h⟩
    cases i <;> cases j <;> simp_all [placement,Prod.mk.injEq]
  · rintro (rfl|rfl) <;> cases b
    · exact ⟨false,false,rfl⟩
    · exact ⟨true,true,rfl⟩
    · exact ⟨true,false,rfl⟩
    · exact ⟨false,true,rfl⟩

private theorem pow4 (ω : K) (h : ω^3=1) : ω^4=ω := by
  calc
    ω^4 = ω^3*ω := by ring
    _ = ω := by rw [h,one_mul]

private theorem pow5 (ω : K) (h : ω^3=1) : ω^5=ω^2 := by
  calc
    ω^5 = ω^3*ω^2 := by ring
    _ = ω^2 := by rw [h,one_mul]

private theorem pow6 (ω : K) (h : ω^3=1) : ω^6=1 := by
  calc
    ω^6 = (ω^3)^2 := by ring
    _ = 1 := by rw [h]; simp

private theorem pow8 (ω : K) (h : ω^3=1) : ω^8=ω^2 := by
  calc
    ω^8 = ω^6*ω^2 := by ring
    _ = ω^2 := by rw [pow6 ω h,one_mul]

private theorem phase_val_sub (a b : Phase) :
    (a-b).val=(a.val+3-b.val)%3 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Each of the actual three phase points has the same literal factor. -/
theorem phase_factorization (ω : K) (hω : ω^3=1)
    (p : Pair) (b : Bool) (c r : Phase) (i j : Bool) :
    rulingMatrix p (vector ω (twoBlock p r (if b then r-c else c-r))) i j =
      if b then fixedFactor ω c i*
        varyingFactor p b (vector ω (twoBlock p r (if b then r-c else c-r))) j
      else varyingFactor p b (vector ω (twoBlock p r (if b then r-c else c-r))) i*
        fixedFactor ω c j := by
  have hp : p.1.1≠p.1.2 := ne_of_lt p.2
  have hq : p.1.2≠p.1.1 := Ne.symm hp
  have h4 := pow4 ω hω
  have h5 := pow5 ω hω
  have h6 := pow6 ω hω
  have h8 := pow8 ω hω
  cases b <;> cases i <;> cases j <;>
    simp [rulingMatrix,placement,fixedFactor,varyingFactor,
      vector,twoBlock,singleVector,hp,hq,phase_val_sub] <;>
    fin_cases c <;> fin_cases r <;>
    norm_num [ZMod.val] <;>
    ring_nf <;> simp_all

theorem point_factorization (ω : K) (hω : ω^3=1)
    (l : RulingLabel) (t : Fin 3) (i j : Bool) :
    rulingMatrix l.1 (vector ω (richPoints (.inr (.inl l)) t)) i j =
      if l.2.1 then fixedFactor ω l.2.2 i*
        varyingFactor l.1 l.2.1 (vector ω (richPoints (.inr (.inl l)) t)) j
      else varyingFactor l.1 l.2.1 (vector ω (richPoints (.inr (.inl l)) t)) i*
        fixedFactor ω l.2.2 j :=
  phase_factorization ω hω l.1 l.2.1 l.2.2 (phase t) i j

/-- Every linear combination of the first two phase points retains the
fixed tensor factor, and every coefficient outside the two blocks vanishes. -/
theorem combination_fixedRuling (ω : K) (hω : ω^3=1)
    (l : RulingLabel) (α β : K) :
    FixedRuling ω l
      (α • vector ω (richPoints (.inr (.inl l)) 0)+
       β • vector ω (richPoints (.inr (.inl l)) 1)) := by
  constructor
  · intro x hp hq
    simp [richPoints,vector,twoBlock,singleVector,hp,hq]
  · refine ⟨fun i => α*varyingFactor l.1 l.2.1
        (vector ω (richPoints (.inr (.inl l)) 0)) i+
        β*varyingFactor l.1 l.2.1
        (vector ω (richPoints (.inr (.inl l)) 1)) i,?_⟩
    intro i j
    change α*rulingMatrix l.1 (vector ω (richPoints (.inr (.inl l)) 0)) i j+
      β*rulingMatrix l.1 (vector ω (richPoints (.inr (.inl l)) 1)) i j=_
    rw [point_factorization ω hω,point_factorization ω hω]
    cases l.2.1 <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> ring

/-- Membership in the actual linear submodule span, rather than only a
statement about the three stored points. -/
theorem span_fixedRuling (ω : K) (hω : ω^3=1)
    (l : RulingLabel) (v : Coordinate → K)
    (hv : v ∈ Submodule.span K
      ({vector ω (richPoints (.inr (.inl l)) 0),
        vector ω (richPoints (.inr (.inl l)) 1)} : Set (Coordinate → K))) :
    FixedRuling ω l v := by
  obtain ⟨α,β,rfl⟩ := Submodule.mem_span_pair.mp hv
  exact combination_fixedRuling ω hω l α β

/-- Nonzero projective points in the ruling have two nonzero actual factors;
the zero vector is the only span vector whose varying factor can vanish. -/
theorem FixedRuling.nonzero_factors {ω : K} {l : RulingLabel}
    {v : Coordinate → K} (h : FixedRuling ω l v) (hv : v≠0) :
    fixedFactor ω l.2.2≠0 ∧ ∃ u : Bool → K, u≠0 ∧ ∀ i j,
      rulingMatrix l.1 v i j =
        if l.2.1 then fixedFactor ω l.2.2 i*u j
        else u i*fixedFactor ω l.2.2 j := by
  obtain ⟨hout,u,hu⟩ := h
  refine ⟨fixedFactor_ne_zero _ _,u,?_,hu⟩
  intro hz
  apply hv
  funext x
  by_cases hx : x.1=l.1.1.1 ∨ x.1=l.1.1.2
  · obtain ⟨i,j,hx⟩ := (placement_range l.1 x).mpr hx
    have hh := hu i j
    rw [hz] at hh
    simpa [rulingMatrix,hx] using hh
  · push Not at hx
    exact hout x hx.1 hx.2

theorem primitive_span_fixedRuling (ω : K) (hω : IsPrimitiveRoot ω 3)
    (l : RulingLabel) (v : Coordinate → K)
    (hv : v ∈ Submodule.span K
      ({vector ω (richPoints (.inr (.inl l)) 0),
        vector ω (richPoints (.inr (.inl l)) 1)} : Set (Coordinate → K))) :
    FixedRuling ω l v := span_fixedRuling ω hω.pow_eq_one l v hv

end Paper2.Certificates.DihedralSupport.AtlasRulingFactors

