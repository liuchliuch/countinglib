import Paper2.HeightOne.PhaseCards.Source

/-! Source Lemma 5.10 for an arbitrary original tensor. Chosen projective
representatives are explicit coefficient matrices with nonzero scalar data.
The statement has no network-realizability or safe-binary-language premise.
Every ordered distinct-port contraction and both orientations are retained. -/
namespace Paper2.SourceFaithful.SourceStatements.TypeParityStatement
open Paper2.Tractable Paper2.HeightOne Paper2.HeightOne.PhaseCards
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
open Paper2.HeightOne.GroupSplit.FiniteGroupFacts.ProjectiveCentralizers
open Paper2.EndpointSelfLoop
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

inductive GroupKind
  | cyclic
  | dihedral
  deriving DecidableEq

/-- Rotation tags occur in both groups; reflection tags occur only in D₂N. -/
def RepresentativeIndex (kind : GroupKind) (N : ℕ) :=
  {reflection : Bool // reflection=false ∨ kind=.dihedral} × rootsOfUnity N AlgebraicComplex

/-- One fixed binary representative and its actual nonzero projective scale
for each class of H. Native transfer classes are R_s and Z R_s; their Walsh
forms are D_s and X D_s. -/
structure Representatives (kind : GroupKind) (N : ℕ) where
  binary : RepresentativeIndex kind N → AMat
  scale : RepresentativeIndex kind N → AlgebraicComplex
  scale_ne_zero : ∀r,scale r≠0
  transfer_eq : ∀r,transfer (binary r)=scale r •
    (if r.1.val then (zGL : AMat)*phase r.2.val else phase r.2.val)

def rotationIndex (kind : GroupKind) {N : ℕ} (s : rootsOfUnity N AlgebraicComplex) :
    RepresentativeIndex kind N := (⟨false,Or.inl rfl⟩,s)

/-- Orientation reverses the literal ordered binary coefficient matrix. -/
def orientedBinary {kind : GroupKind} {N : ℕ} (R : Representatives kind N)
    (r : RepresentativeIndex kind N) (orientation : Bool) : AMat :=
  if orientation then (R.binary r).transpose else R.binary r

def contraction {kind : GroupKind} {N : ℕ} {ι : Type} [Fintype ι]
    (R : Representatives kind N) (a b : ι) (hab : a≠b)
    (r : RepresentativeIndex kind N) (orientation : Bool)
    (f : Tensor AlgebraicComplex ι) :=
  card (nativeKernel (orientedBinary R r orientation)) a b hab f

def TensorParity {ι : Type} [Fintype ι] (kind : GroupKind)
    (f : Tensor AlgebraicComplex ι) : Prop :=
  match kind with
  | .cyclic => SupportedOnParity f 0
  | .dihedral => HasParity f

def PrimeFactorParity {ι : Type} [Fintype ι] (kind : GroupKind)
    (f : Tensor AlgebraicComplex ι) : Prop :=
  match kind with
  | .cyclic => PrimeFactorsEven f
  | .dihedral => PrimeFactorsHaveParity f

/-- Literal membership of the binary Walsh transfer in the displayed
projective group: D_s in C_N, and D_s or X D_s in D₂N. -/
def WalshTransferMember (kind : GroupKind) (N : ℕ) (B : AMat) : Prop :=
  (∃s : rootsOfUnity N AlgebraicComplex,∃c : AlgebraicComplex,c≠0 ∧
    walshBinary B*(zGL : AMat)=c • diagonal 1 s.val) ∨
  (kind=.dihedral ∧ ∃s : rootsOfUnity N AlgebraicComplex,∃c : AlgebraicComplex,c≠0 ∧
    walshBinary B*(zGL : AMat)=c • (X*diagonal 1 s.val))

private theorem rotation_even {B : AMat} {s c : AlgebraicComplex}
    (h : walshBinary B*(zGL : AMat)=c • diagonal 1 s) :
    SupportedOnParity (walshCoordinates (binarySignature B)) 0 := by
  rw [walshCoordinates_binary]
  apply binary_diagonal_signature_even
  · have he := congrArg (fun M : AMat=>M false true) h
    simpa [Matrix.mul_apply,zGL,diagonalGL,diagonal] using he
  · have he := congrArg (fun M : AMat=>M true false) h
    simpa [Matrix.mul_apply,zGL,diagonalGL,diagonal] using he

private theorem reflection_odd {B : AMat} {s c : AlgebraicComplex}
    (h : walshBinary B*(zGL : AMat)=c • (X*diagonal 1 s)) :
    SupportedOnParity (walshCoordinates (binarySignature B)) 1 := by
  rw [walshCoordinates_binary]
  apply binary_antidiagonal_signature_odd
  · have he := congrArg (fun M : AMat=>M false false) h
    simpa [Matrix.mul_apply,zGL,diagonalGL,diagonal,X,Signature.disequality] using he
  · have he := congrArg (fun M : AMat=>M true true) h
    simpa [Matrix.mul_apply,zGL,diagonalGL,diagonal,X,Signature.disequality] using he

theorem binary_parity {kind : GroupKind} {N : ℕ} (f : Signature AlgebraicComplex 2)
    (h : WalshTransferMember kind N (tableBinary f)) : TensorParity kind (walshCoordinates f) := by
  rcases h with ⟨s,c,hc,ht⟩ | ⟨hk,s,c,hc,ht⟩
  · have hp := rotation_even ht
    rw [binarySignature_tableBinary] at hp
    cases kind
    · exact hp
    · exact supportedOnParity_hasParity hp
  · subst kind
    have hp := reflection_odd ht
    rw [binarySignature_tableBinary] at hp
    exact supportedOnParity_hasParity hp

theorem high_arity_parity {kind : GroupKind} {N : ℕ}
    (hN : 3≤N) (R : Representatives kind N) {ι : Type} [Fintype ι]
    (hn : 4≤Fintype.card ι) (f : Tensor AlgebraicComplex ι)
    (h : ∀(a b : ι)(hab : a≠b)(r : RepresentativeIndex kind N)(orientation : Bool),
      contraction R a b hab r orientation f≠0 →
      PrimeFactorParity kind (contraction R a b hab r orientation f)) :
    TensorParity kind (walshCoordinates f) := by
  let : NeZero N := ⟨by omega⟩
  obtain ⟨ζ,hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  have ht (s : rootsOfUnity N AlgebraicComplex) :
      transfer (R.binary (rotationIndex kind s))=R.scale (rotationIndex kind s) • phase s.val := by
    simpa only [rotationIndex,Bool.false_eq_true,ite_false] using R.transfer_eq (rotationIndex kind s)
  have hs (s : rootsOfUnity N AlgebraicComplex) : 2*R.scale (rotationIndex kind s)≠0 :=
    mul_ne_zero (by norm_num) (R.scale_ne_zero _)
  have hw (a b : ι) (hab : a≠b) (s : rootsOfUnity N AlgebraicComplex) :
      walshCoordinates (contraction R a b hab (rotationIndex kind s) false f)=
        (2*R.scale (rotationIndex kind s)) •
          HeightOne.plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f) :=
    rotation_card_walsh a b hab f (ht s)
  cases kind
  · apply even_of_root_of_unity_contractions (by omega) N (by omega) ζ hζ (walshCoordinates f)
    intro a b hab s hs'
    let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs'
    have hp : SupportedOnParity
        (walshCoordinates (contraction R a b hab (rotationIndex .cyclic r) false f)) 0 := by
      by_cases hz : contraction R a b hab (rotationIndex .cyclic r) false f=0
      · rw [hz,walsh_zero]
        intro x hx
        exact False.elim (hx rfl)
      · apply even_of_primeFactors _ ?_ hz (h a b hab _ false hz)
        have := remaining_card a b hab
        omega
    rw [hw] at hp
    exact (supportedOnParity_scale_iff _ (hs r) _ 0).mp hp
  · apply hasParity_of_root_of_unity_contractions hn N hN ζ hζ (walshCoordinates f)
    intro a b hab s hs'
    let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs'
    have hp : HasParity
        (walshCoordinates (contraction R a b hab (rotationIndex .dihedral r) false f)) := by
      by_cases hz : contraction R a b hab (rotationIndex .dihedral r) false f=0
      · rw [hz,walsh_zero]
        exact hasParity_zero
      · apply hasParity_of_primeFactors _ ?_ hz (h a b hab _ false hz)
        have := remaining_card a b hab
        omega
    rw [hw] at hp
    exact (hasParity_scale_iff _ (hs r) _).mp hp

/-- Exact printed source Lemma 5.10. At arity two the caller supplies group
membership of the literal Walsh transfer. At larger even arity the hypotheses
range over every chosen representative and both literal orientations. -/
theorem lemma_5_10 {kind : GroupKind} {N n : ℕ} (hN : 3≤N) (_hOdd : Odd N)
    (R : Representatives kind N) (f : Signature AlgebraicComplex n)
    (_hf : f≠0) (hpos : 0<n) (heven : Even n)
    (hbinary : ∀h2 : n=2,WalshTransferMember kind N (tableBinary (h2 ▸ f)))
    (hprime : 4≤n → ∀(a b : Fin n)(hab : a≠b)
      (r : RepresentativeIndex kind N)(orientation : Bool),
      contraction R a b hab r orientation f≠0 →
      PrimeFactorParity kind (contraction R a b hab r orientation f)) :
    TensorParity kind (walshCoordinates f) := by
  by_cases h2 : n=2
  · subst n
    exact binary_parity f (hbinary rfl)
  · have hn : 4≤n := by obtain ⟨k,hk⟩ := heven; omega
    exact high_arity_parity hN R (by simpa using hn) f (hprime hn)

end
end Paper2.SourceFaithful.SourceStatements.TypeParityStatement

