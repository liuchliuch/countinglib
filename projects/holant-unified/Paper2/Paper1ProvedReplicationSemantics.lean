import Paper2.SourceFaithful.OccurrenceInputs
import Paper2.Paper1ProvedReplicationCompiler
import Paper2.Paper1ProvedReplicationOrdinals
import Paper2.Paper1ProvedReplicationValidation
import Mathlib.Data.Fin.Tuple.Basic

/-! Exact finite denotation of a sequence of carrier contexts. The fresh
coordinatewise native-X edges keep one carrier and expose all ordered output
blocks. The multiplier counts context occurrences without dropping the fixed
nonzero closure value. -/
namespace Paper2.Paper1Proved.ReplicationSemantics
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def splitLast (S : Type) (k : ℕ) : (Fin (k+1) → S) ≃ ((Fin k → S) × S) where
  toFun z := (fun i => z i.castSucc,z (Fin.last k))
  invFun p := Fin.lastCases p.2 p.1
  left_inv z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp

def complementWords (r : ℕ) : (Fin r → Bool) ≃ (Fin r → Bool) where
  toFun z := fun i => !(z i)
  invFun z := fun i => !(z i)
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

def splitAppend (S : Type) (m n : ℕ) : (Fin (m+n) → S) ≃ ((Fin m → S) × (Fin n → S)) where
  toFun z := (fun i => z (Fin.castAdd n i),fun i => z (Fin.natAdd m i))
  invFun p := Fin.append p.1 p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

def stateComplement (r k : ℕ) : (Fin k → Fin r → Bool) ≃ (Fin k → Fin r → Bool) where
  toFun z := fun t i => !(z t i)
  invFun z := fun t i => !(z t i)
  left_inv z := by funext t i; simp
  right_inv z := by funext t i; simp

/-- The compiler numbers fresh blocks by r*t+i. A state is the bit at the
false endpoint, hence the complement of `Choice`'s edge choice. -/
def freshStates (r k : ℕ) : (Fin (r*k) → Bool) ≃ (Fin k → Fin r → Bool) :=
  ((Equiv.arrowCongr ((finCongr (Nat.mul_comm r k)).trans finProdFinEquiv.symm)
      (Equiv.refl Bool)).trans (Equiv.curry (Fin k) (Fin r) Bool)).trans (stateComplement r k)

def threeBlocks (m n r k : ℕ) : (Fin (m+n+r*k) → Bool) ≃
    ((Fin m → Bool) × ((Fin n → Bool) × (Fin k → Fin r → Bool))) :=
  (splitAppend Bool (m+n) (r*k)).trans
    ((Equiv.prodCongr (splitAppend Bool m n) (freshStates r k)).trans
      (Equiv.prodAssoc _ _ _))

theorem sum_threeBlocks {K : Type} [AddCommMonoid K] (m n r k : ℕ)
    (f : (Fin m → Bool) → (Fin n → Bool) → (Fin k → Fin r → Bool) → K) :
    (∑ w : Fin (m+n+r*k) → Bool,
      f ((threeBlocks m n r k) w).1 ((threeBlocks m n r k) w).2.1
        ((threeBlocks m n r k) w).2.2) =
      ∑ u : Fin m → Bool, ∑ v : Fin n → Bool, ∑ z : Fin k → Fin r → Bool, f u v z := by
  rw [← (threeBlocks m n r k).symm.sum_comp,Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro u _
  exact Fintype.sum_prod_type _

theorem freshStates_symm_apply (r k : ℕ) (z : Fin k → Fin r → Bool)
    (t : Fin k) (i : Fin r) :
    (freshStates r k).symm z (Fin.cast (Nat.mul_comm k r) (finProdFinEquiv (t,i))) = !(z t i) := by
  simp [freshStates,stateComplement,Equiv.arrowCongr,Equiv.curry]

theorem threeBlocks_source (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (i : Fin m) :
    (threeBlocks m n r k).symm (u,v,z) (Fin.castAdd (r*k) (Fin.castAdd n i)) = u i := by
  simp [threeBlocks,splitAppend]

theorem threeBlocks_closure (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (i : Fin n) :
    (threeBlocks m n r k).symm (u,v,z) (Fin.castAdd (r*k) (Fin.natAdd m i)) = v i := by
  simp [threeBlocks,splitAppend]

theorem threeBlocks_fresh (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (t : Fin k) (i : Fin r) :
    (threeBlocks m n r k).symm (u,v,z)
      (Fin.natAdd (m+n) (Fin.cast (Nat.mul_comm k r) (finProdFinEquiv (t,i)))) = !(z t i) := by
  simp only [threeBlocks,Equiv.symm_trans_apply,Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_symm,Equiv.prodCongr_apply,splitAppend,Equiv.coe_fn_symm_mk,
    Fin.append_right]
  exact freshStates_symm_apply r k z t i

def extendLast {S : Type} {k : ℕ} (p : S) (z : Fin k → S) : Fin (k+1) → S :=
  Fin.lastCases p z

@[simp] theorem extendLast_last {S : Type} {k : ℕ} (p : S) (z : Fin k → S) :
    extendLast p z (Fin.last k) = p := by simp [extendLast]

@[simp] theorem extendLast_castSucc {S : Type} {k : ℕ} (p : S) (z : Fin k → S) (i : Fin k) :
    extendLast p z i.castSucc = z i := by simp [extendLast]

section Chain
variable {K : Type} [CommSemiring K] {r s : ℕ}
variable (g : Signature K r)
variable (T : (Fin r → Bool) → (Fin r → Bool) → (Fin s → Bool) → K)

/-- Each new context receives the complement of the previous exposed carrier
word. This is the actual orientation of the fresh native-X edge occurrences. -/
def chainProduct : (k : ℕ) → (Fin r → Bool) →
    (Fin k → Fin s → Bool) → (Fin k → Fin r → Bool) → K
  | 0,p,_,_ => g p
  | k+1,p,y,z => chainProduct k (z (Fin.last k))
      (fun i => y i.castSucc) (fun i => z i.castSucc) *
      T (fun i => !(z (Fin.last k) i)) p (y (Fin.last k))

theorem lastCases_split (S : Type) (k : ℕ) (z : Fin (k+1) → S) :
    extendLast (z (Fin.last k)) (fun i => z i.castSucc) = z :=
  (splitLast S k).left_inv z

/-- The recursion is exactly the product of contexts on the ordered chain,
with output p after its last fresh carrier block. -/
theorem chainProduct_explicit (k : ℕ) (p : Fin r → Bool)
    (y : Fin k → Fin s → Bool) (z : Fin k → Fin r → Bool) :
    chainProduct g T k p y z =
      g ((extendLast p z) 0) * ∏ i : Fin k,
        T (fun j => !(z i j)) ((extendLast p z) i.succ) (y i) := by
  induction k generalizing p with
  | zero =>
    change g p = g (extendLast p z (Fin.last 0)) * 1
    rw [extendLast_last,mul_one]
  | succ k ih =>
    rw [chainProduct,ih,lastCases_split,Fin.prod_univ_castSucc]
    rw [← mul_assoc]
    congr 1
    · congr 1
      · congr 1
        change z 0 = extendLast p z (Fin.castSucc 0)
        rw [extendLast_castSucc]
      · apply Finset.prod_congr rfl
        intro i _
        congr 1
        change z i.succ = extendLast p z i.succ.castSucc
        rw [extendLast_castSucc]
    · congr 1
      change p = extendLast p z (Fin.last (k+1))
      rw [extendLast_last]

theorem chain_sum (h : Signature K s) (c : K)
    (step : ∀ p y, (∑ a : Fin r → Bool, g (fun i => !(a i)) * T a p y) = c*g p*h y)
    (k : ℕ) (p : Fin r → Bool) (y : Fin k → Fin s → Bool) :
    (∑ z : Fin k → Fin r → Bool, chainProduct g T k p y z) =
      c^k * g p * ∏ i : Fin k, h (y i) := by
  induction k generalizing p with
  | zero => simp [chainProduct]
  | succ k ih =>
    rw [← (splitLast (Fin r → Bool) k).symm.sum_comp, Fintype.sum_prod_type]
    simp only [splitLast,Equiv.coe_fn_symm_mk,chainProduct,
      Fin.lastCases_last,Fin.lastCases_castSucc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,ih]
    have hs : (∑ a : Fin r → Bool, g a * T (fun i => !(a i)) p (y (Fin.last k))) =
        c*g p*h (y (Fin.last k)) := by
      rw [← (complementWords r).sum_comp]
      simpa only [complementWords,Equiv.coe_fn_mk,Bool.not_not] using step p (y (Fin.last k))
    have he : (∑ a : Fin r → Bool,
        c^k * g a * (∏ i : Fin k, h (y i.castSucc)) *
          T (fun i => !(a i)) p (y (Fin.last k))) =
        c^k * (∏ i : Fin k, h (y i.castSucc)) *
          ∑ a : Fin r → Bool, g a * T (fun i => !(a i)) p (y (Fin.last k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ac_rfl
    rw [he,hs,Fin.prod_univ_castSucc,pow_succ]
    ac_rfl

end Chain

def contextTable {L : Language} {r s : ℕ} {g : Signature AlgebraicComplex r}
    {h : Signature AlgebraicComplex s} (C : CarrierContext L g h)
    (a p : Fin r → Bool) (y : Fin s → Bool) : AlgebraicComplex :=
  C.graph.denote (Fin.append a (Fin.append p y))

theorem context_chain_sum {L : Language} {r s : ℕ}
    {g : Signature AlgebraicComplex r} {h : Signature AlgebraicComplex s}
    (C : CarrierContext L g h) (k : ℕ) (p : Fin r → Bool)
    (y : Fin k → Fin s → Bool) :
    (∑ z : Fin k → Fin r → Bool, chainProduct g (contextTable C) k p y z) =
      C.scalar^k * g p * ∏ i : Fin k, h (y i) :=
  chain_sum g (contextTable C) h C.scalar C.step k p y

section Raw
open Holant.Complexity Holant.Complexity.RawClosedNetwork
open Holant.Complexity.UniversalPairReduction.Surgery
variable {K : Type} [CommSemiring K]

def word (r : ℕ) (bits : List Bool) : Fin r → Bool := fun i => bits.getD i.val false

def markedTable {r : ℕ} (F : Choice.Table K) (g : Signature K r) : Choice.Table K :=
  fun label bits => if label=0 then g (word r bits) else F label bits

def contextWord {r s : ℕ}
    (T : (Fin r → Bool) → (Fin r → Bool) → (Fin s → Bool) → K)
    (bits : List Bool) : K :=
  T (fun i => bits.getD i.val false) (fun i => bits.getD (r+i.val) false)
    (fun i => bits.getD (r+r+i.val) false)

def targetTable {r s : ℕ} (label : ℕ) (F : Choice.Table K) (g : Signature K r)
    (T : (Fin r → Bool) → (Fin r → Bool) → (Fin s → Bool) → K) : Choice.Table K :=
  fun j bits => if j=label then contextWord T bits else markedTable F g j bits

def rowWord (r : ℕ) (c : ℕ → Bool) (row : RawVertex) : Fin r → Bool :=
  word r (row.2.map (Choice.bit c))

def unmarked (rows : List RawVertex) : List RawVertex :=
  rows.filter (fun row => !(row.1 == 0))

theorem weight_append (F : Choice.Table K) (c : ℕ → Bool) (a b : List RawVertex) :
    Choice.weight F c (a++b) = Choice.weight F c a * Choice.weight F c b := by
  simp [Choice.weight]

theorem weight_marked_split (F : Choice.Table K) (c : ℕ → Bool) (rows : List RawVertex) :
    Choice.weight F c rows = Choice.weight F c (unmarked rows) *
      Choice.weight F c (rows.filter (fun row => row.1 == 0)) := by
  induction rows with
  | nil => simp [Choice.weight,unmarked]
  | cons a rows ih =>
    by_cases ha : a.1=0
    · simpa [Choice.weight,unmarked,ha,mul_assoc,mul_comm,mul_left_comm] using
        congrArg (fun z => Choice.rowValue F c a*z) ih
    · simpa [Choice.weight,unmarked,ha,mul_assoc] using
        congrArg (fun z => Choice.rowValue F c a*z) ih

theorem extend_source (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (i : ℕ) (hi : i<m) :
    Choice.extend ((threeBlocks m n r k).symm (u,v,z)) i = Choice.extend u i := by
  simp only [Choice.extend,dite_eq_left (show i<m+n+r*k by omega),dite_eq_left hi]
  exact threeBlocks_source m n r k u v z ⟨i,hi⟩

theorem extend_closure (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (i : ℕ) (hi : i<n) :
    Choice.extend ((threeBlocks m n r k).symm (u,v,z)) (m+i) = Choice.extend v i := by
  simp only [Choice.extend,dite_eq_left (show m+i<m+n+r*k by omega),dite_eq_left hi]
  exact threeBlocks_closure m n r k u v z ⟨i,hi⟩

theorem extend_fresh (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (t : Fin k) (i : Fin r) :
    Choice.extend ((threeBlocks m n r k).symm (u,v,z)) (m+n+r*t.val+i.val) = !(z t i) := by
  have hb : r*t.val+i.val<r*k := by
    simpa [Nat.mul_comm,Nat.add_comm,finProdFinEquiv] using (finProdFinEquiv (t,i)).isLt
  simp only [Choice.extend,dite_eq_left (show m+n+r*t.val+i.val<m+n+r*k by omega)]
  have h := threeBlocks_fresh m n r k u v z t i
  convert h using 1
  apply congrArg ((threeBlocks m n r k).symm (u,v,z))
  apply Fin.ext
  simp [finProdFinEquiv,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem bit_source (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (p : RawEndpoint) (hp : p.1<m) :
    Choice.bit (Choice.extend ((threeBlocks m n r k).symm (u,v,z))) p =
      Choice.bit (Choice.extend u) p := by
  simp [Choice.bit,extend_source m n r k u v z p.1 hp]

theorem bit_closure (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (p : RawEndpoint) (hp : p.1<n) :
    Choice.bit (Choice.extend ((threeBlocks m n r k).symm (u,v,z))) (ReplicationCompiler.shift m p) =
      Choice.bit (Choice.extend v) p := by
  simp [Choice.bit,ReplicationCompiler.shift,extend_closure m n r k u v z p.1 hp]

theorem bits_source (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (ports : List RawEndpoint) (hp : ∀ p∈ports,p.1<m) :
    ports.map (Choice.bit (Choice.extend ((threeBlocks m n r k).symm (u,v,z)))) =
      ports.map (Choice.bit (Choice.extend u)) := by
  apply List.map_congr_left
  intro p hp'
  exact bit_source m n r k u v z p (hp p hp')

theorem bits_closure (m n r k : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (z : Fin k → Fin r → Bool) (ports : List RawEndpoint) (hp : ∀ p∈ports,p.1<n) :
    (ports.map (ReplicationCompiler.shift m)).map
      (Choice.bit (Choice.extend ((threeBlocks m n r k).symm (u,v,z)))) =
      ports.map (Choice.bit (Choice.extend v)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp'
  exact bit_closure m n r k u v z p (hp p hp')


omit [CommSemiring K] in
theorem contextWord_append {r s : ℕ}
    (T : (Fin r → Bool) → (Fin r → Bool) → (Fin s → Bool) → K)
    (a p : Fin r → Bool) (bits : List Bool) :
    contextWord T (List.ofFn a ++ (List.ofFn p ++ bits)) = T a p (word s bits) := by
  unfold contextWord word
  congr 1
  · funext i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact i.isLt)]
    simp
  · funext i
    rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact i.isLt)]
    simp
  · funext i
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),List.length_ofFn]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn]
    congr 1; omega

theorem extendLast_succ_last {S : Type} {k : ℕ} (p : S) (z : Fin k → S)
    (t : Fin k) (ht : t.val+1=k) : extendLast p z t.succ = p := by
  have he : t.succ=Fin.last k := Fin.ext ht
  rw [he,extendLast_last]

theorem extendLast_succ_not_last {S : Type} {k : ℕ} (p : S) (z : Fin k → S)
    (t : Fin k) (ht : t.val+1≠k) :
    extendLast p z t.succ = z ⟨t.val+1,by omega⟩ := by
  have he : t.succ=(⟨t.val+1,by omega⟩ : Fin k).castSucc := Fin.ext rfl
  rw [he,extendLast_castSucc]

theorem bits_carrierA (D : ReplicationCompiler.Data) (m k : ℕ)
    (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (t : Fin k) :
    ((List.finRange D.gArity).map (fun i => ReplicationCompiler.carrierA D m t.val i.val)).map
      (Choice.bit (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))) =
        List.ofFn (fun i => !(z t i)) := by
  rw [List.map_map,List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  simp [ReplicationCompiler.carrierA,Choice.bit,extend_fresh]

theorem bits_carrierP (D : ReplicationCompiler.Data) (m k : ℕ)
    (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (t : Fin k)
    (hseed : D.seedPorts.length=D.gArity)
    (hp : ∀ p∈D.seedPorts,p.1<D.closure.edges.length) :
    ((List.finRange D.gArity).map (fun i => ReplicationCompiler.carrierP D m k t.val i.val)).map
      (Choice.bit (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))) =
        List.ofFn ((extendLast (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) z) t.succ) := by
  rw [List.map_map,List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  change Choice.bit _ (ReplicationCompiler.carrierP D m k t.val i.val) = _
  by_cases ht : t.val+1=k
  · rw [ReplicationCompiler.carrierP,ite_eq_left ht,extendLast_succ_last _ _ _ ht]
    rw [bit_closure _ _ _ _ _ _ _ _ (hp _ (by
      rw [List.getD_eq_getElem _ _ (by rw [hseed]; exact i.isLt)]
      exact List.getElem_mem _))]
    unfold word
    rw [List.getD_eq_getElem (D.seedPorts.map (Choice.bit (Choice.extend v))) false
      (by simpa only [List.length_map,hseed] using i.isLt),List.getElem_map]
    rw [List.getD_eq_getElem D.seedPorts (0,false) (by rw [hseed]; exact i.isLt)]
  · rw [ReplicationCompiler.carrierP,ite_eq_right ht,extendLast_succ_not_last _ _ _ ht]
    simp only [Choice.bit,Bool.false_eq_true,↓reduceIte]
    rw [extend_fresh _ _ _ _ _ _ _ (⟨t.val+1,by omega⟩ : Fin k) i]
    simp


omit [CommSemiring K] in
theorem sourceRow_marked (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (m k : ℕ) (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (t : Fin k) (row : RawVertex)
    (hz : row.1=0) (hs : D.seedPorts.length=D.gArity)
    (hseed : ∀ p∈D.seedPorts,p.1<D.closure.edges.length) (hp : ∀ p∈row.2,p.1<m) :
    Choice.rowValue (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))
      (ReplicationCompiler.sourceRow D m k t.val row) =
        T (fun i => !(z t i))
          (extendLast (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) z t.succ)
          (rowWord D.hArity (Choice.extend u) row) := by
  simp only [ReplicationCompiler.sourceRow,hz,↓reduceIte,Choice.rowValue,targetTable]
  simp only [List.map_append]
  rw [bits_carrierA,bits_carrierP _ _ _ _ _ _ _ hs hseed,bits_source _ _ _ _ _ _ _ _ hp]
  exact contextWord_append T _ _ _

omit [CommSemiring K] in
theorem sourceRow_unmarked (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (m k : ℕ) (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (t : ℕ) (row : RawVertex)
    (hz : row.1≠0) (hl : row.1<D.count+1) (hp : ∀ p∈row.2,p.1<m) :
    Choice.rowValue (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))
      (ReplicationCompiler.sourceRow D m k t row) = Choice.rowValue F (Choice.extend u) row := by
  simp only [ReplicationCompiler.sourceRow,Choice.rowValue,targetTable,
    ite_eq_right (show row.1≠D.count+1 by omega),markedTable,ite_eq_right hz]
  rw [bits_source _ _ _ _ _ _ _ _ hp]

omit [CommSemiring K] in
theorem closureRow_unmarked (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (m k : ℕ) (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (row : RawVertex)
    (hz : row.1≠0) (hl : row.1<D.count+1)
    (hp : ∀ p∈row.2,p.1<D.closure.edges.length) :
    Choice.rowValue (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))
      (ReplicationCompiler.closureRow D m k row) = Choice.rowValue F (Choice.extend v) row := by
  simp only [ReplicationCompiler.closureRow,hz,false_and,↓reduceIte,Choice.rowValue,targetTable,
    ite_eq_right (show row.1≠D.count+1 by omega),markedTable]
  rw [bits_closure _ _ _ _ _ _ _ _ hp]

omit [CommSemiring K] in
theorem closureRow_marked (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (m k : ℕ) (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) (row : RawVertex)
    (hz : row.1=0) (hrow : row.2=D.seedPorts)
    (hp : ∀ p∈D.seedPorts,p.1<D.closure.edges.length) :
    Choice.rowValue (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))
      (ReplicationCompiler.closureRow D m k row) =
        g (extendLast (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) z 0) := by
  cases k with
  | zero =>
    simp only [ReplicationCompiler.closureRow,hz,ne_eq,not_true_eq_false,and_false,
      ↓reduceIte,Choice.rowValue,targetTable,Nat.zero_ne_add_one,markedTable]
    simp only [hrow]
    rw [bits_closure _ _ _ _ _ _ _ _ hp]
    change g _ = g (extendLast _ z (Fin.last 0))
    rw [extendLast_last]
  | succ k =>
    simp only [ReplicationCompiler.closureRow,hz,↓reduceIte,
      Choice.rowValue,targetTable,Nat.zero_ne_add_one,markedTable]
    change g (word D.gArity (((List.finRange D.gArity).map
      (fun i => (m+D.closure.edges.length+i.val,false))).map
       (Choice.bit (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity (k+1)).symm (u,v,z)))))) = _
    rw [List.map_map]
    have hb : (List.finRange D.gArity).map (fun i =>
        Choice.bit (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity (k+1)).symm (u,v,z)))
          (m+D.closure.edges.length+i.val,false)) = List.ofFn (z 0) := by
      rw [List.ofFn_eq_map]
      apply List.map_congr_left
      intro i _
      simp only [Choice.bit,Bool.false_eq_true,↓reduceIte]
      have he := extend_fresh m D.closure.edges.length D.gArity (k+1) u v z 0 i
      simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at he
      rw [he,Bool.not_not]
    simp only [Function.comp_def]
    rw [hb]
    have hw : word D.gArity (List.ofFn (z 0))=z 0 := by
      funext i
      simp [word]
    rw [hw]
    congr 1
    change z 0 = extendLast _ z ((0 : Fin (k+1)).castSucc)
    rw [extendLast_castSucc]

theorem before_eq (D : ReplicationCompiler.Data) (x : ReplicationCompiler.Input D)
    (v : Fin x.val.vertices.length) :
    ReplicationCompiler.before D ⟨x,v⟩ =
      ((x.val.vertices.take v.val).filter (fun row => row.1 == 0)).length := by
  exact Holant.Complexity.FixedGadgetSubstitution.Compiler.indicator_sum 0 _


theorem wf_label {q : RawClosedNetwork} {a : ℕ → ℕ} {l b : ℕ}
    (hw : q.WellFormed l b a) (row : RawVertex) (hm : row∈q.vertices) : row.1<l := by
  obtain ⟨v,hv⟩ := List.mem_iff_get.mp hm
  rw [← hv]
  exact (hw.1 v).1

theorem wf_port {q : RawClosedNetwork} {a : ℕ → ℕ} {l b : ℕ}
    (hw : q.WellFormed l b a) (row : RawVertex) (hm : row∈q.vertices)
    (p : RawEndpoint) (hp : p∈row.2) : p.1<q.edges.length := by
  apply (q.mem_expectedEndpoints_iff p).mp
  apply hw.2.2.mem_iff.mp
  apply List.mem_flatten.mpr
  exact ⟨row.2,List.mem_map.mpr ⟨row,hm,rfl⟩,hp⟩

theorem prod_zero_split (rows : List RawVertex) (W : RawVertex → K) :
    (rows.map W).prod = ((unmarked rows).map W).prod *
      ((rows.filter (fun row => row.1==0)).map W).prod := by
  induction rows with
  | nil => simp [unmarked]
  | cons a rows ih =>
    by_cases ha : a.1=0
    · simpa [unmarked,ha,mul_assoc,mul_comm,mul_left_comm] using
        congrArg (fun z => W a*z) ih
    · simpa [unmarked,ha,mul_assoc] using congrArg (fun z => W a*z) ih

open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

theorem zero_ports (D : ReplicationCompiler.Data)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (row : RawVertex) (hm : row∈D.closure.vertices) (hz : row.1=0) : row.2=D.seedPorts := by
  obtain ⟨seed,he⟩ := List.length_eq_one_iff.mp hc
  have hm' : row∈D.closure.vertices.filter (fun row => row.1==0) :=
    List.mem_filter.mpr ⟨hm,by simpa using hz⟩
  rw [he,List.mem_singleton] at hm'
  subst row
  simpa [RawGrouping.selected,he] using hs

theorem seed_bound (D : ReplicationCompiler.Data)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts) :
    ∀ p∈D.seedPorts,p.1<D.closure.edges.length := by
  obtain ⟨v,hz,hv⟩ := ReplicationCompiler.unique_seed D.closure.vertices hc
  have he : D.seedPorts=(D.closure.vertices.get v).2 := hs.symm.trans hv
  intro p hp
  rw [he] at hp
  exact wf_port hw _ (List.get_mem _ _) p hp

theorem closure_weight (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (m k : ℕ) (u : Fin m → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin k → Fin D.gArity → Bool) :
    Choice.weight (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks m D.closure.edges.length D.gArity k).symm (u,v,z)))
      (D.closure.vertices.map (ReplicationCompiler.closureRow D m k)) =
        Choice.weight F (Choice.extend v) (unmarked D.closure.vertices) *
        g (extendLast (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) z 0) := by
  unfold Choice.weight
  rw [List.map_map,prod_zero_split]
  congr 1
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row hm
    have hh := List.mem_filter.mp hm
    have hz : row.1≠0 := by simpa using hh.2
    exact closureRow_unmarked D F g T m k u v z row hz
      (wf_label hw row hh.1) (wf_port hw row hh.1)
  · obtain ⟨row,he⟩ := List.length_eq_one_iff.mp hc
    have hm : row∈D.closure.vertices := (List.mem_filter.mp (by rw [he]; simp)).1
    have hz : row.1=0 := by
      have := (List.mem_filter.mp (show row∈D.closure.vertices.filter (fun row => row.1==0) by rw [he]; simp)).2
      simpa using this
    rw [he,List.map_singleton,List.prod_singleton]
    exact closureRow_marked D F g T m k u v z row hz (zero_ports D hc hs row hm hz)
      (seed_bound D hw hc hs)

def markedWords (s : ℕ) (rows : List RawVertex) (c : ℕ → Bool) :
    Fin (ReplicationCompiler.count rows) → Fin s → Bool :=
  fun j => rowWord s c ((rows.filter (fun row : RawVertex => row.1==0)).get j)

theorem source_weight (D : ReplicationCompiler.Data) (x : ReplicationCompiler.Input D)
    (F : Choice.Table K) (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity)
    (u : Fin x.val.edges.length → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin (ReplicationCompiler.count x.val.vertices) → Fin D.gArity → Bool) :
    Choice.weight (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks x.val.edges.length D.closure.edges.length D.gArity
        (ReplicationCompiler.count x.val.vertices)).symm (u,v,z)))
      ((List.finRange x.val.vertices.length).map (fun w => ReplicationCompiler.sourceRow D
        x.val.edges.length (ReplicationCompiler.count x.val.vertices) (ReplicationCompiler.before D ⟨x,w⟩)
        (x.val.vertices.get w))) =
      Choice.weight F (Choice.extend u) (unmarked x.val.vertices) *
        ∏ j : Fin (ReplicationCompiler.count x.val.vertices),
          T (fun i => !(z j i))
            (extendLast (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) z j.succ)
            (markedWords D.hArity x.val.vertices (Choice.extend u) j) := by
  let k := ReplicationCompiler.count x.val.vertices
  let p := word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))
  let B := Choice.rowValue F (Choice.extend u)
  let A : ℕ → RawVertex → K := fun t row => if ht : t<k then
    T (fun i => !(z ⟨t,ht⟩ i)) (extendLast p z (⟨t,ht⟩ : Fin k).succ)
      (rowWord D.hArity (Choice.extend u) row) else 0
  have he : ((List.finRange x.val.vertices.length).map (fun w =>
      Choice.rowValue (targetTable (D.count+1) F g T)
        (Choice.extend ((threeBlocks x.val.edges.length D.closure.edges.length D.gArity k).symm (u,v,z)))
        (ReplicationCompiler.sourceRow D x.val.edges.length k (ReplicationCompiler.before D ⟨x,w⟩)
          (x.val.vertices.get w)))) =
      ((List.finRange x.val.vertices.length).map (fun w =>
        if (x.val.vertices.get w).1==0 then
          A (((x.val.vertices.take w.val).filter (fun row => row.1==0)).length) (x.val.vertices.get w)
        else B (x.val.vertices.get w))) := by
    apply List.map_congr_left
    intro w _
    rw [before_eq]
    by_cases hz : (x.val.vertices.get w).1=0
    · have ht : ((x.val.vertices.take w.val).filter (fun row => row.1==0)).length<k :=
        ReplicationOrdinals.marked_rank_lt _ _ w (by simpa using hz)
      simp only [hz,beq_self_eq_true,↓reduceIte,A,dite_eq_left ht]
      exact sourceRow_marked D F g T _ k u v z ⟨_,ht⟩ _ hz hl
        (seed_bound D hw hc hs) (wf_port x.property _ (List.get_mem _ _))
    · simp only [Bool.beq_eq_decide_eq,decide_eq_false hz]
      exact sourceRow_unmarked D F g T _ k u v z _ _ hz (x.property.1 w).1
        (wf_port x.property _ (List.get_mem _ _))
  unfold Choice.weight
  rw [List.map_map]
  simp only [Function.comp_def]
  rw [he,ReplicationOrdinals.indexed_marked_prod (fun row : RawVertex => row.1==0) x.val.vertices B A]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [A,k,p,ReplicationCompiler.count,dite_eq_left j.isLt]
  rfl


theorem marked_weight {r : ℕ} (F : Choice.Table K) (g : Signature K r)
    (rows : List RawVertex) (c : ℕ → Bool) :
    Choice.weight (markedTable F g) c rows = Choice.weight F c (unmarked rows) *
      ∏ j : Fin (ReplicationCompiler.count rows),g (markedWords r rows c j) := by
  unfold Choice.weight
  rw [prod_zero_split]
  congr 1
  · apply congrArg List.prod
    apply List.map_congr_left
    intro row hm
    have hz : row.1≠0 := by simpa [unmarked] using (List.mem_filter.mp hm).2
    simp [Choice.rowValue,markedTable,hz]
  · rw [← List.prod_ofFn,← List.ofFn_getElem_eq_map]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    have hz : ((rows.filter (fun row => row.1==0)).get j).1=0 := by
      have hm := List.get_mem (rows.filter (fun row => row.1==0)) j
      simpa using (List.mem_filter.mp hm).2
    simp only [List.get_eq_getElem] at hz
    simp [Choice.rowValue,markedTable,hz,markedWords,rowWord]

theorem original_closure_weight (D : ReplicationCompiler.Data) (F : Choice.Table K)
    (g : Signature K D.gArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (v : Fin D.closure.edges.length → Bool) :
    Choice.weight (markedTable F g) (Choice.extend v) D.closure.vertices =
      Choice.weight F (Choice.extend v) (unmarked D.closure.vertices) *
        g (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) := by
  rw [marked_weight]
  congr 1
  obtain ⟨row,he⟩ := List.length_eq_one_iff.mp hc
  have hp : row.2=D.seedPorts := by simpa [RawGrouping.selected,he] using hs
  change (∏ j : Fin (D.closure.vertices.filter (fun row => row.1==0)).length,
    g (rowWord D.gArity (Choice.extend v) ((D.closure.vertices.filter (fun row => row.1==0)).get j))) = _
  rw [he]
  simp [rowWord,hp]

theorem query_weight (D : ReplicationCompiler.Data) (x : ReplicationCompiler.Input D)
    (F : Choice.Table K) (g : Signature K D.gArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity)
    (u : Fin x.val.edges.length → Bool) (v : Fin D.closure.edges.length → Bool)
    (z : Fin (ReplicationCompiler.count x.val.vertices) → Fin D.gArity → Bool) :
    Choice.weight (targetTable (D.count+1) F g T)
      (Choice.extend ((threeBlocks x.val.edges.length D.closure.edges.length D.gArity
        (ReplicationCompiler.count x.val.vertices)).symm (u,v,z))) (ReplicationCompiler.query D x).vertices =
      Choice.weight F (Choice.extend u) (unmarked x.val.vertices) *
      Choice.weight F (Choice.extend v) (unmarked D.closure.vertices) *
        chainProduct g T (ReplicationCompiler.count x.val.vertices)
          (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v))))
          (markedWords D.hArity x.val.vertices (Choice.extend u)) z := by
  change Choice.weight _ _ (_++_) = _
  rw [weight_append,closure_weight D F g T hw hc hs,source_weight D x F g T hw hc hs hl,
    chainProduct_explicit]
  ac_rfl

/-- The actual emitted graph evaluates to exactly c^k times the fixed closure
and the input partition. All fresh choices are summed, including zero arities
and the zero-occurrence input case. -/
theorem query_partition (D : ReplicationCompiler.Data) (x : ReplicationCompiler.Input D)
    (F : Choice.Table K) (g : Signature K D.gArity) (h : Signature K D.hArity)
    (T : (Fin D.gArity → Bool) → (Fin D.gArity → Bool) → (Fin D.hArity → Bool) → K)
    (c : K)
    (step : ∀ p y,(∑ a : Fin D.gArity → Bool,g (fun i => !(a i))*T a p y)=c*g p*h y)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity) :
    Choice.evaluate (targetTable (D.count+1) F g T) (ReplicationCompiler.query D x).edges.length
        (ReplicationCompiler.query D x).vertices =
      c^(ReplicationCompiler.count x.val.vertices) *
        Choice.evaluate (markedTable F g) D.closure.edges.length D.closure.vertices *
        Choice.evaluate (markedTable F h) x.val.edges.length x.val.vertices := by
  unfold Choice.evaluate
  rw [ReplicationCompiler.query_edge_length]
  rw [← (threeBlocks x.val.edges.length D.closure.edges.length D.gArity
    (ReplicationCompiler.count x.val.vertices)).symm.sum_comp,Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,query_weight D x F g T hw hc hs hl]
  simp_rw [← Finset.mul_sum,chain_sum g T h c step]
  have he : ∀ (u : Fin x.val.edges.length → Bool) (v : Fin D.closure.edges.length → Bool),
    Choice.weight F (Choice.extend u) (unmarked x.val.vertices) *
      Choice.weight F (Choice.extend v) (unmarked D.closure.vertices) *
      (c^(ReplicationCompiler.count x.val.vertices) *
        g (word D.gArity (D.seedPorts.map (Choice.bit (Choice.extend v)))) *
        ∏ j : Fin (ReplicationCompiler.count x.val.vertices),h (markedWords D.hArity x.val.vertices (Choice.extend u) j)) =
      c^(ReplicationCompiler.count x.val.vertices) *
        Choice.weight (markedTable F g) (Choice.extend v) D.closure.vertices *
        Choice.weight (markedTable F h) (Choice.extend u) x.val.vertices := by
    intro u v
    rw [original_closure_weight D F g hc hs,marked_weight]
    ac_rfl
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [← Finset.mul_sum]


omit [CommSemiring K] in
/-- The list slices use exactly the context graph's ordered A, P, Y ports. -/
theorem contextWord_signature {r s : ℕ} (H : Signature K (r+(r+s))) (bits : List Bool) :
    contextWord (fun a p y => H (Fin.append a (Fin.append p y))) bits =
      H (word (r+(r+s)) bits) := by
  simp only [contextWord]
  apply congrArg H
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [word]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [word]
    · simp [word,Nat.add_assoc]

/-- Closed instance specialization to the actual algebraic carrier context. -/
theorem context_query_partition (D : ReplicationCompiler.Data) (x : ReplicationCompiler.Input D)
    (L : Language) (F : Choice.Table AlgebraicComplex)
    (g : Signature AlgebraicComplex D.gArity) (h : Signature AlgebraicComplex D.hArity)
    (C : CarrierContext L g h)
    (hw : D.closure.WellFormed (D.count+1) 1 D.carrierArity)
    (hc : ReplicationCompiler.count D.closure.vertices=1)
    (hs : RawGrouping.selected 0 D.closure.vertices=D.seedPorts)
    (hl : D.seedPorts.length=D.gArity) :
    Choice.evaluate (targetTable (D.count+1) F g (contextTable C))
        (ReplicationCompiler.query D x).edges.length (ReplicationCompiler.query D x).vertices =
      C.scalar^(ReplicationCompiler.count x.val.vertices) *
        Choice.evaluate (markedTable F g) D.closure.edges.length D.closure.vertices *
        Choice.evaluate (markedTable F h) x.val.edges.length x.val.vertices :=
  query_partition D x F g h (contextTable C) C.scalar C.step hw hc hs hl

end Raw
end
end Paper2.Paper1Proved.ReplicationSemantics
