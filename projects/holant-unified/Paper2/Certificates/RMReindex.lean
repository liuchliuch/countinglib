import Paper2.ReedMuller

/-! Explicit affine port bijections carrying the canonical ordered pair
000,001 to any chosen ordered pair p,q. Both maps and all affine-code claims
are checked in the kernel. This upgrades the fixed-port RM Bell identity to
the every-pair version used by the occurrence reduction. -/
namespace Paper2.ReedMuller

def pairOrder : Fin 8 → Fin 8 → Fin 8 → Fin 8 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 1, 3, 4, 6, 5, 7], ![0, 3, 1, 2, 4, 7, 5, 6], ![0, 4, 1, 5, 2, 6, 3, 7], ![0, 5, 1, 4, 2, 7, 3, 6], ![0, 6, 1, 7, 2, 4, 3, 5], ![0, 7, 1, 6, 2, 5, 3, 4]], ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 2, 0, 3, 5, 6, 4, 7], ![1, 3, 0, 2, 5, 7, 4, 6], ![1, 4, 0, 5, 3, 6, 2, 7], ![1, 5, 0, 4, 3, 7, 2, 6], ![1, 6, 0, 7, 3, 4, 2, 5], ![1, 7, 0, 6, 3, 5, 2, 4]], ![![2, 0, 3, 1, 6, 4, 7, 5], ![2, 1, 3, 0, 6, 5, 7, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![2, 4, 3, 5, 0, 6, 1, 7], ![2, 5, 3, 4, 0, 7, 1, 6], ![2, 6, 3, 7, 0, 4, 1, 5], ![2, 7, 3, 6, 0, 5, 1, 4]], ![![3, 0, 2, 1, 7, 4, 6, 5], ![3, 1, 2, 0, 7, 5, 6, 4], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 4, 2, 5, 1, 6, 0, 7], ![3, 5, 2, 4, 1, 7, 0, 6], ![3, 6, 2, 7, 1, 4, 0, 5], ![3, 7, 2, 6, 1, 5, 0, 4]], ![![4, 0, 5, 1, 6, 2, 7, 3], ![4, 1, 5, 0, 6, 3, 7, 2], ![4, 2, 5, 3, 6, 0, 7, 1], ![4, 3, 5, 2, 6, 1, 7, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![4, 6, 5, 7, 0, 2, 1, 3], ![4, 7, 5, 6, 0, 3, 1, 2]], ![![5, 0, 4, 1, 7, 2, 6, 3], ![5, 1, 4, 0, 7, 3, 6, 2], ![5, 2, 4, 3, 7, 0, 6, 1], ![5, 3, 4, 2, 7, 1, 6, 0], ![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![5, 6, 4, 7, 1, 2, 0, 3], ![5, 7, 4, 6, 1, 3, 0, 2]], ![![6, 0, 7, 1, 4, 2, 5, 3], ![6, 1, 7, 0, 4, 3, 5, 2], ![6, 2, 7, 3, 4, 0, 5, 1], ![6, 3, 7, 2, 4, 1, 5, 0], ![6, 4, 7, 5, 2, 0, 3, 1], ![6, 5, 7, 4, 2, 1, 3, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1]], ![![7, 0, 6, 1, 5, 2, 4, 3], ![7, 1, 6, 0, 5, 3, 4, 2], ![7, 2, 6, 3, 5, 0, 4, 1], ![7, 3, 6, 2, 5, 1, 4, 0], ![7, 4, 6, 5, 3, 0, 2, 1], ![7, 5, 6, 4, 3, 1, 2, 0], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7]]]

def pairOrderInv : Fin 8 → Fin 8 → Fin 8 → Fin 8 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 3, 1, 4, 6, 7, 5], ![0, 2, 4, 6, 1, 3, 5, 7], ![0, 2, 4, 6, 3, 1, 7, 5], ![0, 2, 4, 6, 5, 7, 1, 3], ![0, 2, 4, 6, 7, 5, 3, 1]], ![![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 0, 1, 3, 6, 4, 5, 7], ![2, 0, 3, 1, 6, 4, 7, 5], ![2, 0, 6, 4, 1, 3, 5, 7], ![2, 0, 6, 4, 3, 1, 7, 5], ![2, 0, 6, 4, 5, 7, 1, 3], ![2, 0, 6, 4, 7, 5, 3, 1]], ![![1, 3, 0, 2, 5, 7, 4, 6], ![3, 1, 0, 2, 7, 5, 4, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![2, 3, 0, 1, 6, 7, 4, 5], ![4, 6, 0, 2, 1, 3, 5, 7], ![4, 6, 0, 2, 3, 1, 7, 5], ![4, 6, 0, 2, 5, 7, 1, 3], ![4, 6, 0, 2, 7, 5, 3, 1]], ![![1, 3, 2, 0, 5, 7, 6, 4], ![3, 1, 2, 0, 7, 5, 6, 4], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 4, 2, 0, 1, 3, 5, 7], ![6, 4, 2, 0, 3, 1, 7, 5], ![6, 4, 2, 0, 5, 7, 1, 3], ![6, 4, 2, 0, 7, 5, 3, 1]], ![![1, 3, 5, 7, 0, 2, 4, 6], ![3, 1, 7, 5, 0, 2, 4, 6], ![5, 7, 1, 3, 0, 2, 4, 6], ![7, 5, 3, 1, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![4, 5, 6, 7, 0, 1, 2, 3], ![4, 6, 5, 7, 0, 2, 1, 3], ![4, 6, 7, 5, 0, 2, 3, 1]], ![![1, 3, 5, 7, 2, 0, 6, 4], ![3, 1, 7, 5, 2, 0, 6, 4], ![5, 7, 1, 3, 2, 0, 6, 4], ![7, 5, 3, 1, 2, 0, 6, 4], ![5, 4, 7, 6, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 4, 5, 7, 2, 0, 1, 3], ![6, 4, 7, 5, 2, 0, 3, 1]], ![![1, 3, 5, 7, 4, 6, 0, 2], ![3, 1, 7, 5, 4, 6, 0, 2], ![5, 7, 1, 3, 4, 6, 0, 2], ![7, 5, 3, 1, 4, 6, 0, 2], ![5, 7, 4, 6, 1, 3, 0, 2], ![7, 5, 4, 6, 3, 1, 0, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1]], ![![1, 3, 5, 7, 6, 4, 2, 0], ![3, 1, 7, 5, 6, 4, 2, 0], ![5, 7, 1, 3, 6, 4, 2, 0], ![7, 5, 3, 1, 6, 4, 2, 0], ![5, 7, 6, 4, 1, 3, 2, 0], ![7, 5, 6, 4, 3, 1, 2, 0], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7]]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_order_left_inverse (p q t : Fin 8) :
    pairOrderInv p q (pairOrder p q t) = t := by
  revert p q t
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_order_right_inverse (p q t : Fin 8) :
    pairOrder p q (pairOrderInv p q t) = t := by
  revert p q t
  decide +kernel

def pairEquiv (p q : Fin 8) : Fin 8 ≃ Fin 8 where
  toFun := pairOrder p q
  invFun := pairOrderInv p q
  left_inv := pair_order_left_inverse p q
  right_inv := pair_order_right_inverse p q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_order_endpoints (p q : Fin 8) (hpq : p ≠ q) :
    pairOrder p q 0 = p ∧ pairOrder p q 1 = q := by
  revert p q
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The surviving pairs are exactly translates by h = p xor q. -/
theorem pair_order_translation (p q : Fin 8) (hpq : p ≠ q) (i : Fin 4) :
    pairOrder p q (Fin.ofNat 8 (2 * i.val + 1)) =
      Fin.xor (pairOrder p q (Fin.ofNat 8 (2 * i.val))) (Fin.xor p q) := by
  revert p q i
  decide +kernel

/-- Recover the affine parameters from the canonical information set. -/
def recoverParameters (x : Word) : Parameters :=
  ![x 0, Bool.xor (x 0) (x 4), Bool.xor (x 0) (x 2), Bool.xor (x 0) (x 1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem affine_under_pair_order (p q : Fin 8) (a : Parameters) :
    affineWord (recoverParameters (fun t => affineWord a (pairOrder p q t))) =
      fun t => affineWord a (pairOrder p q t) := by
  revert p q a
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem affine_under_pair_order_inv (p q : Fin 8) (a : Parameters) :
    affineWord (recoverParameters (fun t => affineWord a (pairOrderInv p q t))) =
      fun t => affineWord a (pairOrderInv p q t) := by
  revert p q a
  decide +kernel

theorem codeword_pair_order_iff (p q : Fin 8) (x : Word) :
    IsCodeword (fun t => x (pairOrder p q t)) ↔ IsCodeword x := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨recoverParameters (fun t => affineWord a (pairOrderInv p q t)), ?_⟩
    rw [affine_under_pair_order_inv]
    funext t
    simpa only [pair_order_right_inverse] using congrFun ha (pairOrderInv p q t)
  · rintro ⟨a, rfl⟩
    exact ⟨_, affine_under_pair_order p q a⟩

theorem core_reindex_pair {K : Type*} [Zero K] [One K] (p q : Fin 8) :
    Tensor.reindex (pairEquiv p q) (core (K := K)) = core := by
  funext x
  change (if IsCodeword (fun t => x (pairOrder p q t)) then (1 : K) else 0) = _
  simp only [codeword_pair_order_iff, core]

theorem core_reindex_pair_symm {K : Type*} [Zero K] [One K] (p q : Fin 8) :
    Tensor.reindex (pairEquiv p q).symm (core (K := K)) = core := by
  have h := congrArg (Tensor.reindex (pairEquiv p q).symm)
    (core_reindex_pair (K := K) p q)
  simpa only [Tensor.reindex_symm] using h.symm

/-- Close the original ordered ports p,q, displaying surviving ports in the
explicit affine order. For p ≠ q the endpoints theorem identifies those ports;
the translation theorem identifies every remaining matched pair. -/
def contractAtPair {K : Type*} [Semiring K] (E : Kernel K)
    (p q : Fin 8) (f : Signature K 8) : Signature K 6 :=
  Signature.contract E (Tensor.reindex (pairEquiv p q).symm f)

/-- Every ordered pair has the exact Bell occurrence identity, with its
remaining-port order exhibited by `pairEquiv` and no unknown scalar. -/
theorem contract_core_bell_at_pair {K : Type*} [Ring K]
    (p q : Fin 8) (d l : Bool) :
    contractAtPair (Bell.ordered (K := K) d l) p q core = bellTriple d l := by
  rw [contractAtPair, core_reindex_pair_symm, contract_core_bell]


/-- The distinct-pair statement bundles the port identification with the exact
six-port tensor identity, so no degenerate ordered-pair convention is hidden. -/
theorem contract_core_bell_at_distinct_pair {K : Type*} [Ring K]
    (p q : Fin 8) (hpq : p ≠ q) (d l : Bool) :
    pairOrder p q 0 = p ∧ pairOrder p q 1 = q ∧
      contractAtPair (Bell.ordered (K := K) d l) p q core = bellTriple d l :=
  ⟨(pair_order_endpoints p q hpq).1, (pair_order_endpoints p q hpq).2,
    contract_core_bell_at_pair p q d l⟩

end Paper2.ReedMuller
