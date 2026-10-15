import Paper2.Certificates.Q6Dense
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring

/-!
The nine concrete two-copy cards used for dense orbits 20--23, calculated from
the exact Appendix-A subset-sum definition. The raw term tables are untrusted
witness data: their equality with the finite construction, absence of duplicate
terms, and all displayed polynomial expansions are proved inside Lean.
-/
namespace Paper2.Certificates.Q6

abbrev Port := Fin 6
abbrev PortSet := Finset Port

/-- W₄ = (0011,0101,0110,1001,1010,1100), as in Appendix A. -/
def eoWords : Fin 6 → Fin 4 → Bool :=
  ![![false,false,true,true], ![false,true,false,true],
    ![false,true,true,false], ![true,false,false,true],
    ![true,false,true,false], ![true,true,false,false]]

structure CardSpec where
  left0 : Port
  left1 : Port
  right0 : Port
  right1 : Port
  wiring : Port → Port

def denseSpecs : Fin 9 → CardSpec :=
  ![⟨0, 3, 0, 3, ![0, 1, 2, 3, 4, 5]⟩, ⟨0, 1, 0, 1, ![0, 1, 3, 4, 5, 2]⟩, ⟨0, 4, 0, 4, ![0, 2, 3, 5, 4, 1]⟩, ⟨0, 1, 0, 1, ![0, 1, 2, 3, 5, 4]⟩, ⟨0, 1, 0, 1, ![0, 1, 4, 5, 3, 2]⟩, ⟨0, 3, 0, 3, ![0, 1, 2, 3, 4, 5]⟩, ⟨0, 1, 0, 1, ![0, 1, 3, 4, 5, 2]⟩, ⟨0, 1, 1, 4, ![1, 4, 2, 3, 0, 5]⟩, ⟨0, 3, 0, 3, ![0, 5, 1, 3, 2, 4]⟩]

def selected (p q : Port) (a b : Bool) : PortSet :=
  (if a then {p} else ∅) ∪ (if b then {q} else ∅)

def internalLeft (s : CardSpec) : PortSet := Finset.univ \ {s.left0,s.left1}
def internalRight (s : CardSpec) : PortSet := Finset.univ \ {s.right0,s.right1}

def internalChoices (s : CardSpec) (e : Fin 6) : Finset PortSet :=
  (internalLeft s).powerset.filter (fun T =>
    T.card = 3 - ((eoWords e 0).toNat + (eoWords e 1).toNat))

def sourceSets (s : CardSpec) (e : Fin 6) (T : PortSet) : PortSet × PortSet :=
  (selected s.left0 s.left1 (eoWords e 0) (eoWords e 1) ∪ T,
    selected s.right0 s.right1 (eoWords e 2) (eoWords e 3) ∪
      (internalRight s \ T.image s.wiring))

def mask (S : PortSet) : ℕ := ∑ v ∈ S, 2^v.val

def sourceMasks (s : CardSpec) (e : Fin 6) (T : PortSet) : ℕ × ℕ :=
  (mask (sourceSets s e T).1, mask (sourceSets s e T).2)

/-- Increasing lexicographic order of triples, as in the Python orbit rows. -/
def tripleMasks : Fin 20 → ℕ := ![7, 11, 19, 35, 13, 21, 37, 25, 41, 49, 14, 22, 38, 26, 42, 50, 28, 44, 52, 56]

/-- Extend the twenty triple coefficients by zero off the triple layer. -/
def coefficient {K : Type*} [Zero K] (q : Fin 20 → K) (m : ℕ) : K :=
  match m with
  | 7 => q 0
  | 11 => q 1
  | 19 => q 2
  | 35 => q 3
  | 13 => q 4
  | 21 => q 5
  | 37 => q 6
  | 25 => q 7
  | 41 => q 8
  | 49 => q 9
  | 14 => q 10
  | 22 => q 11
  | 38 => q 12
  | 26 => q 13
  | 42 => q 14
  | 50 => q 15
  | 28 => q 16
  | 44 => q 17
  | 52 => q 18
  | 56 => q 19
  | _ => 0

/-- Exactly the formula C_{A,B,π}(x,y) of Appendix A. -/
def twoCopyArray {K : Type*} [CommRing K] (q : Fin 20 → K)
    (t : K) (s : CardSpec) : Fin 6 → K := fun e =>
  (if e = 0 ∨ e = 5 then t else 0) +
    ∑ T ∈ internalChoices s e,
      coefficient q (sourceMasks s e T).1 * coefficient q (sourceMasks s e T).2

/-- The explicit term-pair tables, with port k represented by bit k. -/
def densePairTable : Fin 9 → Fin 6 → Finset (ℕ × ℕ) :=
  ![![{(22, 41), (38, 25), (50, 13), (52, 11)}, {(14, 56), (26, 44), (42, 28), (28, 42), (44, 26), (56, 14)}, {(14, 49), (26, 37), (42, 21), (28, 35), (44, 19), (56, 7)}, {(7, 56), (19, 44), (35, 28), (21, 42), (37, 26), (49, 14)}, {(7, 49), (19, 37), (35, 21), (21, 35), (37, 19), (49, 7)}, {(11, 52), (13, 50), (25, 38), (41, 22)}], ![{(28, 7), (44, 35), (52, 19), (56, 11)}, {(14, 38), (22, 22), (38, 50), (26, 14), (42, 42), (50, 26)}, {(14, 37), (22, 21), (38, 49), (26, 13), (42, 41), (50, 25)}, {(13, 38), (21, 22), (37, 50), (25, 14), (41, 42), (49, 26)}, {(13, 37), (21, 21), (37, 49), (25, 13), (41, 41), (49, 25)}, {(7, 52), (11, 44), (19, 28), (35, 56)}], ![{(14, 19), (38, 49), (42, 25), (44, 21)}, {(22, 50), (26, 26), (50, 56), (28, 22), (52, 52), (56, 28)}, {(22, 35), (26, 11), (50, 41), (28, 7), (52, 37), (56, 13)}, {(7, 50), (11, 26), (35, 56), (13, 22), (37, 52), (41, 28)}, {(7, 35), (11, 11), (35, 41), (13, 7), (37, 37), (41, 13)}, {(19, 42), (21, 38), (25, 14), (49, 44)}], ![{(28, 19), (44, 35), (52, 11), (56, 7)}, {(14, 50), (22, 26), (38, 42), (26, 22), (42, 38), (50, 14)}, {(14, 49), (22, 25), (38, 41), (26, 21), (42, 37), (50, 13)}, {(13, 50), (21, 26), (37, 42), (25, 22), (41, 38), (49, 14)}, {(13, 49), (21, 25), (37, 41), (25, 21), (41, 37), (49, 13)}, {(7, 56), (11, 52), (19, 28), (35, 44)}], ![{(28, 7), (44, 11), (52, 35), (56, 19)}, {(14, 14), (22, 38), (38, 42), (26, 22), (42, 26), (50, 50)}, {(14, 13), (22, 37), (38, 41), (26, 21), (42, 25), (50, 49)}, {(13, 14), (21, 38), (37, 42), (25, 22), (41, 26), (49, 50)}, {(13, 13), (21, 37), (37, 41), (25, 21), (41, 25), (49, 49)}, {(7, 44), (11, 28), (19, 52), (35, 56)}], ![{(22, 41), (38, 25), (50, 13), (52, 11)}, {(14, 56), (26, 44), (42, 28), (28, 42), (44, 26), (56, 14)}, {(14, 49), (26, 37), (42, 21), (28, 35), (44, 19), (56, 7)}, {(7, 56), (19, 44), (35, 28), (21, 42), (37, 26), (49, 14)}, {(7, 49), (19, 37), (35, 21), (21, 35), (37, 19), (49, 7)}, {(11, 52), (13, 50), (25, 38), (41, 22)}], ![{(28, 7), (44, 35), (52, 19), (56, 11)}, {(14, 38), (22, 22), (38, 50), (26, 14), (42, 42), (50, 26)}, {(14, 37), (22, 21), (38, 49), (26, 13), (42, 41), (50, 25)}, {(13, 38), (21, 22), (37, 50), (25, 14), (41, 42), (49, 26)}, {(13, 37), (21, 21), (37, 49), (25, 13), (41, 41), (49, 25)}, {(7, 52), (11, 44), (19, 28), (35, 56)}], ![{(28, 50), (44, 19), (52, 26), (56, 22)}, {(14, 49), (22, 56), (38, 25), (26, 52), (42, 21), (50, 28)}, {(14, 35), (22, 42), (38, 11), (26, 38), (42, 7), (50, 14)}, {(13, 49), (21, 56), (37, 25), (25, 52), (41, 21), (49, 28)}, {(13, 35), (21, 42), (37, 11), (25, 38), (41, 7), (49, 14)}, {(7, 41), (11, 37), (19, 44), (35, 13)}], ![{(22, 25), (38, 13), (50, 11), (52, 41)}, {(14, 28), (26, 26), (42, 14), (28, 56), (44, 44), (56, 42)}, {(14, 21), (26, 19), (42, 7), (28, 49), (44, 37), (56, 35)}, {(7, 28), (19, 26), (35, 14), (21, 56), (37, 44), (49, 42)}, {(7, 21), (19, 19), (35, 7), (21, 49), (37, 37), (49, 35)}, {(11, 22), (13, 52), (25, 50), (41, 38)}]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dense_specs_valid (i : Fin 9) :
    (denseSpecs i).left0 < (denseSpecs i).left1 ∧
    (denseSpecs i).right0 < (denseSpecs i).right1 ∧
    Function.Bijective (denseSpecs i).wiring ∧
    (internalLeft (denseSpecs i)).image (denseSpecs i).wiring =
      internalRight (denseSpecs i) := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dense_source_triples (i : Fin 9) (e : Fin 6) (T : PortSet)
    (hT : T ∈ internalChoices (denseSpecs i) e) :
    (sourceSets (denseSpecs i) e T).1.card = 3 ∧
      (sourceSets (denseSpecs i) e T).2.card = 3 := by
  revert i e T
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dense_pair_table_correct (i : Fin 9) (e : Fin 6) :
    (internalChoices (denseSpecs i) e).image (sourceMasks (denseSpecs i) e) =
      densePairTable i e := by
  revert i e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dense_source_injective (i : Fin 9) (e : Fin 6) :
    Set.InjOn (sourceMasks (denseSpecs i) e) (internalChoices (denseSpecs i) e) := by
  apply Finset.card_image_iff.mp
  revert i e
  decide +kernel

/-- The signed rows of dense families 20--23, with independent parameters. -/
def denseOrbit {K : Type*} [Ring K] (u : Fin 5 → K) : Fin 4 → Fin 20 → K :=
  ![![u 0, -u 0, -u 0, u 0, -u 0, u 0, -u 0, u 1, u 2, -u 0, u 0, u 3, u 4, u 0, -u 0, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, -u 0, u 1, -u 0, u 0, u 1, -u 1, u 1, -u 1, -u 0, u 0, -u 1, u 0, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, u 1, -u 1, -u 0, u 0, -u 1, u 2, -u 1, u 2, -u 0, u 0, u 2, -u 2, -u 0, u 0, u 0, -u 0], ![u 0, -u 0, -u 0, u 0, u 1, -u 1, -u 0, u 0, -u 1, u 2, u 3, u 1, -u 0, u 0, u 1, -u 1, -u 0, u 0, u 0, -u 0]]

def cardOrbit : Fin 9 → Fin 4 := ![0,1,1,2,2,2,3,3,3]

/-- The expanded cards. Every expansion is verified by the theorem below. -/
def denseFormula {K : Type*} [CommRing K] (u : Fin 5 → K) (t : K) :
    Fin 9 → Fin 6 → K :=
  let a := u 0
  let b := u 1
  let c := u 2
  let d := u 3
  let e := u 4
  ![![-2*a^2+b*e+c*d+t, 2*a^2, -6*a^2, -6*a^2, 2*a^2, -2*a^2+b*e+c*d+t],
    ![t, 2*b^2, -2*b^2, -2*b^2, 2*b^2, t],
    ![t, 2*a^2, -2*a^2, -2*a^2, 2*a^2, t],
    ![t, 2*b*c, -2*b*c, -2*b*c, 2*b*c, t],
    ![t, b^2+c^2, -b^2-c^2, -b^2-c^2, b^2+c^2, t],
    ![-2*a^2-2*b*c+t, 2*a^2+2*a*b-2*a*c, -4*a^2-2*b*c,
      -4*a^2-2*b*c, 2*a^2-2*a*b+2*a*c, -2*a^2-2*b*c+t],
    ![t, 2*b^2, -a*c-a*d-2*b^2, a*c+a*d-2*b^2, 2*b^2, t],
    ![t, -b^2+c*d, a*b+a*d+b^2-b*d, a*b-a*c+b^2+b*c, -b^2+c*d, t],
    ![t, 3*a^2-a*b-a*d+b*d, -3*a^2+a*b-a*c-b*d,
      -3*a^2+a*b+a*d+b*c, 3*a^2-a*b+a*c-b*c, t]]

theorem twoCopyArray_eq_pair_table {K : Type*} [CommRing K]
    (q : Fin 20 → K) (t : K) (i : Fin 9) (e : Fin 6) :
    twoCopyArray q t (denseSpecs i) e =
      (if e = 0 ∨ e = 5 then t else 0) +
        ∑ ab ∈ densePairTable i e, coefficient q ab.1 * coefficient q ab.2 := by
  rw [twoCopyArray, ← dense_pair_table_correct]
  congr 1
  exact (Finset.sum_image (f := fun ab : ℕ × ℕ =>
    coefficient q ab.1 * coefficient q ab.2) (dense_source_injective i e)).symm

set_option maxHeartbeats 2000000 in
private theorem dense_card_0 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 0)) t (denseSpecs 0) = denseFormula u t 0 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22, 41), (38, 25), (50, 13), (52, 11)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 3)) * ((u 2)) + (((u 4)) * ((u 1)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = -2*(u 0)^2+(u 1)*(u 4)+(u 2)*(u 3)+t
    ring
  · change 0 + (∑ ab ∈ ({(14, 56), (26, 44), (42, 28), (28, 42), (44, 26), (56, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14, 49), (26, 37), (42, 21), (28, 35), (44, 19), (56, 7)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7, 56), (19, 44), (35, 28), (21, 42), (37, 26), (49, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7, 49), (19, 37), (35, 21), (21, 35), (37, 19), (49, 7)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11, 52), (13, 50), (25, 38), (41, 22)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 0)) ab.1 * coefficient (denseOrbit u (cardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 1)) * ((u 4)) + ((u 2)) * ((u 3))))) = -2*(u 0)^2+(u 1)*(u 4)+(u 2)*(u 3)+t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_1 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 1)) t (denseSpecs 1) = denseFormula u t 1 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28, 7), (44, 35), (52, 19), (56, 11)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 38), (22, 22), (38, 50), (26, 14), (42, 42), (50, 26)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((-(u 1)) * (-(u 1)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 1)) + ((-(u 1)) * (-(u 1)) + ((u 0)) * ((u 0))))))) = 2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(14, 37), (22, 21), (38, 49), (26, 13), (42, 41), (50, 25)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((-(u 1)) * ((u 1)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 0)) + ((-(u 1)) * ((u 1)) + ((u 0)) * ((u 0))))))) = -2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 38), (21, 22), (37, 50), (25, 14), (41, 42), (49, 26)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 1)) * (-(u 1)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 1)) + (((u 1)) * (-(u 1)) + (-(u 1)) * ((u 0))))))) = -2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 37), (21, 21), (37, 49), (25, 13), (41, 41), (49, 25)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 1)) * ((u 1)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 0)) + (((u 1)) * ((u 1)) + (-(u 1)) * ((u 0))))))) = 2*(u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7, 52), (11, 44), (19, 28), (35, 56)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 1)) ab.1 * coefficient (denseOrbit u (cardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_2 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 2)) t (denseSpecs 2) = denseFormula u t 2 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(14, 19), (38, 49), (42, 25), (44, 21)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 1)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + ((-(u 1)) * ((u 0)) + ((u 0)) * ((u 1))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(22, 50), (26, 26), (50, 56), (28, 22), (52, 52), (56, 28)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(22, 35), (26, 11), (50, 41), (28, 7), (52, 37), (56, 13)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 1)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7, 50), (11, 26), (35, 56), (13, 22), (37, 52), (41, 28)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + ((-(u 0)) * ((u 0)) + ((u 1)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7, 35), (11, 11), (35, 41), (13, 7), (37, 37), (41, 13)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 1)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 1)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(19, 42), (21, 38), (25, 14), (49, 44)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 2)) ab.1 * coefficient (denseOrbit u (cardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 1)) + (((u 1)) * (-(u 0)) + (((u 0)) * ((u 1)) + (-(u 1)) * ((u 0))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_3 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 3)) t (denseSpecs 3) = denseFormula u t 3 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28, 19), (44, 35), (52, 11), (56, 7)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 50), (22, 26), (38, 42), (26, 22), (42, 38), (50, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * (-(u 2)) + (((u 2)) * ((u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 2)) + (((u 2)) * (-(u 0)) + (-(u 2)) * (-(u 1))))))) = 2*(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(14, 49), (22, 25), (38, 41), (26, 21), (42, 37), (50, 13)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * ((u 2)) + (((u 2)) * ((u 0)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 1)) + (((u 2)) * (-(u 0)) + (-(u 2)) * ((u 1))))))) = -2*(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13, 50), (21, 26), (37, 42), (25, 22), (41, 38), (49, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 2)) + ((-(u 1)) * ((u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 2)) + ((-(u 1)) * (-(u 0)) + ((u 2)) * (-(u 1))))))) = -2*(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13, 49), (21, 25), (37, 41), (25, 21), (41, 37), (49, 13)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * ((u 2)) + ((-(u 1)) * ((u 0)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 1)) + ((-(u 1)) * (-(u 0)) + ((u 2)) * ((u 1))))))) = 2*(u 1)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(7, 56), (11, 52), (19, 28), (35, 44)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 3)) ab.1 * coefficient (denseOrbit u (cardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_4 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 4)) t (denseSpecs 4) = denseFormula u t 4 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28, 7), (44, 11), (52, 35), (56, 19)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 14), (22, 38), (38, 42), (26, 22), (42, 26), (50, 50)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * (-(u 1)) + (((u 2)) * (-(u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 2)) + (((u 2)) * ((u 0)) + (-(u 2)) * (-(u 2))))))) = (u 1)^2+(u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(14, 13), (22, 37), (38, 41), (26, 21), (42, 25), (50, 49)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * ((u 1)) + (((u 2)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 1)) + (((u 2)) * ((u 0)) + (-(u 2)) * ((u 2))))))) = -(u 1)^2-(u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 14), (21, 38), (37, 42), (25, 22), (41, 26), (49, 50)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 1)) + ((-(u 1)) * (-(u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 2)) + ((-(u 1)) * ((u 0)) + ((u 2)) * (-(u 2))))))) = -(u 1)^2-(u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 13), (21, 37), (37, 41), (25, 21), (41, 25), (49, 49)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * ((u 1)) + ((-(u 1)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 1)) + ((-(u 1)) * ((u 0)) + ((u 2)) * ((u 2))))))) = (u 1)^2+(u 2)^2
    ring
  · change t + (∑ ab ∈ ({(7, 44), (11, 28), (19, 52), (35, 56)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 4)) ab.1 * coefficient (denseOrbit u (cardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_5 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 5)) t (denseSpecs 5) = denseFormula u t 5 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22, 41), (38, 25), (50, 13), (52, 11)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 2)) * (-(u 1)) + ((-(u 0)) * ((u 0)) + ((-(u 2)) * ((u 1)) + ((u 0)) * (-(u 0))))) = -2*(u 0)^2-2*(u 1)*(u 2)+t
    ring
  · change 0 + (∑ ab ∈ ({(14, 56), (26, 44), (42, 28), (28, 42), (44, 26), (56, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 2)) * (-(u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 1))))))) = 2*(u 0)^2+2*(u 0)*(u 1)-2*(u 0)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(14, 49), (26, 37), (42, 21), (28, 35), (44, 19), (56, 7)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 1)) * ((u 2)) + (((u 0)) * (-(u 0)) + (((u 2)) * (-(u 1)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -4*(u 0)^2-2*(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(7, 56), (19, 44), (35, 28), (21, 42), (37, 26), (49, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 1)) * ((u 2)) + ((-(u 0)) * ((u 0)) + ((u 2)) * (-(u 1))))))) = -4*(u 0)^2-2*(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(7, 49), (19, 37), (35, 21), (21, 35), (37, 19), (49, 7)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 2)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 1)) + ((-(u 1)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 2)) * ((u 0))))))) = 2*(u 0)^2-2*(u 0)*(u 1)+2*(u 0)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(11, 52), (13, 50), (25, 38), (41, 22)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 5)) ab.1 * coefficient (denseOrbit u (cardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 1)) * (-(u 2)) + (((u 0)) * (-(u 0)) + (-(u 1)) * ((u 2))))) = -2*(u 0)^2-2*(u 1)*(u 2)+t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_6 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 6)) t (denseSpecs 6) = denseFormula u t 6 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28, 7), (44, 35), (52, 19), (56, 11)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 38), (22, 22), (38, 50), (26, 14), (42, 42), (50, 26)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (-(u 0)) + (((u 1)) * ((u 1)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * ((u 3)) + (((u 1)) * ((u 1)) + (-(u 1)) * ((u 0))))))) = 2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(14, 37), (22, 21), (38, 49), (26, 13), (42, 41), (50, 25)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (-(u 0)) + (((u 1)) * (-(u 1)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 1)) + (((u 1)) * (-(u 1)) + (-(u 1)) * ((u 0))))))) = -(u 0)*(u 2)-(u 0)*(u 3)-2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 38), (21, 22), (37, 50), (25, 14), (41, 42), (49, 26)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((-(u 1)) * ((u 1)) + ((-(u 0)) * (-(u 1)) + (((u 0)) * ((u 3)) + ((-(u 1)) * ((u 1)) + ((u 2)) * ((u 0))))))) = (u 0)*(u 2)+(u 0)*(u 3)-2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13, 37), (21, 21), (37, 49), (25, 13), (41, 41), (49, 25)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((-(u 1)) * (-(u 1)) + ((-(u 0)) * ((u 2)) + (((u 0)) * ((u 1)) + ((-(u 1)) * (-(u 1)) + ((u 2)) * ((u 0))))))) = 2*(u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7, 52), (11, 44), (19, 28), (35, 56)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 6)) ab.1 * coefficient (denseOrbit u (cardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_7 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 7)) t (denseSpecs 7) = denseFormula u t 7 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28, 50), (44, 19), (52, 26), (56, 22)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 1)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * ((u 1))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 49), (22, 56), (38, 25), (26, 52), (42, 21), (50, 28)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 2)) + (((u 1)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 1)) * (-(u 1)) + (-(u 1)) * (-(u 0))))))) = -(u 1)^2+(u 2)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(14, 35), (22, 42), (38, 11), (26, 38), (42, 7), (50, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 0)) + (((u 1)) * ((u 1)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (((u 1)) * ((u 0)) + (-(u 1)) * ((u 3))))))) = (u 0)*(u 1)+(u 0)*(u 3)+(u 1)^2-(u 1)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(13, 49), (21, 56), (37, 25), (25, 52), (41, 21), (49, 28)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * ((u 2)) + ((-(u 1)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 1)) * (-(u 1)) + ((u 2)) * (-(u 0))))))) = (u 0)*(u 1)-(u 0)*(u 2)+(u 1)^2+(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13, 35), (21, 42), (37, 11), (25, 38), (41, 7), (49, 14)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * ((u 0)) + ((-(u 1)) * ((u 1)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 1)) * ((u 0)) + ((u 2)) * ((u 3))))))) = -(u 1)^2+(u 2)*(u 3)
    ring
  · change t + (∑ ab ∈ ({(7, 41), (11, 37), (19, 44), (35, 13)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 7)) ab.1 * coefficient (denseOrbit u (cardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 1)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * ((u 1))))) = t
    ring

set_option maxHeartbeats 2000000 in
private theorem dense_card_8 {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) :
    twoCopyArray (denseOrbit u (cardOrbit 8)) t (denseSpecs 8) = denseFormula u t 8 := by
  funext e
  rw [twoCopyArray_eq_pair_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22, 25), (38, 13), (50, 11), (52, 41)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 1)) * ((u 0)) + ((-(u 0)) * ((u 1)) + ((-(u 1)) * (-(u 0)) + ((u 0)) * (-(u 1))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14, 28), (26, 26), (42, 14), (28, 56), (44, 44), (56, 42)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 1)) * ((u 3)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * ((u 1))))))) = 3*(u 0)^2-(u 0)*(u 1)-(u 0)*(u 3)+(u 1)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(14, 21), (26, 19), (42, 7), (28, 49), (44, 37), (56, 35)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (-(u 1)) + (((u 0)) * (-(u 0)) + (((u 1)) * ((u 0)) + ((-(u 0)) * ((u 2)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -3*(u 0)^2+(u 0)*(u 1)-(u 0)*(u 2)-(u 1)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(7, 28), (19, 26), (35, 14), (21, 56), (37, 44), (49, 42)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 3)) + ((-(u 1)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 2)) * ((u 1))))))) = -3*(u 0)^2+(u 0)*(u 1)+(u 0)*(u 3)+(u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(7, 21), (19, 19), (35, 7), (21, 49), (37, 37), (49, 35)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 1)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 1)) * ((u 2)) + ((-(u 0)) * (-(u 0)) + ((u 2)) * ((u 0))))))) = 3*(u 0)^2-(u 0)*(u 1)+(u 0)*(u 2)-(u 1)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(11, 22), (13, 52), (25, 50), (41, 38)} : Finset (ℕ × ℕ)),
      coefficient (denseOrbit u (cardOrbit 8)) ab.1 * coefficient (denseOrbit u (cardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 1)) + (((u 1)) * ((u 0)) + (((u 0)) * (-(u 1)) + (-(u 1)) * (-(u 0))))) = t
    ring

/-- All 54 polynomial entries of the nine actual subset-sum cards. -/
theorem twoCopyArray_dense {K : Type*} [CommRing K]
    (u : Fin 5 → K) (t : K) (i : Fin 9) :
    twoCopyArray (denseOrbit u (cardOrbit i)) t (denseSpecs i) = denseFormula u t i := by
  fin_cases i
  · exact dense_card_0 u t
  · exact dense_card_1 u t
  · exact dense_card_2 u t
  · exact dense_card_3 u t
  · exact dense_card_4 u t
  · exact dense_card_5 u t
  · exact dense_card_6 u t
  · exact dense_card_7 u t
  · exact dense_card_8 u t

end Paper2.Certificates.Q6
