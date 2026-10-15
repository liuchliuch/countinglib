import Paper2.DegreeCSP.QueryRecordIdentity

/-! The final literal incidence compiler emits a validated native-X Holant
query. Its finite machine, polynomial clock and output-length bound are all
inherited from the checked raw compiler; validity comes from the actual graph. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
open Paper2.Complexity.BinaryCompose Paper2.Complexity.FixedFieldMachines
noncomputable section

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3≤k) (jK : Fin s) (hK : a jK.val=k)

/-- No promised compiler is supplied: this is the concrete full incidence
program, with its exact graph validation already proved. -/
def queryComputes : Computes (Raw.validatedEncoding s a k)
    (RawClosedNetwork.validatedEncoding s 1 a)
    (fun r=>query G hk r jK hK) :=
  recode (promisedPaper2RawQueryComputes s a k (by omega) jK.val) id
    (fun _=>rfl) (fun _=>rfl)

/-- A bound on actual encoded query bytes follows from actual transitions. -/
def queryOutputBound : PolynomialOutputBound (Raw.validatedEncoding s a k)
    (RawClosedNetwork.validatedEncoding s 1 a) (fun r=>query G hk r jK hK) :=
  (queryComputes G hk jK hK).outputBound

/-- The varying graph query is polynomial time in the literal original input. -/
def queryPolyTime : PolyTime (Raw.validatedEncoding s a k)
    (RawClosedNetwork.validatedEncoding s 1 a) (fun r=>query G hk r jK hK) :=
  (queryComputes G hk jK hK).toPolyTime

end
end Paper2.DegreeCSP.QueryGraph
