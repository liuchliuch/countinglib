import Counting.ComplexCSP

/-! Executable smoke checks for the exact finite frontend, independent of proof audits. -/
namespace Counting.ComplexCSP.Smoke
open _root_.ComplexCSP.AlgebraicEncoding _root_.ComplexCSP.ComplexRootCertificates

/-- The linear integer polynomial X - 1, isolated in a rational open rectangle. -/
def oneInput : AlgebraicInput := ⟨[-1, 1], ⟨0, 2, -1, 1⟩⟩

theorem oneInput_represents : oneInput.Represents 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
    change (integerListPolynomial [-1, 1]).coeff 1 = (0 : Polynomial ℤ).coeff 1 at hc
    rw [integerListPolynomial_coeff] at hc
    norm_num at hc
  · norm_num [oneInput, evalIntegerList]
  · norm_num [oneInput, Rectangle.Contains]
  · intro w hw _
    norm_num [oneInput, evalIntegerList] at hw
    linear_combination hw

/-- Nonempty domain and one unary table, with all runtime data made explicit. -/
def singletonLanguage : Recognition.FiniteAlgebraicLanguage where
  domainSize := 1
  domain_pos := by decide
  signatureSize := 1
  tables := ⟨fun _ => 1, fun _ => by decide, fun _ _ => oneInput⟩

theorem singletonLanguage_valid : singletonLanguage.Valid :=
  fun _ _ => ⟨1, oneInput_represents⟩

#eval do
  unless Recognition.recognize singletonLanguage singletonLanguage_valid do
    throw (IO.userError "ordinary recognizer rejected the singleton unit language")
  unless Recognition.recognizeDegree singletonLanguage singletonLanguage_valid 1 (by decide) do
    throw (IO.userError "degree-one recognizer rejected the singleton unit language")
  let restored := (Encodable.decode (Encodable.encode singletonLanguage) :
    Option Recognition.FiniteAlgebraicLanguage)
  unless restored.map (fun (L : Recognition.FiniteAlgebraicLanguage) => (L.domainSize, L.signatureSize)) == some (1, 1) do
    throw (IO.userError "encoded frontend did not retain its domain and signature sizes")
  IO.println "C1_SMOKE_OK ordinary=true degree1=true roundtrip=true"

end Counting.ComplexCSP.Smoke
