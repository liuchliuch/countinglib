import Counting
import Counting.Bridge.PlanarHomSharpP
import Counting.Bridge.WitnessSharpP
import Counting.Bridge.CountingCookLevin
import Counting.Reduction.OneQuery
import Counting.Algorithms
import Counting.Reuse
import Counting.Algorithm.Affine.FixedLanguage
import Counting.Algorithm.Holographic.All
import Counting.Flagships.Holant
import Counting.Flagships.MatchgateWidth
import Counting.Flagships.ComplexCSP
import Counting.Flagships.PlanarHom

/-! Complete coordinated library entry point. Use Counting for the small core,
Counting.Algorithms for the mathematical algorithm entries. Fixed-language
machines and upstream holographic adapters are explicitly included here.
Use Counting.Flagships.Holant for the Holant classifier.
Counting.Flagships.ComplexCSP exposes the complete fixed-language classification
and effective recognition on exact finite algebraic input.
Counting.Flagships.PlanarHom exposes the original closed nonnegative algebraic
dichotomies on ordinary planar inputs.
-/
