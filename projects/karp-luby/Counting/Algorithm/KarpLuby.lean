import Counting.Algorithm.KarpLuby.Imported.RobustEstimate
import Counting.Algorithm.KarpLuby.CoverPAC
import Counting.Algorithm.KarpLuby.DNFCover
import Counting.Algorithm.KarpLuby.ProgramCorrectness
import Counting.Algorithm.KarpLuby.Guarantee
import Counting.Algorithm.KarpLuby.ProgramEncoding
import Counting.Algorithm.KarpLuby.MedianCost
import Counting.Algorithm.KarpLuby.EncodedBounds
import Counting.Algorithm.KarpLuby.Encoding
import Counting.Algorithm.KarpLuby.Examples

/-!
# Karp–Luby bounded-fair-bit counting

The standalone public entry point deliberately distinguishes the finite/PAC
proofs from executable program refinement, representation, operation-count
bounds, and the still separate finite-alphabet machine cost obligation.
-/
