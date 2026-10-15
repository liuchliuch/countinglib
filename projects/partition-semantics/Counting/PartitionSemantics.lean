import Counting.Model.Basic
import Counting.Model.FiniteSums
import Counting.Model.Relabel
import Counting.Gadget.Composition
import Counting.Model.Graph
import Counting.Model.Holant
import Counting.Bridge.ComplexCSP
import Counting.Bridge.PlanarHom
import Counting.Bridge.Holant

/-!
# Stable partition semantics and original-source bridges

This standalone S1 entry point avoids importing `Counting.lean`, allowing a
combined package to import the complete stable semantic API without relying on
which pilot package supplies the root aggregator. Examples and audit commands
remain separate.
-/
