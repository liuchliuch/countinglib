import Counting.FiniteSupport.Computer

/-!
# Finite-support compilation of actual TM2 programs

This public entry reuses the canonical PlanarHom compiler and its F1/S1/core
dependencies, without the accepting-path or classification closures. Declarations live in
`Counting.Computation.FiniteSupport`; the module path deliberately avoids the
module subtree owned by the foundations component. The F1 packaging and the
Pfaffian application are separate optional imports.
-/
